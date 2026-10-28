import QEC.Count.ChunksK3
import QEC.KChecks.D2M8K2.A20

namespace QECKChecks.D2M8K2

open QEC QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem arows2498 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2498 = true := by
  rw [show D2M8K2.u2498 = KTree.node D2M8K2.u2494 (nat_lit 6574888) (nat_lit 3801061395) (nat_lit 0) D2M8K2.u2497 from rfl, allE_node, arows2494, irow2498, arows2497]
  all_goals rfl

theorem atot2498 : totK PD2M8K2 D2M8K2.u2498 = [63020407318, 1451199868836, 3509512938073, 1942494905493, 183350344884, 1206465782, 0, 0] := by
  rw [show D2M8K2.u2498 = KTree.node D2M8K2.u2494 (nat_lit 6574888) (nat_lit 3801061395) (nat_lit 0) D2M8K2.u2497 from rfl, totK_node, atot2494, atot2497]
  decide +kernel

theorem arows2505 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2505 = true := by
  rw [show D2M8K2.u2505 = KTree.node D2M8K2.u2501 (nat_lit 6587248) (nat_lit 3372580223) (nat_lit 0) D2M8K2.u2504 from rfl, allE_node, arows2501, irow2505, arows2504]
  all_goals rfl

theorem atot2505 : totK PD2M8K2 D2M8K2.u2505 = [0, 899023841939, 3084800249488, 2581978280876, 481508413691, 17590593026, 0, 0] := by
  rw [show D2M8K2.u2505 = KTree.node D2M8K2.u2501 (nat_lit 6587248) (nat_lit 3372580223) (nat_lit 0) D2M8K2.u2504 from rfl, totK_node, atot2501, atot2504]
  decide +kernel

theorem arows2513 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2513 = true := by
  rw [show D2M8K2.u2513 = KTree.node D2M8K2.u2509 (nat_lit 6596733) (nat_lit 1504947805) (nat_lit 0) D2M8K2.u2512 from rfl, allE_node, arows2509, irow2513, arows2512]
  all_goals rfl

theorem atot2513 : totK PD2M8K2 D2M8K2.u2513 = [754053148791, 2720688898747, 2820100816401, 926136183957, 69489080765, 0, 0, 0] := by
  rw [show D2M8K2.u2513 = KTree.node D2M8K2.u2509 (nat_lit 6596733) (nat_lit 1504947805) (nat_lit 0) D2M8K2.u2512 from rfl, totK_node, atot2509, atot2512]
  decide +kernel

theorem arows2520 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2520 = true := by
  rw [show D2M8K2.u2520 = KTree.node D2M8K2.u2516 (nat_lit 6606283) (nat_lit 1599363829) (nat_lit 0) D2M8K2.u2519 from rfl, allE_node, arows2516, irow2520, arows2519]
  all_goals rfl

theorem atot2520 : totK PD2M8K2 D2M8K2.u2520 = [851035406701, 2893662951365, 2777587568846, 693869961875, 25481086211, 0, 0, 0] := by
  rw [show D2M8K2.u2520 = KTree.node D2M8K2.u2516 (nat_lit 6606283) (nat_lit 1599363829) (nat_lit 0) D2M8K2.u2519 from rfl, totK_node, atot2516, atot2519]
  decide +kernel

theorem arows2529 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2529 = true := by
  rw [show D2M8K2.u2529 = KTree.node D2M8K2.u2525 (nat_lit 6613179) (nat_lit 3019366617) (nat_lit 0) D2M8K2.u2528 from rfl, allE_node, arows2525, irow2529, arows2528]
  all_goals rfl

theorem atot2529 : totK PD2M8K2 D2M8K2.u2529 = [416383101368, 2184780158076, 3225254157883, 1237397893281, 105978587167, 1239866073, 0, 0] := by
  rw [show D2M8K2.u2529 = KTree.node D2M8K2.u2525 (nat_lit 6613179) (nat_lit 3019366617) (nat_lit 0) D2M8K2.u2528 from rfl, totK_node, atot2525, atot2528]
  decide +kernel

theorem arows2536 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2536 = true := by
  rw [show D2M8K2.u2536 = KTree.node D2M8K2.u2532 (nat_lit 6626043) (nat_lit 3755701842) (nat_lit 0) D2M8K2.u2535 from rfl, allE_node, arows2532, irow2536, arows2535]
  all_goals rfl

theorem atot2536 : totK PD2M8K2 D2M8K2.u2536 = [0, 1031644768602, 3248857205614, 2491644605413, 406180724264, 13105450397, 0, 0] := by
  rw [show D2M8K2.u2536 = KTree.node D2M8K2.u2532 (nat_lit 6626043) (nat_lit 3755701842) (nat_lit 0) D2M8K2.u2535 from rfl, totK_node, atot2532, atot2535]
  decide +kernel

theorem arows2544 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2544 = true := by
  rw [show D2M8K2.u2544 = KTree.node D2M8K2.u2540 (nat_lit 6632782) (nat_lit 4022490277) (nat_lit 0) D2M8K2.u2543 from rfl, allE_node, arows2540, irow2544, arows2543]
  all_goals rfl

theorem atot2544 : totK PD2M8K2 D2M8K2.u2544 = [321152759376, 1797782002785, 3051206873902, 1729587755241, 220671557592, 4720618446, 0, 0] := by
  rw [show D2M8K2.u2544 = KTree.node D2M8K2.u2540 (nat_lit 6632782) (nat_lit 4022490277) (nat_lit 0) D2M8K2.u2543 from rfl, totK_node, atot2540, atot2543]
  decide +kernel

theorem arows2551 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2551 = true := by
  rw [show D2M8K2.u2551 = KTree.node D2M8K2.u2547 (nat_lit 6641904) (nat_lit 3186296335) (nat_lit 0) D2M8K2.u2550 from rfl, allE_node, arows2547, irow2551, arows2550]
  all_goals rfl

theorem atot2551 : totK PD2M8K2 D2M8K2.u2551 = [843361304411, 2847648108504, 2768109388266, 771484350476, 38766027842, 0, 0, 0] := by
  rw [show D2M8K2.u2551 = KTree.node D2M8K2.u2547 (nat_lit 6641904) (nat_lit 3186296335) (nat_lit 0) D2M8K2.u2550 from rfl, totK_node, atot2547, atot2550]
  decide +kernel

theorem arows2564 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2564 = true := by
  rw [show D2M8K2.u2564 = KTree.node D2M8K2.u2560 (nat_lit 6648585) (nat_lit 1897303611) (nat_lit 0) D2M8K2.u2563 from rfl, allE_node, arows2560, irow2564, arows2563]
  all_goals rfl

theorem atot2564 : totK PD2M8K2 D2M8K2.u2564 = [850908763291, 2910888075550, 2757964772755, 646131227351, 26232597979, 0, 0, 0] := by
  rw [show D2M8K2.u2564 = KTree.node D2M8K2.u2560 (nat_lit 6648585) (nat_lit 1897303611) (nat_lit 0) D2M8K2.u2563 from rfl, totK_node, atot2560, atot2563]
  decide +kernel

theorem arows2571 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2571 = true := by
  rw [show D2M8K2.u2571 = KTree.node D2M8K2.u2567 (nat_lit 6660136) (nat_lit 3733577409) (nat_lit 0) D2M8K2.u2570 from rfl, allE_node, arows2567, irow2571, arows2570]
  all_goals rfl

theorem atot2571 : totK PD2M8K2 D2M8K2.u2571 = [0, 1385886973738, 3623769399973, 1963190338222, 179344946160, 1138244013, 0, 0] := by
  rw [show D2M8K2.u2571 = KTree.node D2M8K2.u2567 (nat_lit 6660136) (nat_lit 3733577409) (nat_lit 0) D2M8K2.u2570 from rfl, totK_node, atot2567, atot2570]
  decide +kernel

theorem arows2579 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2579 = true := by
  rw [show D2M8K2.u2579 = KTree.node D2M8K2.u2575 (nat_lit 6670975) (nat_lit 2366502261) (nat_lit 0) D2M8K2.u2578 from rfl, allE_node, arows2575, irow2579, arows2578]
  all_goals rfl

theorem atot2579 : totK PD2M8K2 D2M8K2.u2579 = [324769904457, 1621626520432, 3051243431642, 1889921553469, 254788778560, 4977114383, 0, 0] := by
  rw [show D2M8K2.u2579 = KTree.node D2M8K2.u2575 (nat_lit 6670975) (nat_lit 2366502261) (nat_lit 0) D2M8K2.u2578 from rfl, totK_node, atot2575, atot2578]
  decide +kernel

theorem arows2586 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2586 = true := by
  rw [show D2M8K2.u2586 = KTree.node D2M8K2.u2582 (nat_lit 6682578) (nat_lit 3349558907) (nat_lit 0) D2M8K2.u2585 from rfl, allE_node, arows2582, irow2586, arows2585]
  all_goals rfl

theorem atot2586 : totK PD2M8K2 D2M8K2.u2586 = [792315288394, 2836883830022, 2851132533743, 772112856219, 38958597222, 0, 0, 0] := by
  rw [show D2M8K2.u2586 = KTree.node D2M8K2.u2582 (nat_lit 6682578) (nat_lit 3349558907) (nat_lit 0) D2M8K2.u2585 from rfl, totK_node, atot2582, atot2585]
  decide +kernel

theorem arows2595 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2595 = true := by
  rw [show D2M8K2.u2595 = KTree.node D2M8K2.u2591 (nat_lit 6688809) (nat_lit 1372840761) (nat_lit 0) D2M8K2.u2594 from rfl, allE_node, arows2591, irow2595, arows2594]
  all_goals rfl

theorem atot2595 : totK PD2M8K2 D2M8K2.u2595 = [816305679700, 2892884908701, 2847788026291, 660564088704, 25988484455, 0, 0, 0] := by
  rw [show D2M8K2.u2595 = KTree.node D2M8K2.u2591 (nat_lit 6688809) (nat_lit 1372840761) (nat_lit 0) D2M8K2.u2594 from rfl, totK_node, atot2591, atot2594]
  decide +kernel

theorem arows2602 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2602 = true := by
  rw [show D2M8K2.u2602 = KTree.node D2M8K2.u2598 (nat_lit 6698828) (nat_lit 2278870583) (nat_lit 0) D2M8K2.u2601 from rfl, allE_node, arows2598, irow2602, arows2601]
  all_goals rfl

theorem atot2602 : totK PD2M8K2 D2M8K2.u2602 = [93768764846, 1503005162790, 3482038309714, 1971551748405, 185036664522, 1310285577, 0, 0] := by
  rw [show D2M8K2.u2602 = KTree.node D2M8K2.u2598 (nat_lit 6698828) (nat_lit 2278870583) (nat_lit 0) D2M8K2.u2601 from rfl, totK_node, atot2598, atot2601]
  decide +kernel

theorem arows2610 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2610 = true := by
  rw [show D2M8K2.u2610 = KTree.node D2M8K2.u2606 (nat_lit 6708219) (nat_lit 2966267556) (nat_lit 0) D2M8K2.u2609 from rfl, allE_node, arows2606, irow2610, arows2609]
  all_goals rfl

theorem atot2610 : totK PD2M8K2 D2M8K2.u2610 = [0, 928068982120, 3142089944724, 2623851219747, 432746401838, 9811245038, 0, 0] := by
  rw [show D2M8K2.u2610 = KTree.node D2M8K2.u2606 (nat_lit 6708219) (nat_lit 2966267556) (nat_lit 0) D2M8K2.u2609 from rfl, totK_node, atot2606, atot2609]
  decide +kernel

theorem arows2617 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2617 = true := by
  rw [show D2M8K2.u2617 = KTree.node D2M8K2.u2613 (nat_lit 6718456) (nat_lit 3332910879) (nat_lit 0) D2M8K2.u2616 from rfl, allE_node, arows2613, irow2617, arows2616]
  all_goals rfl

theorem atot2617 : totK PD2M8K2 D2M8K2.u2617 = [0, 788691416634, 2770701195340, 2818764751856, 827421688447, 51146060711, 0, 0] := by
  rw [show D2M8K2.u2617 = KTree.node D2M8K2.u2613 (nat_lit 6718456) (nat_lit 3332910879) (nat_lit 0) D2M8K2.u2616 from rfl, totK_node, atot2613, atot2616]
  decide +kernel

theorem arows2627 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2627 = true := by
  rw [show D2M8K2.u2627 = KTree.node D2M8K2.u2623 (nat_lit 6769256) (nat_lit 3889969880) (nat_lit 0) D2M8K2.u2626 from rfl, allE_node, arows2623, irow2627, arows2626]
  all_goals rfl

theorem atot2627 : totK PD2M8K2 D2M8K2.u2627 = [0, 845726118887, 2944413512769, 2816926164515, 629757605370, 16920921409, 0, 0] := by
  rw [show D2M8K2.u2627 = KTree.node D2M8K2.u2623 (nat_lit 6769256) (nat_lit 3889969880) (nat_lit 0) D2M8K2.u2626 from rfl, totK_node, atot2623, atot2626]
  decide +kernel

theorem arows2634 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2634 = true := by
  rw [show D2M8K2.u2634 = KTree.node D2M8K2.u2630 (nat_lit 6776069) (nat_lit 2325556726) (nat_lit 0) D2M8K2.u2633 from rfl, allE_node, arows2630, irow2634, arows2633]
  all_goals rfl

theorem atot2634 : totK PD2M8K2 D2M8K2.u2634 = [0, 845744674632, 3002693371986, 2819539860490, 558550221763, 11323144342, 0, 0] := by
  rw [show D2M8K2.u2634 = KTree.node D2M8K2.u2630 (nat_lit 6776069) (nat_lit 2325556726) (nat_lit 0) D2M8K2.u2633 from rfl, totK_node, atot2630, atot2633]
  decide +kernel

theorem arows2642 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2642 = true := by
  rw [show D2M8K2.u2642 = KTree.node D2M8K2.u2638 (nat_lit 6786246) (nat_lit 3765499757) (nat_lit 0) D2M8K2.u2641 from rfl, allE_node, arows2638, irow2642, arows2641]
  all_goals rfl

theorem atot2642 : totK PD2M8K2 D2M8K2.u2642 = [0, 0, 1031014663952, 3063972072464, 2447986807302, 623741757556, 36921873854, 0] := by
  rw [show D2M8K2.u2642 = KTree.node D2M8K2.u2638 (nat_lit 6786246) (nat_lit 3765499757) (nat_lit 0) D2M8K2.u2641 from rfl, totK_node, atot2638, atot2641]
  decide +kernel

theorem arows2649 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2649 = true := by
  rw [show D2M8K2.u2649 = KTree.node D2M8K2.u2645 (nat_lit 6792623) (nat_lit 2777443937) (nat_lit 0) D2M8K2.u2648 from rfl, allE_node, arows2645, irow2649, arows2648]
  all_goals rfl

theorem atot2649 : totK PD2M8K2 D2M8K2.u2649 = [0, 0, 891308818963, 3083013854878, 2688754065634, 450162302811, 10194375460, 0] := by
  rw [show D2M8K2.u2649 = KTree.node D2M8K2.u2645 (nat_lit 6792623) (nat_lit 2777443937) (nat_lit 0) D2M8K2.u2648 from rfl, totK_node, atot2645, atot2648]
  decide +kernel

theorem arows2658 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2658 = true := by
  rw [show D2M8K2.u2658 = KTree.node D2M8K2.u2654 (nat_lit 6800092) (nat_lit 3847299078) (nat_lit 0) D2M8K2.u2657 from rfl, allE_node, arows2654, irow2658, arows2657]
  all_goals rfl

theorem atot2658 : totK PD2M8K2 D2M8K2.u2658 = [0, 322854152712, 1509533235731, 2706192635752, 2162060506910, 417975028110, 10531122277, 0] := by
  rw [show D2M8K2.u2658 = KTree.node D2M8K2.u2654 (nat_lit 6800092) (nat_lit 3847299078) (nat_lit 0) D2M8K2.u2657 from rfl, totK_node, atot2654, atot2657]
  decide +kernel

theorem arows2665 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2665 = true := by
  rw [show D2M8K2.u2665 = KTree.node D2M8K2.u2661 (nat_lit 6807731) (nat_lit 2743639631) (nat_lit 0) D2M8K2.u2664 from rfl, allE_node, arows2661, irow2665, arows2664]
  all_goals rfl

theorem atot2665 : totK PD2M8K2 D2M8K2.u2665 = [0, 871112273919, 2884109026796, 2738093361973, 755196592027, 38651645802, 0, 0] := by
  rw [show D2M8K2.u2665 = KTree.node D2M8K2.u2661 (nat_lit 6807731) (nat_lit 2743639631) (nat_lit 0) D2M8K2.u2664 from rfl, totK_node, atot2661, atot2664]
  decide +kernel

theorem arows2673 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2673 = true := by
  rw [show D2M8K2.u2673 = KTree.node D2M8K2.u2669 (nat_lit 6817342) (nat_lit 3125194145) (nat_lit 0) D2M8K2.u2672 from rfl, allE_node, arows2669, irow2673, arows2672]
  all_goals rfl

theorem atot2673 : totK PD2M8K2 D2M8K2.u2673 = [0, 826993596608, 2950323299507, 2814556475180, 580176096005, 18098320894, 0, 0] := by
  rw [show D2M8K2.u2673 = KTree.node D2M8K2.u2669 (nat_lit 6817342) (nat_lit 3125194145) (nat_lit 0) D2M8K2.u2672 from rfl, totK_node, atot2669, atot2672]
  decide +kernel

theorem arows2680 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2680 = true := by
  rw [show D2M8K2.u2680 = KTree.node D2M8K2.u2676 (nat_lit 6826601) (nat_lit 1101832514) (nat_lit 0) D2M8K2.u2679 from rfl, allE_node, arows2676, irow2680, arows2679]
  all_goals rfl

theorem atot2680 : totK PD2M8K2 D2M8K2.u2680 = [0, 0, 1430870282027, 3710217980852, 1881069190755, 127435383223, 0, 0] := by
  rw [show D2M8K2.u2680 = KTree.node D2M8K2.u2676 (nat_lit 6826601) (nat_lit 1101832514) (nat_lit 0) D2M8K2.u2679 from rfl, totK_node, atot2676, atot2679]
  decide +kernel

theorem arows2691 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2691 = true := by
  rw [show D2M8K2.u2691 = KTree.node D2M8K2.u2687 (nat_lit 6838848) (nat_lit 3678680325) (nat_lit 0) D2M8K2.u2690 from rfl, allE_node, arows2687, irow2691, arows2690]
  all_goals rfl

theorem atot2691 : totK PD2M8K2 D2M8K2.u2691 = [0, 271560262698, 1481679026594, 2942186415150, 2068701384187, 315869872562, 6546549506, 0] := by
  rw [show D2M8K2.u2691 = KTree.node D2M8K2.u2687 (nat_lit 6838848) (nat_lit 3678680325) (nat_lit 0) D2M8K2.u2690 from rfl, totK_node, atot2687, atot2690]
  decide +kernel

theorem arows2698 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2698 = true := by
  rw [show D2M8K2.u2698 = KTree.node D2M8K2.u2694 (nat_lit 6848425) (nat_lit 926406732) (nat_lit 0) D2M8K2.u2697 from rfl, allE_node, arows2694, irow2698, arows2697]
  all_goals rfl

theorem atot2698 : totK PD2M8K2 D2M8K2.u2698 = [0, 834384468755, 2868735033204, 2788434957230, 747755980145, 38796216711, 0, 0] := by
  rw [show D2M8K2.u2698 = KTree.node D2M8K2.u2694 (nat_lit 6848425) (nat_lit 926406732) (nat_lit 0) D2M8K2.u2697 from rfl, totK_node, atot2694, atot2697]
  decide +kernel

theorem arows2706 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2706 = true := by
  rw [show D2M8K2.u2706 = KTree.node D2M8K2.u2702 (nat_lit 6857672) (nat_lit 3909129062) (nat_lit 0) D2M8K2.u2705 from rfl, allE_node, arows2702, irow2706, arows2705]
  all_goals rfl

theorem atot2706 : totK PD2M8K2 D2M8K2.u2706 = [0, 823193579185, 2957141932022, 2814640744179, 586295185116, 18176614947, 0, 0] := by
  rw [show D2M8K2.u2706 = KTree.node D2M8K2.u2702 (nat_lit 6857672) (nat_lit 3909129062) (nat_lit 0) D2M8K2.u2705 from rfl, totK_node, atot2702, atot2705]
  decide +kernel

theorem arows2713 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2713 = true := by
  rw [show D2M8K2.u2713 = KTree.node D2M8K2.u2709 (nat_lit 6867425) (nat_lit 2108564817) (nat_lit 0) D2M8K2.u2712 from rfl, allE_node, arows2709, irow2713, arows2712]
  all_goals rfl

theorem atot2713 : totK PD2M8K2 D2M8K2.u2713 = [0, 92333346222, 1790547058223, 3666233654180, 1544424218488, 94340197834, 0, 0] := by
  rw [show D2M8K2.u2713 = KTree.node D2M8K2.u2709 (nat_lit 6867425) (nat_lit 2108564817) (nat_lit 0) D2M8K2.u2712 from rfl, totK_node, atot2709, atot2712]
  decide +kernel

theorem arows2722 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2722 = true := by
  rw [show D2M8K2.u2722 = KTree.node D2M8K2.u2718 (nat_lit 6878639) (nat_lit 1837772675) (nat_lit 0) D2M8K2.u2721 from rfl, allE_node, arows2718, irow2722, arows2721]
  all_goals rfl

theorem atot2722 : totK PD2M8K2 D2M8K2.u2722 = [0, 70882335681, 1006599545695, 3139253925896, 2516691912494, 358857903325, 6624648996, 0] := by
  rw [show D2M8K2.u2722 = KTree.node D2M8K2.u2718 (nat_lit 6878639) (nat_lit 1837772675) (nat_lit 0) D2M8K2.u2721 from rfl, totK_node, atot2718, atot2721]
  decide +kernel

theorem arows2729 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2729 = true := by
  rw [show D2M8K2.u2729 = KTree.node D2M8K2.u2725 (nat_lit 6888849) (nat_lit 1587072831) (nat_lit 0) D2M8K2.u2728 from rfl, allE_node, arows2725, irow2729, arows2728]
  all_goals rfl

theorem atot2729 : totK PD2M8K2 D2M8K2.u2729 = [0, 841221383729, 2876558111284, 2711359007033, 725894558319, 38700319430, 0, 0] := by
  rw [show D2M8K2.u2729 = KTree.node D2M8K2.u2725 (nat_lit 6888849) (nat_lit 1587072831) (nat_lit 0) D2M8K2.u2728 from rfl, totK_node, atot2725, atot2728]
  decide +kernel

theorem arows2737 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2737 = true := by
  rw [show D2M8K2.u2737 = KTree.node D2M8K2.u2733 (nat_lit 6895100) (nat_lit 3353581136) (nat_lit 0) D2M8K2.u2736 from rfl, allE_node, arows2733, irow2737, arows2736]
  all_goals rfl

theorem atot2737 : totK PD2M8K2 D2M8K2.u2737 = [0, 761825487401, 2831996293424, 2849488238185, 669917766185, 26300412495, 0, 0] := by
  rw [show D2M8K2.u2737 = KTree.node D2M8K2.u2733 (nat_lit 6895100) (nat_lit 3353581136) (nat_lit 0) D2M8K2.u2736 from rfl, totK_node, atot2733, atot2736]
  decide +kernel

theorem arows2744 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2744 = true := by
  rw [show D2M8K2.u2744 = KTree.node D2M8K2.u2740 (nat_lit 6905697) (nat_lit 1776540847) (nat_lit 0) D2M8K2.u2743 from rfl, allE_node, arows2740, irow2744, arows2743]
  all_goals rfl

theorem atot2744 : totK PD2M8K2 D2M8K2.u2744 = [0, 337432228733, 2176382515904, 3438341170572, 1160157488588, 55427351582, 0, 0] := by
  rw [show D2M8K2.u2744 = KTree.node D2M8K2.u2740 (nat_lit 6905697) (nat_lit 1776540847) (nat_lit 0) D2M8K2.u2743 from rfl, totK_node, atot2740, atot2743]
  decide +kernel

theorem arows2754 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2754 = true := by
  rw [show D2M8K2.u2754 = KTree.node D2M8K2.u2750 (nat_lit 6918963) (nat_lit 2797389594) (nat_lit 0) D2M8K2.u2753 from rfl, allE_node, arows2750, irow2754, arows2753]
  all_goals rfl

theorem atot2754 : totK PD2M8K2 D2M8K2.u2754 = [0, 71794763572, 1317329899216, 3449870104361, 2089613785532, 216641513297, 1429815836, 0] := by
  rw [show D2M8K2.u2754 = KTree.node D2M8K2.u2750 (nat_lit 6918963) (nat_lit 2797389594) (nat_lit 0) D2M8K2.u2753 from rfl, totK_node, atot2750, atot2753]
  decide +kernel

theorem arows2761 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2761 = true := by
  rw [show D2M8K2.u2761 = KTree.node D2M8K2.u2757 (nat_lit 6930384) (nat_lit 2483715505) (nat_lit 0) D2M8K2.u2760 from rfl, allE_node, arows2757, irow2761, arows2760]
  all_goals rfl

theorem atot2761 : totK PD2M8K2 D2M8K2.u2761 = [0, 849731074163, 2892323459631, 2749955328089, 736501914806, 38849856064, 0, 0] := by
  rw [show D2M8K2.u2761 = KTree.node D2M8K2.u2757 (nat_lit 6930384) (nat_lit 2483715505) (nat_lit 0) D2M8K2.u2760 from rfl, totK_node, atot2757, atot2760]
  decide +kernel

theorem arows2769 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2769 = true := by
  rw [show D2M8K2.u2769 = KTree.node D2M8K2.u2765 (nat_lit 6936652) (nat_lit 3704090693) (nat_lit 0) D2M8K2.u2768 from rfl, allE_node, arows2765, irow2769, arows2768]
  all_goals rfl

theorem atot2769 : totK PD2M8K2 D2M8K2.u2769 = [0, 816886245978, 2912778992118, 2839303609400, 632834611349, 18248331466, 0, 0] := by
  rw [show D2M8K2.u2769 = KTree.node D2M8K2.u2765 (nat_lit 6936652) (nat_lit 3704090693) (nat_lit 0) D2M8K2.u2768 from rfl, totK_node, atot2765, atot2768]
  decide +kernel

theorem arows2776 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2776 = true := by
  rw [show D2M8K2.u2776 = KTree.node D2M8K2.u2772 (nat_lit 6946618) (nat_lit 3892781461) (nat_lit 0) D2M8K2.u2775 from rfl, allE_node, arows2772, irow2776, arows2775]
  all_goals rfl

theorem atot2776 : totK PD2M8K2 D2M8K2.u2776 = [0, 285717665046, 2159159730947, 3473982912569, 1266080200315, 69310366320, 0, 0] := by
  rw [show D2M8K2.u2776 = KTree.node D2M8K2.u2772 (nat_lit 6946618) (nat_lit 3892781461) (nat_lit 0) D2M8K2.u2775 from rfl, totK_node, atot2772, atot2775]
  decide +kernel

theorem arows2785 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2785 = true := by
  rw [show D2M8K2.u2785 = KTree.node D2M8K2.u2781 (nat_lit 6957966) (nat_lit 3953930835) (nat_lit 0) D2M8K2.u2784 from rfl, allE_node, arows2781, irow2785, arows2784]
  all_goals rfl

theorem atot2785 : totK PD2M8K2 D2M8K2.u2785 = [0, 0, 992360763254, 3289069851330, 2561964465431, 304757305096, 2656098521, 0] := by
  rw [show D2M8K2.u2785 = KTree.node D2M8K2.u2781 (nat_lit 6957966) (nat_lit 3953930835) (nat_lit 0) D2M8K2.u2784 from rfl, totK_node, atot2781, atot2784]
  decide +kernel

theorem arows2792 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2792 = true := by
  rw [show D2M8K2.u2792 = KTree.node D2M8K2.u2788 (nat_lit 6968649) (nat_lit 1836561371) (nat_lit 0) D2M8K2.u2791 from rfl, allE_node, arows2788, irow2792, arows2791]
  all_goals rfl

theorem atot2792 : totK PD2M8K2 D2M8K2.u2792 = [806087225585, 2413993407010, 1807508428687, 880457990243, 1001459006187, 265670552289, 9533751846, 0] := by
  rw [show D2M8K2.u2792 = KTree.node D2M8K2.u2788 (nat_lit 6968649) (nat_lit 1836561371) (nat_lit 0) D2M8K2.u2791 from rfl, totK_node, atot2788, atot2791]
  decide +kernel

theorem arows2800 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2800 = true := by
  rw [show D2M8K2.u2800 = KTree.node D2M8K2.u2796 (nat_lit 6982301) (nat_lit 2274073490) (nat_lit 0) D2M8K2.u2799 from rfl, allE_node, arows2796, irow2800, arows2799]
  all_goals rfl

theorem atot2800 : totK PD2M8K2 D2M8K2.u2800 = [841462763533, 2953665687467, 2789725628069, 577167643128, 18030242193, 0, 0, 0] := by
  rw [show D2M8K2.u2800 = KTree.node D2M8K2.u2796 (nat_lit 6982301) (nat_lit 2274073490) (nat_lit 0) D2M8K2.u2799 from rfl, totK_node, atot2796, atot2799]
  decide +kernel

theorem arows2807 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2807 = true := by
  rw [show D2M8K2.u2807 = KTree.node D2M8K2.u2803 (nat_lit 6989478) (nat_lit 3775869734) (nat_lit 0) D2M8K2.u2806 from rfl, allE_node, arows2803, irow2807, arows2806]
  all_goals rfl

theorem atot2807 : totK PD2M8K2 D2M8K2.u2807 = [0, 1317541423221, 3538584868926, 1992161245268, 205450303243, 1369150432, 0, 0] := by
  rw [show D2M8K2.u2807 = KTree.node D2M8K2.u2803 (nat_lit 6989478) (nat_lit 3775869734) (nat_lit 0) D2M8K2.u2806 from rfl, totK_node, atot2803, atot2806]
  decide +kernel

theorem arows2819 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2819 = true := by
  rw [show D2M8K2.u2819 = KTree.node D2M8K2.u2815 (nat_lit 7006780) (nat_lit 3828168964) (nat_lit 0) D2M8K2.u2818 from rfl, allE_node, arows2815, irow2819, arows2818]
  all_goals rfl

theorem atot2819 : totK PD2M8K2 D2M8K2.u2819 = [445091534014, 2148717468955, 3222170086022, 1360287117386, 86220563256, 0, 0, 0] := by
  rw [show D2M8K2.u2819 = KTree.node D2M8K2.u2815 (nat_lit 7006780) (nat_lit 3828168964) (nat_lit 0) D2M8K2.u2818 from rfl, totK_node, atot2815, atot2818]
  decide +kernel

theorem arows2826 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2826 = true := by
  rw [show D2M8K2.u2826 = KTree.node D2M8K2.u2822 (nat_lit 7017673) (nat_lit 1426063987) (nat_lit 0) D2M8K2.u2825 from rfl, allE_node, arows2822, irow2826, arows2825]
  all_goals rfl

theorem atot2826 : totK PD2M8K2 D2M8K2.u2826 = [773738422244, 2829718027000, 2935024197507, 740283581406, 25272475536, 0, 0, 0] := by
  rw [show D2M8K2.u2826 = KTree.node D2M8K2.u2822 (nat_lit 7017673) (nat_lit 1426063987) (nat_lit 0) D2M8K2.u2825 from rfl, totK_node, atot2822, atot2825]
  decide +kernel

theorem arows2834 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2834 = true := by
  rw [show D2M8K2.u2834 = KTree.node D2M8K2.u2830 (nat_lit 7025185) (nat_lit 1282460991) (nat_lit 0) D2M8K2.u2833 from rfl, allE_node, arows2830, irow2834, arows2833]
  all_goals rfl

theorem atot2834 : totK PD2M8K2 D2M8K2.u2834 = [829302901382, 2951879096123, 2842329316817, 606552494480, 18047467553, 0, 0, 0] := by
  rw [show D2M8K2.u2834 = KTree.node D2M8K2.u2830 (nat_lit 7025185) (nat_lit 1282460991) (nat_lit 0) D2M8K2.u2833 from rfl, totK_node, atot2830, atot2833]
  decide +kernel

theorem arows2841 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2841 = true := by
  rw [show D2M8K2.u2841 = KTree.node D2M8K2.u2837 (nat_lit 7035245) (nat_lit 2033150400) (nat_lit 0) D2M8K2.u2840 from rfl, allE_node, arows2837, irow2841, arows2840]
  all_goals rfl

theorem atot2841 : totK PD2M8K2 D2M8K2.u2841 = [0, 1041262168446, 3077931920037, 2478620036471, 634006567902, 36921873854, 0, 0] := by
  rw [show D2M8K2.u2841 = KTree.node D2M8K2.u2837 (nat_lit 7035245) (nat_lit 2033150400) (nat_lit 0) D2M8K2.u2840 from rfl, totK_node, atot2837, atot2840]
  decide +kernel

theorem arows2850 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2850 = true := by
  rw [show D2M8K2.u2850 = KTree.node D2M8K2.u2846 (nat_lit 7042493) (nat_lit 1609601109) (nat_lit 0) D2M8K2.u2849 from rfl, allE_node, arows2846, irow2850, arows2849]
  all_goals rfl

theorem atot2850 : totK PD2M8K2 D2M8K2.u2850 = [0, 756793867767, 2980991804007, 2964061202968, 540656966616, 10378741320, 0, 0] := by
  rw [show D2M8K2.u2850 = KTree.node D2M8K2.u2846 (nat_lit 7042493) (nat_lit 1609601109) (nat_lit 0) D2M8K2.u2849 from rfl, totK_node, atot2846, atot2849]
  decide +kernel

theorem arows2857 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2857 = true := by
  rw [show D2M8K2.u2857 = KTree.node D2M8K2.u2853 (nat_lit 7049468) (nat_lit 2999646898) (nat_lit 0) D2M8K2.u2856 from rfl, allE_node, arows2853, irow2857, arows2856]
  all_goals rfl

theorem atot2857 : totK PD2M8K2 D2M8K2.u2857 = [397470960283, 1735572846338, 2693593050925, 1925114952123, 416385838611, 10717512769, 0, 0] := by
  rw [show D2M8K2.u2857 = KTree.node D2M8K2.u2853 (nat_lit 7049468) (nat_lit 2999646898) (nat_lit 0) D2M8K2.u2856 from rfl, totK_node, atot2853, atot2856]
  decide +kernel

theorem arows2865 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2865 = true := by
  rw [show D2M8K2.u2865 = KTree.node D2M8K2.u2861 (nat_lit 7056532) (nat_lit 2694116526) (nat_lit 0) D2M8K2.u2864 from rfl, allE_node, arows2861, irow2865, arows2864]
  all_goals rfl

theorem atot2865 : totK PD2M8K2 D2M8K2.u2865 = [872808095304, 2899476755513, 2757475400610, 751634456558, 38705125895, 0, 0, 0] := by
  rw [show D2M8K2.u2865 = KTree.node D2M8K2.u2861 (nat_lit 7056532) (nat_lit 2694116526) (nat_lit 0) D2M8K2.u2864 from rfl, totK_node, atot2861, atot2864]
  decide +kernel

theorem arows2872 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2872 = true := by
  rw [show D2M8K2.u2872 = KTree.node D2M8K2.u2868 (nat_lit 7066060) (nat_lit 2995109531) (nat_lit 0) D2M8K2.u2871 from rfl, allE_node, arows2868, irow2872, arows2871]
  all_goals rfl

theorem atot2872 : totK PD2M8K2 D2M8K2.u2872 = [836849654700, 2947928962514, 2799550991477, 577118586782, 18134661876, 0, 0, 0] := by
  rw [show D2M8K2.u2872 = KTree.node D2M8K2.u2868 (nat_lit 7066060) (nat_lit 2995109531) (nat_lit 0) D2M8K2.u2871 from rfl, totK_node, atot2868, atot2871]
  decide +kernel

theorem arows2882 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2882 = true := by
  rw [show D2M8K2.u2882 = KTree.node D2M8K2.u2878 (nat_lit 7072852) (nat_lit 3496796485) (nat_lit 0) D2M8K2.u2881 from rfl, allE_node, arows2878, irow2882, arows2881]
  all_goals rfl

theorem atot2882 : totK PD2M8K2 D2M8K2.u2882 = [0, 1307396765399, 3566153639144, 2058200295458, 189723297450, 1206465782, 0, 0] := by
  rw [show D2M8K2.u2882 = KTree.node D2M8K2.u2878 (nat_lit 7072852) (nat_lit 3496796485) (nat_lit 0) D2M8K2.u2881 from rfl, totK_node, atot2878, atot2881]
  decide +kernel

theorem arows2889 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2889 = true := by
  rw [show D2M8K2.u2889 = KTree.node D2M8K2.u2885 (nat_lit 7085130) (nat_lit 3742810749) (nat_lit 0) D2M8K2.u2888 from rfl, allE_node, arows2885, irow2889, arows2888]
  all_goals rfl

theorem atot2889 : totK PD2M8K2 D2M8K2.u2889 = [0, 857548901646, 3054782272824, 2622469099908, 493885874238, 17590593026, 0, 0] := by
  rw [show D2M8K2.u2889 = KTree.node D2M8K2.u2885 (nat_lit 7085130) (nat_lit 3742810749) (nat_lit 0) D2M8K2.u2888 from rfl, totK_node, atot2885, atot2888]
  decide +kernel

theorem arows2897 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2897 = true := by
  rw [show D2M8K2.u2897 = KTree.node D2M8K2.u2893 (nat_lit 7135137) (nat_lit 1575400985) (nat_lit 0) D2M8K2.u2896 from rfl, allE_node, arows2893, irow2897, arows2896]
  all_goals rfl

theorem atot2897 : totK PD2M8K2 D2M8K2.u2897 = [796619420203, 2806123621575, 2754010838208, 822493678946, 55731053596, 0, 0, 0] := by
  rw [show D2M8K2.u2897 = KTree.node D2M8K2.u2893 (nat_lit 7135137) (nat_lit 1575400985) (nat_lit 0) D2M8K2.u2896 from rfl, totK_node, atot2893, atot2896]
  decide +kernel

theorem arows2904 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2904 = true := by
  rw [show D2M8K2.u2904 = KTree.node D2M8K2.u2900 (nat_lit 7141889) (nat_lit 2220641219) (nat_lit 0) D2M8K2.u2903 from rfl, allE_node, arows2900, irow2904, arows2903]
  all_goals rfl

theorem atot2904 : totK PD2M8K2 D2M8K2.u2904 = [750852163593, 2729269755938, 2892309401094, 807659534766, 30430358629, 0, 0, 0] := by
  rw [show D2M8K2.u2904 = KTree.node D2M8K2.u2900 (nat_lit 7141889) (nat_lit 2220641219) (nat_lit 0) D2M8K2.u2903 from rfl, totK_node, atot2900, atot2903]
  decide +kernel

theorem arows2913 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2913 = true := by
  rw [show D2M8K2.u2913 = KTree.node D2M8K2.u2909 (nat_lit 7149118) (nat_lit 3274593186) (nat_lit 0) D2M8K2.u2912 from rfl, allE_node, arows2909, irow2913, arows2912]
  all_goals rfl

theorem atot2913 : totK PD2M8K2 D2M8K2.u2913 = [435720955444, 2125366139104, 3125294732866, 1299907396798, 114532202239, 1138244013, 0, 0] := by
  rw [show D2M8K2.u2913 = KTree.node D2M8K2.u2909 (nat_lit 7149118) (nat_lit 3274593186) (nat_lit 0) D2M8K2.u2912 from rfl, totK_node, atot2909, atot2912]
  decide +kernel

theorem arows2920 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2920 = true := by
  rw [show D2M8K2.u2920 = KTree.node D2M8K2.u2916 (nat_lit 7161993) (nat_lit 1850716406) (nat_lit 0) D2M8K2.u2919 from rfl, allE_node, arows2916, irow2920, arows2919]
  all_goals rfl

theorem atot2920 : totK PD2M8K2 D2M8K2.u2920 = [0, 1426540695887, 3732375923903, 1929176605122, 134700015307, 0, 0, 0] := by
  rw [show D2M8K2.u2920 = KTree.node D2M8K2.u2916 (nat_lit 7161993) (nat_lit 1850716406) (nat_lit 0) D2M8K2.u2919 from rfl, totK_node, atot2916, atot2919]
  decide +kernel

theorem arows2928 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2928 = true := by
  rw [show D2M8K2.u2928 = KTree.node D2M8K2.u2924 (nat_lit 7175968) (nat_lit 2346326243) (nat_lit 0) D2M8K2.u2927 from rfl, allE_node, arows2924, irow2928, arows2927]
  all_goals rfl

theorem atot2928 : totK PD2M8K2 D2M8K2.u2928 = [800159524572, 2502944902051, 2515494548611, 1156245937698, 202011278146, 4977114383, 0, 0] := by
  rw [show D2M8K2.u2928 = KTree.node D2M8K2.u2924 (nat_lit 7175968) (nat_lit 2346326243) (nat_lit 0) D2M8K2.u2927 from rfl, totK_node, atot2924, atot2927]
  decide +kernel

theorem arows2935 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2935 = true := by
  rw [show D2M8K2.u2935 = KTree.node D2M8K2.u2931 (nat_lit 7182721) (nat_lit 1543733305) (nat_lit 0) D2M8K2.u2934 from rfl, allE_node, arows2931, irow2935, arows2934]
  all_goals rfl

theorem atot2935 : totK PD2M8K2 D2M8K2.u2935 = [665651302286, 2636134771704, 2988376417317, 921290542828, 50598507583, 0, 0, 0] := by
  rw [show D2M8K2.u2935 = KTree.node D2M8K2.u2931 (nat_lit 7182721) (nat_lit 1543733305) (nat_lit 0) D2M8K2.u2934 from rfl, totK_node, atot2931, atot2934]
  decide +kernel

theorem arows2946 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2946 = true := by
  rw [show D2M8K2.u2946 = KTree.node D2M8K2.u2942 (nat_lit 7193458) (nat_lit 4023268641) (nat_lit 0) D2M8K2.u2945 from rfl, allE_node, arows2942, irow2946, arows2945]
  all_goals rfl

theorem atot2946 : totK PD2M8K2 D2M8K2.u2946 = [529390851355, 2451550044638, 3198243185257, 996991786011, 42037803812, 0, 0, 0] := by
  rw [show D2M8K2.u2946 = KTree.node D2M8K2.u2942 (nat_lit 7193458) (nat_lit 4023268641) (nat_lit 0) D2M8K2.u2945 from rfl, totK_node, atot2942, atot2945]
  decide +kernel

theorem arows2953 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2953 = true := by
  rw [show D2M8K2.u2953 = KTree.node D2M8K2.u2949 (nat_lit 7200513) (nat_lit 1232234937) (nat_lit 0) D2M8K2.u2952 from rfl, allE_node, arows2949, irow2953, arows2952]
  all_goals rfl

theorem atot2953 : totK PD2M8K2 D2M8K2.u2953 = [0, 939820074135, 3185388315634, 2680214570065, 382746606497, 6190125969, 0, 0] := by
  rw [show D2M8K2.u2953 = KTree.node D2M8K2.u2949 (nat_lit 7200513) (nat_lit 1232234937) (nat_lit 0) D2M8K2.u2952 from rfl, totK_node, atot2949, atot2952]
  decide +kernel

theorem arows2961 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2961 = true := by
  rw [show D2M8K2.u2961 = KTree.node D2M8K2.u2957 (nat_lit 7213256) (nat_lit 3133599772) (nat_lit 0) D2M8K2.u2960 from rfl, allE_node, arows2957, irow2961, arows2960]
  all_goals rfl

theorem atot2961 : totK PD2M8K2 D2M8K2.u2961 = [0, 861242886380, 2954831750053, 2728608749398, 616680387294, 26682572712, 0, 0] := by
  rw [show D2M8K2.u2961 = KTree.node D2M8K2.u2957 (nat_lit 7213256) (nat_lit 3133599772) (nat_lit 0) D2M8K2.u2960 from rfl, totK_node, atot2957, atot2960]
  decide +kernel

theorem arows2968 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2968 = true := by
  rw [show D2M8K2.u2968 = KTree.node D2M8K2.u2964 (nat_lit 7223575) (nat_lit 1481394661) (nat_lit 0) D2M8K2.u2967 from rfl, allE_node, arows2964, irow2968, arows2967]
  all_goals rfl

theorem atot2968 : totK PD2M8K2 D2M8K2.u2968 = [0, 874003291348, 3046146925887, 2720699847929, 495459438959, 14418877666, 0, 0] := by
  rw [show D2M8K2.u2968 = KTree.node D2M8K2.u2964 (nat_lit 7223575) (nat_lit 1481394661) (nat_lit 0) D2M8K2.u2967 from rfl, totK_node, atot2964, atot2967]
  decide +kernel

theorem arows2977 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2977 = true := by
  rw [show D2M8K2.u2977 = KTree.node D2M8K2.u2973 (nat_lit 7234023) (nat_lit 3571624149) (nat_lit 0) D2M8K2.u2976 from rfl, allE_node, arows2973, irow2977, arows2976]
  all_goals rfl

theorem atot2977 : totK PD2M8K2 D2M8K2.u2977 = [0, 645998611296, 2685050104301, 3050836986476, 735232156886, 28248826209, 0, 0] := by
  rw [show D2M8K2.u2977 = KTree.node D2M8K2.u2973 (nat_lit 7234023) (nat_lit 3571624149) (nat_lit 0) D2M8K2.u2976 from rfl, totK_node, atot2973, atot2976]
  decide +kernel

theorem arows2984 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2984 = true := by
  rw [show D2M8K2.u2984 = KTree.node D2M8K2.u2980 (nat_lit 7244989) (nat_lit 1213604548) (nat_lit 0) D2M8K2.u2983 from rfl, allE_node, arows2980, irow2984, arows2983]
  all_goals rfl

theorem atot2984 : totK PD2M8K2 D2M8K2.u2984 = [0, 0, 1324804137743, 3635056882722, 1852791166468, 154145109234, 1275377855, 0] := by
  rw [show D2M8K2.u2984 = KTree.node D2M8K2.u2980 (nat_lit 7244989) (nat_lit 1213604548) (nat_lit 0) D2M8K2.u2983 from rfl, totK_node, atot2980, atot2983]
  decide +kernel

theorem arows2992 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2992 = true := by
  rw [show D2M8K2.u2992 = KTree.node D2M8K2.u2988 (nat_lit 7263560) (nat_lit 3582519073) (nat_lit 0) D2M8K2.u2991 from rfl, allE_node, arows2988, irow2992, arows2991]
  all_goals rfl

theorem atot2992 : totK PD2M8K2 D2M8K2.u2992 = [0, 870676875276, 2871476108771, 2734908328243, 789862048157, 46359328580, 0, 0] := by
  rw [show D2M8K2.u2992 = KTree.node D2M8K2.u2988 (nat_lit 7263560) (nat_lit 3582519073) (nat_lit 0) D2M8K2.u2991 from rfl, totK_node, atot2988, atot2991]
  decide +kernel

theorem arows2999 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2999 = true := by
  rw [show D2M8K2.u2999 = KTree.node D2M8K2.u2995 (nat_lit 7270777) (nat_lit 1367785643) (nat_lit 0) D2M8K2.u2998 from rfl, allE_node, arows2995, irow2999, arows2998]
  all_goals rfl

theorem atot2999 : totK PD2M8K2 D2M8K2.u2999 = [0, 757653798126, 2963612524767, 2970605402273, 588119095867, 17312036757, 0, 0] := by
  rw [show D2M8K2.u2999 = KTree.node D2M8K2.u2995 (nat_lit 7270777) (nat_lit 1367785643) (nat_lit 0) D2M8K2.u2998 from rfl, totK_node, atot2995, atot2998]
  decide +kernel

theorem arows3009 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3009 = true := by
  rw [show D2M8K2.u3009 = KTree.node D2M8K2.u3005 (nat_lit 7277557) (nat_lit 1181378166) (nat_lit 0) D2M8K2.u3008 from rfl, allE_node, arows3005, irow3009, arows3008]
  all_goals rfl

theorem atot3009 : totK PD2M8K2 D2M8K2.u3009 = [0, 813613686571, 2878534363475, 2797125002845, 638887510895, 23006347722, 0, 0] := by
  rw [show D2M8K2.u3009 = KTree.node D2M8K2.u3005 (nat_lit 7277557) (nat_lit 1181378166) (nat_lit 0) D2M8K2.u3008 from rfl, totK_node, atot3005, atot3008]
  decide +kernel

theorem arows3016 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3016 = true := by
  rw [show D2M8K2.u3016 = KTree.node D2M8K2.u3012 (nat_lit 7305460) (nat_lit 3986255077) (nat_lit 0) D2M8K2.u3015 from rfl, allE_node, arows3012, irow3016, arows3015]
  all_goals rfl

theorem atot3016 : totK PD2M8K2 D2M8K2.u3016 = [0, 871813702940, 2983368550676, 2797416141070, 644114413024, 25253243897, 0, 0] := by
  rw [show D2M8K2.u3016 = KTree.node D2M8K2.u3012 (nat_lit 7305460) (nat_lit 3986255077) (nat_lit 0) D2M8K2.u3015 from rfl, totK_node, atot3012, atot3015]
  decide +kernel

theorem arows3024 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3024 = true := by
  rw [show D2M8K2.u3024 = KTree.node D2M8K2.u3020 (nat_lit 7315055) (nat_lit 1697902251) (nat_lit 0) D2M8K2.u3023 from rfl, allE_node, arows3020, irow3024, arows3023]
  all_goals rfl

theorem atot3024 : totK PD2M8K2 D2M8K2.u3024 = [0, 835662425276, 2951936588472, 2795147022788, 549857138552, 17972337965, 0, 0] := by
  rw [show D2M8K2.u3024 = KTree.node D2M8K2.u3020 (nat_lit 7315055) (nat_lit 1697902251) (nat_lit 0) D2M8K2.u3023 from rfl, totK_node, atot3020, atot3023]
  decide +kernel

theorem arows3031 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3031 = true := by
  rw [show D2M8K2.u3031 = KTree.node D2M8K2.u3027 (nat_lit 7322520) (nat_lit 3461536205) (nat_lit 0) D2M8K2.u3030 from rfl, allE_node, arows3027, irow3031, arows3030]
  all_goals rfl

theorem atot3031 : totK PD2M8K2 D2M8K2.u3031 = [0, 0, 1324161452316, 3562565649918, 1975698314376, 186059388406, 1206465782, 0] := by
  rw [show D2M8K2.u3031 = KTree.node D2M8K2.u3027 (nat_lit 7322520) (nat_lit 3461536205) (nat_lit 0) D2M8K2.u3030 from rfl, totK_node, atot3027, atot3030]
  decide +kernel

theorem arows3040 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3040 = true := by
  rw [show D2M8K2.u3040 = KTree.node D2M8K2.u3036 (nat_lit 7334421) (nat_lit 1461964138) (nat_lit 0) D2M8K2.u3039 from rfl, allE_node, arows3036, irow3040, arows3039]
  all_goals rfl

theorem atot3040 : totK PD2M8K2 D2M8K2.u3040 = [0, 0, 924599968146, 3060588251455, 2446243798494, 472643145102, 17590593026, 0] := by
  rw [show D2M8K2.u3040 = KTree.node D2M8K2.u3036 (nat_lit 7334421) (nat_lit 1461964138) (nat_lit 0) D2M8K2.u3039 from rfl, totK_node, atot3036, atot3039]
  decide +kernel

theorem arows3047 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3047 = true := by
  rw [show D2M8K2.u3047 = KTree.node D2M8K2.u3043 (nat_lit 7385885) (nat_lit 2181045978) (nat_lit 0) D2M8K2.u3046 from rfl, allE_node, arows3043, irow3047, arows3046]
  all_goals rfl

theorem atot3047 : totK PD2M8K2 D2M8K2.u3047 = [0, 828694701111, 2915353246235, 2813214594397, 652992119564, 25259541359, 0, 0] := by
  rw [show D2M8K2.u3047 = KTree.node D2M8K2.u3043 (nat_lit 7385885) (nat_lit 2181045978) (nat_lit 0) D2M8K2.u3046 from rfl, totK_node, atot3043, atot3046]
  decide +kernel

theorem arows3055 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3055 = true := by
  rw [show D2M8K2.u3055 = KTree.node D2M8K2.u3051 (nat_lit 7392154) (nat_lit 3980572460) (nat_lit 0) D2M8K2.u3054 from rfl, allE_node, arows3051, irow3055, arows3054]
  all_goals rfl

theorem atot3055 : totK PD2M8K2 D2M8K2.u3055 = [0, 889210323658, 3037852757781, 2709389712754, 530079762590, 17735875666, 0, 0] := by
  rw [show D2M8K2.u3055 = KTree.node D2M8K2.u3051 (nat_lit 7392154) (nat_lit 3980572460) (nat_lit 0) D2M8K2.u3054 from rfl, totK_node, atot3051, atot3054]
  decide +kernel

theorem arows3062 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3062 = true := by
  rw [show D2M8K2.u3062 = KTree.node D2M8K2.u3058 (nat_lit 7403577) (nat_lit 1870966113) (nat_lit 0) D2M8K2.u3061 from rfl, allE_node, arows3058, irow3062, arows3061]
  all_goals rfl

theorem atot3062 : totK PD2M8K2 D2M8K2.u3062 = [0, 263188337172, 1925747567590, 3354190001460, 1415183801578, 105926315316, 1103454931, 0] := by
  rw [show D2M8K2.u3062 = KTree.node D2M8K2.u3058 (nat_lit 7403577) (nat_lit 1870966113) (nat_lit 0) D2M8K2.u3061 from rfl, totK_node, atot3058, atot3061]
  decide +kernel

theorem arows3076 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3076 = true := by
  rw [show D2M8K2.u3076 = KTree.node D2M8K2.u3072 (nat_lit 7416936) (nat_lit 2324261287) (nat_lit 0) D2M8K2.u3075 from rfl, allE_node, arows3072, irow3076, arows3075]
  all_goals rfl

theorem atot3076 : totK PD2M8K2 D2M8K2.u3076 = [0, 173180509234, 1553083895849, 3268271628937, 1756113817693, 205572820164, 4779662215, 0] := by
  rw [show D2M8K2.u3076 = KTree.node D2M8K2.u3072 (nat_lit 7416936) (nat_lit 2324261287) (nat_lit 0) D2M8K2.u3075 from rfl, totK_node, atot3072, atot3075]
  decide +kernel

theorem arows3083 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3083 = true := by
  rw [show D2M8K2.u3083 = KTree.node D2M8K2.u3079 (nat_lit 7428069) (nat_lit 1224073752) (nat_lit 0) D2M8K2.u3082 from rfl, allE_node, arows3079, irow3083, arows3082]
  all_goals rfl

theorem atot3083 : totK PD2M8K2 D2M8K2.u3083 = [0, 797030368763, 2852695474044, 2851888494551, 730210072501, 34131549329, 0, 0] := by
  rw [show D2M8K2.u3083 = KTree.node D2M8K2.u3079 (nat_lit 7428069) (nat_lit 1224073752) (nat_lit 0) D2M8K2.u3082 from rfl, totK_node, atot3079, atot3082]
  decide +kernel

theorem arows3091 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3091 = true := by
  rw [show D2M8K2.u3091 = KTree.node D2M8K2.u3087 (nat_lit 7434730) (nat_lit 3891519254) (nat_lit 0) D2M8K2.u3090 from rfl, allE_node, arows3087, irow3091, arows3090]
  all_goals rfl

theorem atot3091 : totK PD2M8K2 D2M8K2.u3091 = [0, 928593888787, 3082213452058, 2735489703256, 514383563550, 14812611811, 0, 0] := by
  rw [show D2M8K2.u3091 = KTree.node D2M8K2.u3087 (nat_lit 7434730) (nat_lit 3891519254) (nat_lit 0) D2M8K2.u3090 from rfl, totK_node, atot3087, atot3090]
  decide +kernel

theorem arows3098 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3098 = true := by
  rw [show D2M8K2.u3098 = KTree.node D2M8K2.u3094 (nat_lit 7466002) (nat_lit 3780689076) (nat_lit 0) D2M8K2.u3097 from rfl, allE_node, arows3094, irow3098, arows3097]
  all_goals rfl

theorem atot3098 : totK PD2M8K2 D2M8K2.u3098 = [709127292956, 2268515277687, 2357234385772, 1435556656778, 419030376419, 21982452388, 0, 0] := by
  rw [show D2M8K2.u3098 = KTree.node D2M8K2.u3094 (nat_lit 7466002) (nat_lit 3780689076) (nat_lit 0) D2M8K2.u3097 from rfl, totK_node, atot3094, atot3097]
  decide +kernel

theorem arows3107 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3107 = true := by
  rw [show D2M8K2.u3107 = KTree.node D2M8K2.u3103 (nat_lit 7479655) (nat_lit 2386208983) (nat_lit 0) D2M8K2.u3106 from rfl, allE_node, arows3103, irow3107, arows3106]
  all_goals rfl

theorem atot3107 : totK PD2M8K2 D2M8K2.u3107 = [846925594291, 2954538222193, 2768186307852, 582876097592, 18231200220, 0, 0, 0] := by
  rw [show D2M8K2.u3107 = KTree.node D2M8K2.u3103 (nat_lit 7479655) (nat_lit 2386208983) (nat_lit 0) D2M8K2.u3106 from rfl, totK_node, atot3103, atot3106]
  decide +kernel

theorem arows3114 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3114 = true := by
  rw [show D2M8K2.u3114 = KTree.node D2M8K2.u3110 (nat_lit 7486809) (nat_lit 1851267405) (nat_lit 0) D2M8K2.u3113 from rfl, allE_node, arows3110, irow3114, arows3113]
  all_goals rfl

theorem atot3114 : totK PD2M8K2 D2M8K2.u3114 = [91792297750, 1469883250411, 3434152944681, 1883615583904, 200583805922, 1369150432, 0, 0] := by
  rw [show D2M8K2.u3114 = KTree.node D2M8K2.u3110 (nat_lit 7486809) (nat_lit 1851267405) (nat_lit 0) D2M8K2.u3113 from rfl, totK_node, atot3110, atot3113]
  decide +kernel

theorem arows3122 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3122 = true := by
  rw [show D2M8K2.u3122 = KTree.node D2M8K2.u3118 (nat_lit 7503827) (nat_lit 2941866908) (nat_lit 0) D2M8K2.u3121 from rfl, allE_node, arows3118, irow3122, arows3121]
  all_goals rfl

theorem atot3122 : totK PD2M8K2 D2M8K2.u3122 = [445106442645, 2124743225999, 3219260870413, 1373502027768, 83025771066, 0, 0, 0] := by
  rw [show D2M8K2.u3122 = KTree.node D2M8K2.u3118 (nat_lit 7503827) (nat_lit 2941866908) (nat_lit 0) D2M8K2.u3121 from rfl, totK_node, atot3118, atot3121]
  decide +kernel

theorem arows3129 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3129 = true := by
  rw [show D2M8K2.u3129 = KTree.node D2M8K2.u3125 (nat_lit 7515486) (nat_lit 3638532336) (nat_lit 0) D2M8K2.u3128 from rfl, allE_node, arows3125, irow3129, arows3128]
  all_goals rfl

theorem atot3129 : totK PD2M8K2 D2M8K2.u3129 = [773803482367, 2789348703394, 2919002068410, 791492215850, 33263596736, 0, 0, 0] := by
  rw [show D2M8K2.u3129 = KTree.node D2M8K2.u3125 (nat_lit 7515486) (nat_lit 3638532336) (nat_lit 0) D2M8K2.u3128 from rfl, totK_node, atot3125, atot3128]
  decide +kernel

theorem arows3139 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3139 = true := by
  rw [show D2M8K2.u3139 = KTree.node D2M8K2.u3135 (nat_lit 7522300) (nat_lit 3899454054) (nat_lit 0) D2M8K2.u3138 from rfl, allE_node, arows3135, irow3139, arows3138]
  all_goals rfl

theorem atot3139 : totK PD2M8K2 D2M8K2.u3139 = [829394532047, 2965192219589, 2839230640057, 596396979605, 18285006710, 0, 0, 0] := by
  rw [show D2M8K2.u3139 = KTree.node D2M8K2.u3135 (nat_lit 7522300) (nat_lit 3899454054) (nat_lit 0) D2M8K2.u3138 from rfl, totK_node, atot3135, atot3138]
  decide +kernel

theorem arows3146 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3146 = true := by
  rw [show D2M8K2.u3146 = KTree.node D2M8K2.u3142 (nat_lit 7532666) (nat_lit 4294967296) (nat_lit 0) D2M8K2.u3145 from rfl, allE_node, arows3142, irow3146, arows3145]
  all_goals rfl

theorem atot3146 : totK PD2M8K2 D2M8K2.u3146 = [0, 1085413119548, 3089839464269, 2443376256894, 632406203017, 36921873854, 0, 0] := by
  rw [show D2M8K2.u3146 = KTree.node D2M8K2.u3142 (nat_lit 7532666) (nat_lit 4294967296) (nat_lit 0) D2M8K2.u3145 from rfl, totK_node, atot3142, atot3145]
  decide +kernel

theorem arows3154 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3154 = true := by
  rw [show D2M8K2.u3154 = KTree.node D2M8K2.u3150 (nat_lit 7539269) (nat_lit 1219014616) (nat_lit 0) D2M8K2.u3153 from rfl, allE_node, arows3150, irow3154, arows3153]
  all_goals rfl

theorem atot3154 : totK PD2M8K2 D2M8K2.u3154 = [0, 852035263618, 3070245571835, 2784319435750, 502718759489, 10378741320, 0, 0] := by
  rw [show D2M8K2.u3154 = KTree.node D2M8K2.u3150 (nat_lit 7539269) (nat_lit 1219014616) (nat_lit 0) D2M8K2.u3153 from rfl, totK_node, atot3150, atot3153]
  decide +kernel

theorem arows3161 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3161 = true := by
  rw [show D2M8K2.u3161 = KTree.node D2M8K2.u3157 (nat_lit 7546784) (nat_lit 3323075049) (nat_lit 0) D2M8K2.u3160 from rfl, allE_node, arows3157, irow3161, arows3160]
  all_goals rfl

theorem atot3161 : totK PD2M8K2 D2M8K2.u3161 = [397564749128, 1569716966241, 2604946947045, 2154076354326, 455735400748, 10717512769, 0, 0] := by
  rw [show D2M8K2.u3161 = KTree.node D2M8K2.u3157 (nat_lit 7546784) (nat_lit 3323075049) (nat_lit 0) D2M8K2.u3160 from rfl, totK_node, atot3157, atot3160]
  decide +kernel

theorem arows3170 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3170 = true := by
  rw [show D2M8K2.u3170 = KTree.node D2M8K2.u3166 (nat_lit 7595337) (nat_lit 1686245097) (nat_lit 0) D2M8K2.u3169 from rfl, allE_node, arows3166, irow3170, arows3169]
  all_goals rfl

theorem atot3170 : totK PD2M8K2 D2M8K2.u3170 = [872994368376, 2955130006708, 2756500203384, 707602001549, 37536932523, 0, 0, 0] := by
  rw [show D2M8K2.u3170 = KTree.node D2M8K2.u3166 (nat_lit 7595337) (nat_lit 1686245097) (nat_lit 0) D2M8K2.u3169 from rfl, totK_node, atot3166, atot3169]
  decide +kernel

theorem arows3177 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3177 = true := by
  rw [show D2M8K2.u3177 = KTree.node D2M8K2.u3173 (nat_lit 7604530) (nat_lit 3245124396) (nat_lit 0) D2M8K2.u3176 from rfl, allE_node, arows3173, irow3177, arows3176]
  all_goals rfl

theorem atot3177 : totK PD2M8K2 D2M8K2.u3177 = [837001742390, 2949572071159, 2807402044357, 589459510021, 18231200220, 0, 0, 0] := by
  rw [show D2M8K2.u3177 = KTree.node D2M8K2.u3173 (nat_lit 7604530) (nat_lit 3245124396) (nat_lit 0) D2M8K2.u3176 from rfl, totK_node, atot3173, atot3176]
  decide +kernel

theorem arows3185 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3185 = true := by
  rw [show D2M8K2.u3185 = KTree.node D2M8K2.u3181 (nat_lit 7611685) (nat_lit 1367397861) (nat_lit 0) D2M8K2.u3184 from rfl, allE_node, arows3181, irow3185, arows3184]
  all_goals rfl

theorem atot3185 : totK PD2M8K2 D2M8K2.u3185 = [0, 1308914417930, 3553728195645, 2065034784270, 192821543488, 1239866073, 0, 0] := by
  rw [show D2M8K2.u3185 = KTree.node D2M8K2.u3181 (nat_lit 7611685) (nat_lit 1367397861) (nat_lit 0) D2M8K2.u3184 from rfl, totK_node, atot3181, atot3184]
  decide +kernel

theorem arows3192 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3192 = true := by
  rw [show D2M8K2.u3192 = KTree.node D2M8K2.u3188 (nat_lit 7623726) (nat_lit 4048482758) (nat_lit 0) D2M8K2.u3191 from rfl, allE_node, arows3188, irow3192, arows3191]
  all_goals rfl

theorem atot3192 : totK PD2M8K2 D2M8K2.u3192 = [0, 872028626759, 3038585038036, 2637837548372, 500050112576, 17826068843, 0, 0] := by
  rw [show D2M8K2.u3192 = KTree.node D2M8K2.u3188 (nat_lit 7623726) (nat_lit 4048482758) (nat_lit 0) D2M8K2.u3191 from rfl, totK_node, atot3188, atot3191]
  decide +kernel

theorem arows3203 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3203 = true := by
  rw [show D2M8K2.u3203 = KTree.node D2M8K2.u3199 (nat_lit 7632372) (nat_lit 3215387251) (nat_lit 0) D2M8K2.u3202 from rfl, allE_node, arows3199, irow3203, arows3202]
  all_goals rfl

theorem atot3203 : totK PD2M8K2 D2M8K2.u3203 = [796724878130, 2807319899622, 2783944945016, 800373411874, 48012342301, 0, 0, 0] := by
  rw [show D2M8K2.u3203 = KTree.node D2M8K2.u3199 (nat_lit 7632372) (nat_lit 3215387251) (nat_lit 0) D2M8K2.u3202 from rfl, totK_node, atot3199, atot3202]
  decide +kernel

theorem arows3210 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3210 = true := by
  rw [show D2M8K2.u3210 = KTree.node D2M8K2.u3206 (nat_lit 7639499) (nat_lit 2629515287) (nat_lit 0) D2M8K2.u3209 from rfl, allE_node, arows3206, irow3210, arows3209]
  all_goals rfl

theorem atot3210 : totK PD2M8K2 D2M8K2.u3210 = [750923452992, 2692534383908, 2847708929419, 883418870806, 50617329729, 0, 0, 0] := by
  rw [show D2M8K2.u3210 = KTree.node D2M8K2.u3206 (nat_lit 7639499) (nat_lit 2629515287) (nat_lit 0) D2M8K2.u3209 from rfl, totK_node, atot3206, atot3209]
  decide +kernel

theorem arows3218 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3218 = true := by
  rw [show D2M8K2.u3218 = KTree.node D2M8K2.u3214 (nat_lit 7646051) (nat_lit 1577134843) (nat_lit 0) D2M8K2.u3217 from rfl, allE_node, arows3214, irow3218, arows3217]
  all_goals rfl

theorem atot3218 : totK PD2M8K2 D2M8K2.u3218 = [435739754619, 2273576654617, 3253639217276, 1101746976058, 60032653200, 0, 0, 0] := by
  rw [show D2M8K2.u3218 = KTree.node D2M8K2.u3214 (nat_lit 7646051) (nat_lit 1577134843) (nat_lit 0) D2M8K2.u3217 from rfl, totK_node, atot3214, atot3217]
  decide +kernel

theorem arows3225 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3225 = true := by
  rw [show D2M8K2.u3225 = KTree.node D2M8K2.u3221 (nat_lit 7659076) (nat_lit 3869846782) (nat_lit 0) D2M8K2.u3224 from rfl, allE_node, arows3221, irow3225, arows3224]
  all_goals rfl

theorem atot3225 : totK PD2M8K2 D2M8K2.u3225 = [0, 1338941848547, 3653102947126, 2040001871147, 173049988296, 1138244013, 0, 0] := by
  rw [show D2M8K2.u3225 = KTree.node D2M8K2.u3221 (nat_lit 7659076) (nat_lit 3869846782) (nat_lit 0) D2M8K2.u3224 from rfl, totK_node, atot3221, atot3224]
  decide +kernel

theorem arows3234 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3234 = true := by
  rw [show D2M8K2.u3234 = KTree.node D2M8K2.u3230 (nat_lit 7673214) (nat_lit 3939651568) (nat_lit 0) D2M8K2.u3233 from rfl, allE_node, arows3230, irow3234, arows3233]
  all_goals rfl

theorem atot3234 : totK PD2M8K2 D2M8K2.u3234 = [640703952463, 2272311816724, 2684752240449, 1332663285239, 217319693121, 4977114383, 0, 0] := by
  rw [show D2M8K2.u3234 = KTree.node D2M8K2.u3230 (nat_lit 7673214) (nat_lit 3939651568) (nat_lit 0) D2M8K2.u3233 from rfl, totK_node, atot3230, atot3233]
  decide +kernel

theorem arows3241 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3241 = true := by
  rw [show D2M8K2.u3241 = KTree.node D2M8K2.u3237 (nat_lit 7679802) (nat_lit 3445434644) (nat_lit 0) D2M8K2.u3240 from rfl, allE_node, arows3237, irow3241, arows3240]
  all_goals rfl

theorem atot3241 : totK PD2M8K2 D2M8K2.u3241 = [824675158634, 2793396437728, 2822705173583, 838876697437, 47029009842, 0, 0, 0] := by
  rw [show D2M8K2.u3241 = KTree.node D2M8K2.u3237 (nat_lit 7679802) (nat_lit 3445434644) (nat_lit 0) D2M8K2.u3240 from rfl, totK_node, atot3237, atot3240]
  decide +kernel

theorem arows3249 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3249 = true := by
  rw [show D2M8K2.u3249 = KTree.node D2M8K2.u3245 (nat_lit 7690492) (nat_lit 3248944430) (nat_lit 0) D2M8K2.u3248 from rfl, allE_node, arows3245, irow3249, arows3248]
  all_goals rfl

theorem atot3249 : totK PD2M8K2 D2M8K2.u3249 = [530041065405, 2508499818956, 3185127340630, 945378393219, 40628634021, 0, 0, 0] := by
  rw [show D2M8K2.u3249 = KTree.node D2M8K2.u3245 (nat_lit 7690492) (nat_lit 3248944430) (nat_lit 0) D2M8K2.u3248 from rfl, totK_node, atot3245, atot3248]
  decide +kernel

theorem arows3256 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3256 = true := by
  rw [show D2M8K2.u3256 = KTree.node D2M8K2.u3252 (nat_lit 7697755) (nat_lit 2213445348) (nat_lit 0) D2M8K2.u3255 from rfl, allE_node, arows3252, irow3256, arows3255]
  all_goals rfl

theorem atot3256 : totK PD2M8K2 D2M8K2.u3256 = [0, 993722927370, 3225726859444, 2617432946323, 371877711331, 6190125969, 0, 0] := by
  rw [show D2M8K2.u3256 = KTree.node D2M8K2.u3252 (nat_lit 7697755) (nat_lit 2213445348) (nat_lit 0) D2M8K2.u3255 from rfl, totK_node, atot3252, atot3255]
  decide +kernel

theorem arows3266 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3266 = true := by
  rw [show D2M8K2.u3266 = KTree.node D2M8K2.u3262 (nat_lit 7710582) (nat_lit 3498374683) (nat_lit 0) D2M8K2.u3265 from rfl, allE_node, arows3262, irow3266, arows3265]
  all_goals rfl

theorem atot3266 : totK PD2M8K2 D2M8K2.u3266 = [0, 786805060216, 2937337914290, 2805821117728, 587312693637, 17078344704, 0, 0] := by
  rw [show D2M8K2.u3266 = KTree.node D2M8K2.u3262 (nat_lit 7710582) (nat_lit 3498374683) (nat_lit 0) D2M8K2.u3265 from rfl, totK_node, atot3262, atot3265]
  decide +kernel

theorem arows3273 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3273 = true := by
  rw [show D2M8K2.u3273 = KTree.node D2M8K2.u3269 (nat_lit 7724272) (nat_lit 3109673283) (nat_lit 0) D2M8K2.u3272 from rfl, allE_node, arows3269, irow3273, arows3272]
  all_goals rfl

theorem atot3273 : totK PD2M8K2 D2M8K2.u3273 = [0, 849103358331, 2995681590471, 2742925755958, 549810524444, 24163376948, 0, 0] := by
  rw [show D2M8K2.u3273 = KTree.node D2M8K2.u3269 (nat_lit 7724272) (nat_lit 3109673283) (nat_lit 0) D2M8K2.u3272 from rfl, totK_node, atot3269, atot3272]
  decide +kernel

theorem arows3281 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3281 = true := by
  rw [show D2M8K2.u3281 = KTree.node D2M8K2.u3277 (nat_lit 7731236) (nat_lit 2722899603) (nat_lit 0) D2M8K2.u3280 from rfl, allE_node, arows3277, irow3281, arows3280]
  all_goals rfl

theorem atot3281 : totK PD2M8K2 D2M8K2.u3281 = [0, 792969625575, 2927659164658, 2848336182023, 576254197663, 18668480565, 0, 0] := by
  rw [show D2M8K2.u3281 = KTree.node D2M8K2.u3277 (nat_lit 7731236) (nat_lit 2722899603) (nat_lit 0) D2M8K2.u3280 from rfl, totK_node, atot3277, atot3280]
  decide +kernel

theorem arows3288 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3288 = true := by
  rw [show D2M8K2.u3288 = KTree.node D2M8K2.u3284 (nat_lit 7745445) (nat_lit 1251227885) (nat_lit 0) D2M8K2.u3287 from rfl, allE_node, arows3284, irow3288, arows3287]
  all_goals rfl

theorem atot3288 : totK PD2M8K2 D2M8K2.u3288 = [0, 0, 1247979022542, 3607028079569, 1940952320999, 163276233667, 1310517177, 0] := by
  rw [show D2M8K2.u3288 = KTree.node D2M8K2.u3284 (nat_lit 7745445) (nat_lit 1251227885) (nat_lit 0) D2M8K2.u3287 from rfl, totK_node, atot3284, atot3287]
  decide +kernel

theorem arows3297 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3297 = true := by
  rw [show D2M8K2.u3297 = KTree.node D2M8K2.u3293 (nat_lit 7760841) (nat_lit 1886076144) (nat_lit 0) D2M8K2.u3296 from rfl, allE_node, arows3293, irow3297, arows3296]
  all_goals rfl

theorem atot3297 : totK PD2M8K2 D2M8K2.u3297 = [0, 791243469301, 2754080731940, 2851118128206, 888475987655, 50310153989, 0, 0] := by
  rw [show D2M8K2.u3297 = KTree.node D2M8K2.u3293 (nat_lit 7760841) (nat_lit 1886076144) (nat_lit 0) D2M8K2.u3296 from rfl, totK_node, atot3293, atot3296]
  decide +kernel

theorem arows3304 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3304 = true := by
  rw [show D2M8K2.u3304 = KTree.node D2M8K2.u3300 (nat_lit 7767494) (nat_lit 3270929762) (nat_lit 0) D2M8K2.u3303 from rfl, allE_node, arows3300, irow3304, arows3303]
  all_goals rfl

theorem atot3304 : totK PD2M8K2 D2M8K2.u3304 = [0, 837854608562, 2972812576894, 2807756369706, 595803205297, 18553496863, 0, 0] := by
  rw [show D2M8K2.u3304 = KTree.node D2M8K2.u3300 (nat_lit 7767494) (nat_lit 3270929762) (nat_lit 0) D2M8K2.u3303 from rfl, totK_node, atot3300, atot3303]
  decide +kernel

theorem arows3312 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3312 = true := by
  rw [show D2M8K2.u3312 = KTree.node D2M8K2.u3308 (nat_lit 7774590) (nat_lit 3908287112) (nat_lit 0) D2M8K2.u3311 from rfl, allE_node, arows3308, irow3312, arows3311]
  all_goals rfl

theorem atot3312 : totK PD2M8K2 D2M8K2.u3312 = [0, 813939523380, 2940453133465, 2809067811929, 614351311727, 21707210787, 0, 0] := by
  rw [show D2M8K2.u3312 = KTree.node D2M8K2.u3308 (nat_lit 7774590) (nat_lit 3908287112) (nat_lit 0) D2M8K2.u3311 from rfl, totK_node, atot3308, atot3311]
  decide +kernel

theorem arows3319 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3319 = true := by
  rw [show D2M8K2.u3319 = KTree.node D2M8K2.u3315 (nat_lit 7843921) (nat_lit 827039904) (nat_lit 0) D2M8K2.u3318 from rfl, allE_node, arows3315, irow3319, arows3318]
  all_goals rfl

theorem atot3319 : totK PD2M8K2 D2M8K2.u3319 = [0, 872001177385, 2889817062462, 2768181694143, 707783655221, 31520323406, 0, 0] := by
  rw [show D2M8K2.u3319 = KTree.node D2M8K2.u3315 (nat_lit 7843921) (nat_lit 827039904) (nat_lit 0) D2M8K2.u3318 from rfl, totK_node, atot3315, atot3318]
  decide +kernel

theorem arows3331 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3331 = true := by
  rw [show D2M8K2.u3331 = KTree.node D2M8K2.u3327 (nat_lit 7853206) (nat_lit 2583561109) (nat_lit 0) D2M8K2.u3330 from rfl, allE_node, arows3327, irow3331, arows3330]
  all_goals rfl

theorem atot3331 : totK PD2M8K2 D2M8K2.u3331 = [0, 801062410349, 2933366544133, 2839291418287, 574027805001, 18231200220, 0, 0] := by
  rw [show D2M8K2.u3331 = KTree.node D2M8K2.u3327 (nat_lit 7853206) (nat_lit 2583561109) (nat_lit 0) D2M8K2.u3330 from rfl, totK_node, atot3327, atot3330]
  decide +kernel

theorem arows3338 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3338 = true := by
  rw [show D2M8K2.u3338 = KTree.node D2M8K2.u3334 (nat_lit 7860384) (nat_lit 3722405375) (nat_lit 0) D2M8K2.u3337 from rfl, allE_node, arows3334, irow3338, arows3337]
  all_goals rfl

theorem atot3338 : totK PD2M8K2 D2M8K2.u3338 = [0, 30722815107, 1461682507610, 3544496882115, 1821358151483, 167928170416, 1217496766, 0] := by
  rw [show D2M8K2.u3338 = KTree.node D2M8K2.u3334 (nat_lit 7860384) (nat_lit 3722405375) (nat_lit 0) D2M8K2.u3337 from rfl, totK_node, atot3334, atot3337]
  decide +kernel

theorem arows3346 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3346 = true := by
  rw [show D2M8K2.u3346 = KTree.node D2M8K2.u3342 (nat_lit 7872816) (nat_lit 3570524400) (nat_lit 0) D2M8K2.u3345 from rfl, allE_node, arows3342, irow3346, arows3345]
  all_goals rfl

theorem atot3346 : totK PD2M8K2 D2M8K2.u3346 = [0, 0, 850412056061, 3050836266538, 2542307567524, 485980303392, 17736366219, 0] := by
  rw [show D2M8K2.u3346 = KTree.node D2M8K2.u3342 (nat_lit 7872816) (nat_lit 3570524400) (nat_lit 0) D2M8K2.u3345 from rfl, totK_node, atot3342, atot3345]
  decide +kernel

theorem arows3353 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3353 = true := by
  rw [show D2M8K2.u3353 = KTree.node D2M8K2.u3349 (nat_lit 7881558) (nat_lit 3524409613) (nat_lit 0) D2M8K2.u3352 from rfl, allE_node, arows3349, irow3353, arows3352]
  all_goals rfl

theorem atot3353 : totK PD2M8K2 D2M8K2.u3353 = [0, 796577075393, 2894189085025, 2805081897998, 705367612832, 36105755122, 0, 0] := by
  rw [show D2M8K2.u3353 = KTree.node D2M8K2.u3349 (nat_lit 7881558) (nat_lit 3524409613) (nat_lit 0) D2M8K2.u3352 from rfl, totK_node, atot3349, atot3352]
  decide +kernel

theorem arows3362 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3362 = true := by
  rw [show D2M8K2.u3362 = KTree.node D2M8K2.u3358 (nat_lit 7889573) (nat_lit 2328353676) (nat_lit 0) D2M8K2.u3361 from rfl, allE_node, arows3358, irow3362, arows3361]
  all_goals rfl

theorem atot3362 : totK PD2M8K2 D2M8K2.u3362 = [0, 750627698194, 2857501342923, 2928266588157, 650318215374, 19613177812, 0, 0] := by
  rw [show D2M8K2.u3362 = KTree.node D2M8K2.u3358 (nat_lit 7889573) (nat_lit 2328353676) (nat_lit 0) D2M8K2.u3361 from rfl, totK_node, atot3358, atot3361]
  decide +kernel

theorem arows3369 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3369 = true := by
  rw [show D2M8K2.u3369 = KTree.node D2M8K2.u3365 (nat_lit 7896402) (nat_lit 3192376211) (nat_lit 0) D2M8K2.u3368 from rfl, allE_node, arows3365, irow3369, arows3368]
  all_goals rfl

theorem atot3369 : totK PD2M8K2 D2M8K2.u3369 = [0, 435665402311, 2077316717014, 3109144741875, 1318862479875, 105785099529, 1138244013, 0] := by
  rw [show D2M8K2.u3369 = KTree.node D2M8K2.u3365 (nat_lit 7896402) (nat_lit 3192376211) (nat_lit 0) D2M8K2.u3368 from rfl, totK_node, atot3365, atot3368]
  decide +kernel

theorem arows3377 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3377 = true := by
  rw [show D2M8K2.u3377 = KTree.node D2M8K2.u3373 (nat_lit 7911864) (nat_lit 3424934041) (nat_lit 0) D2M8K2.u3376 from rfl, allE_node, arows3373, irow3377, arows3376]
  all_goals rfl

theorem atot3377 : totK PD2M8K2 D2M8K2.u3377 = [0, 0, 1488823784817, 3667277404564, 1730896225042, 129801459550, 1095107716, 0] := by
  rw [show D2M8K2.u3377 = KTree.node D2M8K2.u3373 (nat_lit 7911864) (nat_lit 3424934041) (nat_lit 0) D2M8K2.u3376 from rfl, totK_node, atot3373, atot3376]
  decide +kernel

theorem arows3384 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3384 = true := by
  rw [show D2M8K2.u3384 = KTree.node D2M8K2.u3380 (nat_lit 7924381) (nat_lit 1137461297) (nat_lit 0) D2M8K2.u3383 from rfl, allE_node, arows3380, irow3384, arows3383]
  all_goals rfl

theorem atot3384 : totK PD2M8K2 D2M8K2.u3384 = [0, 799596199567, 2729751771594, 2662180633962, 896040458030, 119698881015, 3819176523, 0] := by
  rw [show D2M8K2.u3384 = KTree.node D2M8K2.u3380 (nat_lit 7924381) (nat_lit 1137461297) (nat_lit 0) D2M8K2.u3383 from rfl, totK_node, atot3380, atot3383]
  decide +kernel

theorem arows3394 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3394 = true := by
  rw [show D2M8K2.u3394 = KTree.node D2M8K2.u3390 (nat_lit 7931623) (nat_lit 2347207200) (nat_lit 0) D2M8K2.u3393 from rfl, allE_node, arows3390, irow3394, arows3393]
  all_goals rfl

theorem atot3394 : totK PD2M8K2 D2M8K2.u3394 = [0, 753935014653, 2796772396796, 2932159778555, 722498227572, 26434088857, 0, 0] := by
  rw [show D2M8K2.u3394 = KTree.node D2M8K2.u3390 (nat_lit 7931623) (nat_lit 2347207200) (nat_lit 0) D2M8K2.u3393 from rfl, totK_node, atot3390, atot3393]
  decide +kernel

theorem arows3401 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3401 = true := by
  rw [show D2M8K2.u3401 = KTree.node D2M8K2.u3397 (nat_lit 7941273) (nat_lit 1441498236) (nat_lit 0) D2M8K2.u3400 from rfl, allE_node, arows3397, irow3401, arows3400]
  all_goals rfl

theorem atot3401 : totK PD2M8K2 D2M8K2.u3401 = [421562263945, 1839550711024, 2674109275650, 1785439625712, 455488679084, 21982715828, 0, 0] := by
  rw [show D2M8K2.u3401 = KTree.node D2M8K2.u3397 (nat_lit 7941273) (nat_lit 1441498236) (nat_lit 0) D2M8K2.u3400 from rfl, totK_node, atot3397, atot3400]
  decide +kernel

theorem arows3409 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3409 = true := by
  rw [show D2M8K2.u3409 = KTree.node D2M8K2.u3405 (nat_lit 7972656) (nat_lit 3223242483) (nat_lit 0) D2M8K2.u3408 from rfl, allE_node, arows3405, irow3409, arows3408]
  all_goals rfl

theorem atot3409 : totK PD2M8K2 D2M8K2.u3409 = [800246502269, 2862989435014, 2830857305672, 644403720227, 23730720996, 0, 0, 0] := by
  rw [show D2M8K2.u3409 = KTree.node D2M8K2.u3405 (nat_lit 7972656) (nat_lit 3223242483) (nat_lit 0) D2M8K2.u3408 from rfl, totK_node, atot3405, atot3408]
  decide +kernel

theorem arows3416 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3416 = true := by
  rw [show D2M8K2.u3416 = KTree.node D2M8K2.u3412 (nat_lit 7979478) (nat_lit 3304979610) (nat_lit 0) D2M8K2.u3415 from rfl, allE_node, arows3412, irow3416, arows3415]
  all_goals rfl

theorem atot3416 : totK PD2M8K2 D2M8K2.u3416 = [422517799814, 2033992452661, 3026386609797, 1434162317372, 172035740266, 1369150432, 0, 0] := by
  rw [show D2M8K2.u3416 = KTree.node D2M8K2.u3412 (nat_lit 7979478) (nat_lit 3304979610) (nat_lit 0) D2M8K2.u3415 from rfl, totK_node, atot3412, atot3415]
  decide +kernel

theorem arows3425 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3425 = true := by
  rw [show D2M8K2.u3425 = KTree.node D2M8K2.u3421 (nat_lit 7995313) (nat_lit 1530362503) (nat_lit 0) D2M8K2.u3424 from rfl, allE_node, arows3421, irow3425, arows3424]
  all_goals rfl

theorem atot3425 : totK PD2M8K2 D2M8K2.u3425 = [292455968535, 1888367708207, 3440099323940, 1487723562783, 76690710132, 0, 0, 0] := by
  rw [show D2M8K2.u3425 = KTree.node D2M8K2.u3421 (nat_lit 7995313) (nat_lit 1530362503) (nat_lit 0) D2M8K2.u3424 from rfl, totK_node, atot3421, atot3424]
  decide +kernel

theorem arows3432 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3432 = true := by
  rw [show D2M8K2.u3432 = KTree.node D2M8K2.u3428 (nat_lit 8011521) (nat_lit 1751645922) (nat_lit 0) D2M8K2.u3431 from rfl, allE_node, arows3428, irow3432, arows3431]
  all_goals rfl

theorem atot3432 : totK PD2M8K2 D2M8K2.u3432 = [718326655763, 2672213075397, 2920591485449, 915523644131, 50646263903, 0, 0, 0] := by
  rw [show D2M8K2.u3432 = KTree.node D2M8K2.u3428 (nat_lit 8011521) (nat_lit 1751645922) (nat_lit 0) D2M8K2.u3431 from rfl, totK_node, atot3428, atot3431]
  decide +kernel

theorem arows3440 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3440 = true := by
  rw [show D2M8K2.u3440 = KTree.node D2M8K2.u3436 (nat_lit 8018318) (nat_lit 3878762720) (nat_lit 0) D2M8K2.u3439 from rfl, allE_node, arows3436, irow3440, arows3439]
  all_goals rfl

theorem atot3440 : totK PD2M8K2 D2M8K2.u3440 = [809065547839, 2941731833763, 2894111907206, 602492678257, 18214542822, 0, 0, 0] := by
  rw [show D2M8K2.u3440 = KTree.node D2M8K2.u3436 (nat_lit 8018318) (nat_lit 3878762720) (nat_lit 0) D2M8K2.u3439 from rfl, totK_node, atot3436, atot3439]
  decide +kernel

theorem arows3447 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3447 = true := by
  rw [show D2M8K2.u3447 = KTree.node D2M8K2.u3443 (nat_lit 8029135) (nat_lit 1426885212) (nat_lit 0) D2M8K2.u3446 from rfl, allE_node, arows3443, irow3447, arows3446]
  all_goals rfl

theorem atot3447 : totK PD2M8K2 D2M8K2.u3447 = [218196713264, 1468189545392, 2839284136191, 2112857644795, 598289091271, 36921873854, 0, 0] := by
  rw [show D2M8K2.u3447 = KTree.node D2M8K2.u3443 (nat_lit 8029135) (nat_lit 1426885212) (nat_lit 0) D2M8K2.u3446 from rfl, totK_node, atot3443, atot3446]
  decide +kernel

theorem arows3458 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3458 = true := by
  rw [show D2M8K2.u3458 = KTree.node D2M8K2.u3454 (nat_lit 8035532) (nat_lit 3740007784) (nat_lit 0) D2M8K2.u3457 from rfl, allE_node, arows3454, irow3458, arows3457]
  all_goals rfl

theorem atot3458 : totK PD2M8K2 D2M8K2.u3458 = [0, 897111018680, 3085545475615, 2739823955686, 494678115564, 10378741320, 0, 0] := by
  rw [show D2M8K2.u3458 = KTree.node D2M8K2.u3454 (nat_lit 8035532) (nat_lit 3740007784) (nat_lit 0) D2M8K2.u3457 from rfl, totK_node, atot3454, atot3457]
  decide +kernel

theorem arows3465 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3465 = true := by
  rw [show D2M8K2.u3465 = KTree.node D2M8K2.u3461 (nat_lit 8042837) (nat_lit 2292212220) (nat_lit 0) D2M8K2.u3464 from rfl, allE_node, arows3461, irow3465, arows3464]
  all_goals rfl

theorem atot3465 : totK PD2M8K2 D2M8K2.u3465 = [244726993122, 1227664472829, 2744205757399, 2526648842728, 497669312945, 10717512769, 0, 0] := by
  rw [show D2M8K2.u3465 = KTree.node D2M8K2.u3461 (nat_lit 8042837) (nat_lit 2292212220) (nat_lit 0) D2M8K2.u3464 from rfl, totK_node, atot3461, atot3464]
  decide +kernel

theorem arows3473 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3473 = true := by
  rw [show D2M8K2.u3473 = KTree.node D2M8K2.u3469 (nat_lit 8050477) (nat_lit 1157769382) (nat_lit 0) D2M8K2.u3472 from rfl, allE_node, arows3469, irow3473, arows3472]
  all_goals rfl

theorem atot3473 : totK PD2M8K2 D2M8K2.u3473 = [818905216670, 2843642537290, 2817759899563, 770450813336, 38933689765, 0, 0, 0] := by
  rw [show D2M8K2.u3473 = KTree.node D2M8K2.u3469 (nat_lit 8050477) (nat_lit 1157769382) (nat_lit 0) D2M8K2.u3472 from rfl, totK_node, atot3469, atot3472]
  decide +kernel

theorem arows3480 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3480 = true := by
  rw [show D2M8K2.u3480 = KTree.node D2M8K2.u3476 (nat_lit 8059986) (nat_lit 2556954707) (nat_lit 0) D2M8K2.u3479 from rfl, allE_node, arows3476, irow3480, arows3479]
  all_goals rfl

theorem atot3480 : totK PD2M8K2 D2M8K2.u3480 = [816066792534, 2943968240353, 2851519364725, 584654620569, 18030242193, 0, 0, 0] := by
  rw [show D2M8K2.u3480 = KTree.node D2M8K2.u3476 (nat_lit 8059986) (nat_lit 2556954707) (nat_lit 0) D2M8K2.u3479 from rfl, totK_node, atot3476, atot3479]
  decide +kernel

theorem arows3489 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3489 = true := by
  rw [show D2M8K2.u3489 = KTree.node D2M8K2.u3485 (nat_lit 8067749) (nat_lit 2306827367) (nat_lit 0) D2M8K2.u3488 from rfl, allE_node, arows3485, irow3489, arows3488]
  all_goals rfl

theorem atot3489 : totK PD2M8K2 D2M8K2.u3489 = [103540504535, 1504490842928, 3425528280130, 1930515654296, 185836497909, 1206465782, 0, 0] := by
  rw [show D2M8K2.u3489 = KTree.node D2M8K2.u3485 (nat_lit 8067749) (nat_lit 2306827367) (nat_lit 0) D2M8K2.u3488 from rfl, totK_node, atot3485, atot3488]
  decide +kernel

theorem arows3496 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3496 = true := by
  rw [show D2M8K2.u3496 = KTree.node D2M8K2.u3492 (nat_lit 8076454) (nat_lit 3710476063) (nat_lit 0) D2M8K2.u3495 from rfl, allE_node, arows3492, irow3496, arows3495]
  all_goals rfl

theorem atot3496 : totK PD2M8K2 D2M8K2.u3496 = [0, 885150887694, 3061476286243, 2585221588613, 484054229317, 17590593026, 0, 0] := by
  rw [show D2M8K2.u3496 = KTree.node D2M8K2.u3492 (nat_lit 8076454) (nat_lit 3710476063) (nat_lit 0) D2M8K2.u3495 from rfl, totK_node, atot3492, atot3495]
  decide +kernel

theorem arows3504 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3504 = true := by
  rw [show D2M8K2.u3504 = KTree.node D2M8K2.u3500 (nat_lit 8088921) (nat_lit 1696710943) (nat_lit 0) D2M8K2.u3503 from rfl, allE_node, arows3500, irow3504, arows3503]
  all_goals rfl

theorem atot3504 : totK PD2M8K2 D2M8K2.u3504 = [797344212261, 2807397394042, 2766660896387, 837596778739, 63005002745, 0, 0, 0] := by
  rw [show D2M8K2.u3504 = KTree.node D2M8K2.u3500 (nat_lit 8088921) (nat_lit 1696710943) (nat_lit 0) D2M8K2.u3503 from rfl, totK_node, atot3500, atot3503]
  decide +kernel

theorem arows3511 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3511 = true := by
  rw [show D2M8K2.u3511 = KTree.node D2M8K2.u3507 (nat_lit 8099119) (nat_lit 2186808104) (nat_lit 0) D2M8K2.u3510 from rfl, allE_node, arows3507, irow3511, arows3510]
  all_goals rfl

theorem atot3511 : totK PD2M8K2 D2M8K2.u3511 = [840627257937, 2804389935168, 2795994193704, 763188518032, 29430033303, 0, 0, 0] := by
  rw [show D2M8K2.u3511 = KTree.node D2M8K2.u3507 (nat_lit 8099119) (nat_lit 2186808104) (nat_lit 0) D2M8K2.u3510 from rfl, totK_node, atot3507, atot3510]
  decide +kernel

theorem arows3521 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3521 = true := by
  rw [show D2M8K2.u3521 = KTree.node D2M8K2.u3517 (nat_lit 8106293) (nat_lit 939592499) (nat_lit 0) D2M8K2.u3520 from rfl, allE_node, arows3517, irow3521, arows3520]
  all_goals rfl

theorem atot3521 : totK PD2M8K2 D2M8K2.u3521 = [349342976169, 2093951586913, 3259890277647, 1333715283642, 114705880940, 1239866073, 0, 0] := by
  rw [show D2M8K2.u3521 = KTree.node D2M8K2.u3517 (nat_lit 8106293) (nat_lit 939592499) (nat_lit 0) D2M8K2.u3520 from rfl, totK_node, atot3517, atot3520]
  decide +kernel

theorem arows3528 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3528 = true := by
  rw [show D2M8K2.u3528 = KTree.node D2M8K2.u3524 (nat_lit 8119104) (nat_lit 3507538042) (nat_lit 0) D2M8K2.u3527 from rfl, allE_node, arows3524, irow3528, arows3527]
  all_goals rfl

theorem atot3528 : totK PD2M8K2 D2M8K2.u3528 = [0, 1031609471208, 3232162226051, 2495581392873, 408787501338, 13105450397, 0, 0] := by
  rw [show D2M8K2.u3528 = KTree.node D2M8K2.u3524 (nat_lit 8119104) (nat_lit 3507538042) (nat_lit 0) D2M8K2.u3527 from rfl, totK_node, atot3524, atot3527]
  decide +kernel

theorem arows3536 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3536 = true := by
  rw [show D2M8K2.u3536 = KTree.node D2M8K2.u3532 (nat_lit 8126092) (nat_lit 3011862975) (nat_lit 0) D2M8K2.u3535 from rfl, allE_node, arows3532, irow3536, arows3535]
  all_goals rfl

theorem atot3536 : totK PD2M8K2 D2M8K2.u3536 = [396411393819, 1904978058531, 2951526850871, 1627254529198, 216034367812, 4720618446, 0, 0] := by
  rw [show D2M8K2.u3536 = KTree.node D2M8K2.u3532 (nat_lit 8126092) (nat_lit 3011862975) (nat_lit 0) D2M8K2.u3535 from rfl, totK_node, atot3532, atot3535]
  decide +kernel

theorem arows3543 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3543 = true := by
  rw [show D2M8K2.u3543 = KTree.node D2M8K2.u3539 (nat_lit 8134804) (nat_lit 2702185241) (nat_lit 0) D2M8K2.u3542 from rfl, allE_node, arows3539, irow3543, arows3542]
  all_goals rfl

theorem atot3543 : totK PD2M8K2 D2M8K2.u3543 = [843861562048, 2865123585528, 2755984676626, 751321773736, 38723715410, 0, 0, 0] := by
  rw [show D2M8K2.u3543 = KTree.node D2M8K2.u3539 (nat_lit 8134804) (nat_lit 2702185241) (nat_lit 0) D2M8K2.u3542 from rfl, totK_node, atot3539, atot3542]
  decide +kernel

theorem arows3552 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3552 = true := by
  rw [show D2M8K2.u3552 = KTree.node D2M8K2.u3548 (nat_lit 8141018) (nat_lit 4081935574) (nat_lit 0) D2M8K2.u3551 from rfl, allE_node, arows3548, irow3552, arows3551]
  all_goals rfl

theorem atot3552 : totK PD2M8K2 D2M8K2.u3552 = [862019888459, 2912292229003, 2738531706990, 639222504356, 26232597979, 0, 0, 0] := by
  rw [show D2M8K2.u3552 = KTree.node D2M8K2.u3548 (nat_lit 8141018) (nat_lit 4081935574) (nat_lit 0) D2M8K2.u3551 from rfl, totK_node, atot3548, atot3551]
  decide +kernel

theorem arows3559 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3559 = true := by
  rw [show D2M8K2.u3559 = KTree.node D2M8K2.u3555 (nat_lit 8151682) (nat_lit 3142955423) (nat_lit 0) D2M8K2.u3558 from rfl, allE_node, arows3555, irow3559, arows3558]
  all_goals rfl

theorem atot3559 : totK PD2M8K2 D2M8K2.u3559 = [0, 1403592663993, 3636719093984, 1929777387750, 172361813539, 1138244013, 0, 0] := by
  rw [show D2M8K2.u3559 = KTree.node D2M8K2.u3555 (nat_lit 8151682) (nat_lit 3142955423) (nat_lit 0) D2M8K2.u3558 from rfl, totK_node, atot3555, atot3558]
  decide +kernel

theorem arows3567 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3567 = true := by
  rw [show D2M8K2.u3567 = KTree.node D2M8K2.u3563 (nat_lit 8163450) (nat_lit 3891890497) (nat_lit 0) D2M8K2.u3566 from rfl, allE_node, arows3563, irow3567, arows3566]
  all_goals rfl

theorem atot3567 : totK PD2M8K2 D2M8K2.u3567 = [0, 1200226567980, 3469643550004, 2185429546498, 269562270519, 4977114383, 0, 0] := by
  rw [show D2M8K2.u3567 = KTree.node D2M8K2.u3563 (nat_lit 8163450) (nat_lit 3891890497) (nat_lit 0) D2M8K2.u3566 from rfl, totK_node, atot3563, atot3566]
  decide +kernel

theorem arows3574 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3574 = true := by
  rw [show D2M8K2.u3574 = KTree.node D2M8K2.u3570 (nat_lit 8218974) (nat_lit 2094575160) (nat_lit 0) D2M8K2.u3573 from rfl, allE_node, arows3570, irow3574, arows3573]
  all_goals rfl

theorem atot3574 : totK PD2M8K2 D2M8K2.u3574 = [0, 861613202171, 3039449934708, 2738028934536, 478452107904, 14352600228, 0, 0] := by
  rw [show D2M8K2.u3574 = KTree.node D2M8K2.u3570 (nat_lit 8218974) (nat_lit 2094575160) (nat_lit 0) D2M8K2.u3573 from rfl, totK_node, atot3570, atot3573]
  decide +kernel

theorem arows3587 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3587 = true := by
  rw [show D2M8K2.u3587 = KTree.node D2M8K2.u3583 (nat_lit 8225926) (nat_lit 3545487497) (nat_lit 0) D2M8K2.u3586 from rfl, allE_node, arows3583, irow3587, arows3586]
  all_goals rfl

theorem atot3587 : totK PD2M8K2 D2M8K2.u3587 = [0, 613905356233, 2700747422464, 3057338490713, 711573726277, 27717580766, 0, 0] := by
  rw [show D2M8K2.u3587 = KTree.node D2M8K2.u3583 (nat_lit 8225926) (nat_lit 3545487497) (nat_lit 0) D2M8K2.u3586 from rfl, totK_node, atot3583, atot3586]
  decide +kernel

theorem arows3594 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3594 = true := by
  rw [show D2M8K2.u3594 = KTree.node D2M8K2.u3590 (nat_lit 8240671) (nat_lit 1730745878) (nat_lit 0) D2M8K2.u3593 from rfl, allE_node, arows3590, irow3594, arows3593]
  all_goals rfl

theorem atot3594 : totK PD2M8K2 D2M8K2.u3594 = [0, 0, 1365073316163, 3669583999506, 1783412374092, 148733147936, 1209030869, 0] := by
  rw [show D2M8K2.u3594 = KTree.node D2M8K2.u3590 (nat_lit 8240671) (nat_lit 1730745878) (nat_lit 0) D2M8K2.u3593 from rfl, totK_node, atot3590, atot3593]
  decide +kernel

theorem arows3602 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3602 = true := by
  rw [show D2M8K2.u3602 = KTree.node D2M8K2.u3598 (nat_lit 8259298) (nat_lit 3471276410) (nat_lit 0) D2M8K2.u3601 from rfl, allE_node, arows3598, irow3602, arows3601]
  all_goals rfl

theorem atot3602 : totK PD2M8K2 D2M8K2.u3602 = [0, 857993052171, 2892275101146, 2760098242957, 767585661937, 45223926722, 0, 0] := by
  rw [show D2M8K2.u3602 = KTree.node D2M8K2.u3598 (nat_lit 8259298) (nat_lit 3471276410) (nat_lit 0) D2M8K2.u3601 from rfl, totK_node, atot3598, atot3601]
  decide +kernel

theorem arows3609 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3609 = true := by
  rw [show D2M8K2.u3609 = KTree.node D2M8K2.u3605 (nat_lit 8266155) (nat_lit 2362344393) (nat_lit 0) D2M8K2.u3608 from rfl, allE_node, arows3605, irow3609, arows3608]
  all_goals rfl

theorem atot3609 : totK PD2M8K2 D2M8K2.u3609 = [0, 837121645225, 3054010307254, 2816105368165, 526089058594, 17914571324, 0, 0] := by
  rw [show D2M8K2.u3609 = KTree.node D2M8K2.u3605 (nat_lit 8266155) (nat_lit 2362344393) (nat_lit 0) D2M8K2.u3608 from rfl, totK_node, atot3605, atot3608]
  decide +kernel

theorem arows3618 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3618 = true := by
  rw [show D2M8K2.u3618 = KTree.node D2M8K2.u3614 (nat_lit 8294401) (nat_lit 1575612183) (nat_lit 0) D2M8K2.u3617 from rfl, allE_node, arows3614, irow3618, arows3617]
  all_goals rfl

theorem atot3618 : totK PD2M8K2 D2M8K2.u3618 = [0, 850964170488, 2937228063440, 2851057002829, 583000303747, 14921425640, 0, 0] := by
  rw [show D2M8K2.u3618 = KTree.node D2M8K2.u3614 (nat_lit 8294401) (nat_lit 1575612183) (nat_lit 0) D2M8K2.u3617 from rfl, totK_node, atot3614, atot3617]
  decide +kernel

theorem arows3625 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3625 = true := by
  rw [show D2M8K2.u3625 = KTree.node D2M8K2.u3621 (nat_lit 8301634) (nat_lit 4035474104) (nat_lit 0) D2M8K2.u3624 from rfl, allE_node, arows3621, irow3625, arows3624]
  all_goals rfl

theorem atot3625 : totK PD2M8K2 D2M8K2.u3625 = [0, 800319991749, 2867097181205, 2870467969659, 704277148885, 28063716506, 0, 0] := by
  rw [show D2M8K2.u3625 = KTree.node D2M8K2.u3621 (nat_lit 8301634) (nat_lit 4035474104) (nat_lit 0) D2M8K2.u3624 from rfl, totK_node, atot3621, atot3624]
  decide +kernel

theorem arows3633 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3633 = true := by
  rw [show D2M8K2.u3633 = KTree.node D2M8K2.u3629 (nat_lit 8311876) (nat_lit 3948762570) (nat_lit 0) D2M8K2.u3632 from rfl, allE_node, arows3629, irow3633, arows3632]
  all_goals rfl

theorem atot3633 : totK PD2M8K2 D2M8K2.u3633 = [0, 907487058630, 3099496198191, 2710563246304, 475879391233, 9861410126, 0, 0] := by
  rw [show D2M8K2.u3633 = KTree.node D2M8K2.u3629 (nat_lit 8311876) (nat_lit 3948762570) (nat_lit 0) D2M8K2.u3632 from rfl, totK_node, atot3629, atot3632]
  decide +kernel

theorem arows3640 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3640 = true := by
  rw [show D2M8K2.u3640 = KTree.node D2M8K2.u3636 (nat_lit 8340672) (nat_lit 2527987828) (nat_lit 0) D2M8K2.u3639 from rfl, allE_node, arows3636, irow3640, arows3639]
  all_goals rfl

theorem atot3640 : totK PD2M8K2 D2M8K2.u3640 = [0, 872236454770, 3035965452320, 2808391549832, 568569091319, 16376849850, 0, 0] := by
  rw [show D2M8K2.u3640 = KTree.node D2M8K2.u3636 (nat_lit 8340672) (nat_lit 2527987828) (nat_lit 0) D2M8K2.u3639 from rfl, totK_node, atot3636, atot3639]
  decide +kernel

theorem arows3650 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3650 = true := by
  rw [show D2M8K2.u3650 = KTree.node D2M8K2.u3646 (nat_lit 8350474) (nat_lit 2860331123) (nat_lit 0) D2M8K2.u3649 from rfl, allE_node, arows3646, irow3650, arows3649]
  all_goals rfl

theorem atot3650 : totK PD2M8K2 D2M8K2.u3650 = [0, 810414826153, 2936601391897, 2847818978944, 582465785828, 18151190877, 0, 0] := by
  rw [show D2M8K2.u3650 = KTree.node D2M8K2.u3646 (nat_lit 8350474) (nat_lit 2860331123) (nat_lit 0) D2M8K2.u3649 from rfl, totK_node, atot3646, atot3649]
  decide +kernel

theorem arows3657 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3657 = true := by
  rw [show D2M8K2.u3657 = KTree.node D2M8K2.u3653 (nat_lit 8379082) (nat_lit 3871581885) (nat_lit 0) D2M8K2.u3656 from rfl, allE_node, arows3653, irow3657, arows3656]
  all_goals rfl

theorem atot3657 : totK PD2M8K2 D2M8K2.u3657 = [0, 891370380895, 3127137113204, 2730529236120, 428382483437, 6261201934, 0, 0] := by
  rw [show D2M8K2.u3657 = KTree.node D2M8K2.u3653 (nat_lit 8379082) (nat_lit 3871581885) (nat_lit 0) D2M8K2.u3656 from rfl, totK_node, atot3653, atot3656]
  decide +kernel

theorem arows3665 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3665 = true := by
  rw [show D2M8K2.u3665 = KTree.node D2M8K2.u3661 (nat_lit 8385899) (nat_lit 2718359376) (nat_lit 0) D2M8K2.u3664 from rfl, allE_node, arows3661, irow3665, arows3664]
  all_goals rfl

theorem atot3665 : totK PD2M8K2 D2M8K2.u3665 = [0, 833442042101, 2815566936299, 2754914994453, 718525664861, 36620389566, 0, 0] := by
  rw [show D2M8K2.u3665 = KTree.node D2M8K2.u3661 (nat_lit 8385899) (nat_lit 2718359376) (nat_lit 0) D2M8K2.u3664 from rfl, totK_node, atot3661, atot3664]
  decide +kernel

theorem arows3672 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3672 = true := by
  rw [show D2M8K2.u3672 = KTree.node D2M8K2.u3668 (nat_lit 8392363) (nat_lit 1802348857) (nat_lit 0) D2M8K2.u3671 from rfl, allE_node, arows3668, irow3672, arows3671]
  all_goals rfl

theorem atot3672 : totK PD2M8K2 D2M8K2.u3672 = [0, 443584338047, 2432183040880, 3311673584009, 892022611095, 40041202543, 0, 0] := by
  rw [show D2M8K2.u3672 = KTree.node D2M8K2.u3668 (nat_lit 8392363) (nat_lit 1802348857) (nat_lit 0) D2M8K2.u3671 from rfl, totK_node, atot3668, atot3671]
  decide +kernel

theorem arows3681 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3681 = true := by
  rw [show D2M8K2.u3681 = KTree.node D2M8K2.u3677 (nat_lit 8405451) (nat_lit 3623359143) (nat_lit 0) D2M8K2.u3680 from rfl, allE_node, arows3677, irow3681, arows3680]
  all_goals rfl

theorem atot3681 : totK PD2M8K2 D2M8K2.u3681 = [0, 0, 1379852229181, 3629302006752, 1850324568473, 162615668670, 1138244013, 0] := by
  rw [show D2M8K2.u3681 = KTree.node D2M8K2.u3677 (nat_lit 8405451) (nat_lit 3623359143) (nat_lit 0) D2M8K2.u3680 from rfl, totK_node, atot3677, atot3680]
  decide +kernel

theorem arows3688 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3688 = true := by
  rw [show D2M8K2.u3688 = KTree.node D2M8K2.u3684 (nat_lit 8460989) (nat_lit 2317401966) (nat_lit 0) D2M8K2.u3687 from rfl, allE_node, arows3684, irow3688, arows3687]
  all_goals rfl

theorem atot3688 : totK PD2M8K2 D2M8K2.u3688 = [608919996772, 1926999465553, 1782402307106, 1426821726560, 1165407591884, 223026865017, 4977114383, 0] := by
  rw [show D2M8K2.u3688 = KTree.node D2M8K2.u3684 (nat_lit 8460989) (nat_lit 2317401966) (nat_lit 0) D2M8K2.u3687 from rfl, totK_node, atot3684, atot3687]
  decide +kernel

theorem arows3696 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3696 = true := by
  rw [show D2M8K2.u3696 = KTree.node D2M8K2.u3692 (nat_lit 8471561) (nat_lit 899117699) (nat_lit 0) D2M8K2.u3695 from rfl, allE_node, arows3692, irow3696, arows3695]
  all_goals rfl

theorem atot3696 : totK PD2M8K2 D2M8K2.u3696 = [801037989750, 2865756206714, 2822688381588, 671314458658, 26300412495, 0, 0, 0] := by
  rw [show D2M8K2.u3696 = KTree.node D2M8K2.u3692 (nat_lit 8471561) (nat_lit 899117699) (nat_lit 0) D2M8K2.u3695 from rfl, totK_node, atot3692, atot3695]
  decide +kernel

theorem arows3703 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3703 = true := by
  rw [show D2M8K2.u3703 = KTree.node D2M8K2.u3699 (nat_lit 8481618) (nat_lit 2758532077) (nat_lit 0) D2M8K2.u3702 from rfl, allE_node, arows3699, irow3703, arows3702]
  all_goals rfl

theorem atot3703 : totK PD2M8K2 D2M8K2.u3703 = [237319555436, 1650573661941, 3242680278597, 1750045303931, 191981079460, 1369150432, 0, 0] := by
  rw [show D2M8K2.u3703 = KTree.node D2M8K2.u3699 (nat_lit 8481618) (nat_lit 2758532077) (nat_lit 0) D2M8K2.u3702 from rfl, totK_node, atot3699, atot3702]
  decide +kernel

theorem arows3714 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3714 = true := by
  rw [show D2M8K2.u3714 = KTree.node D2M8K2.u3710 (nat_lit 8498637) (nat_lit 1248378190) (nat_lit 0) D2M8K2.u3713 from rfl, allE_node, arows3710, irow3714, arows3713]
  all_goals rfl

theorem atot3714 : totK PD2M8K2 D2M8K2.u3714 = [433306685740, 2098505983512, 3261251025775, 1385560905229, 77409238429, 0, 0, 0] := by
  rw [show D2M8K2.u3714 = KTree.node D2M8K2.u3710 (nat_lit 8498637) (nat_lit 1248378190) (nat_lit 0) D2M8K2.u3713 from rfl, totK_node, atot3710, atot3713]
  decide +kernel

theorem arows3721 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3721 = true := by
  rw [show D2M8K2.u3721 = KTree.node D2M8K2.u3717 (nat_lit 8509509) (nat_lit 1470583704) (nat_lit 0) D2M8K2.u3720 from rfl, allE_node, arows3717, irow3721, arows3720]
  all_goals rfl

theorem atot3721 : totK PD2M8K2 D2M8K2.u3721 = [671334053109, 2638921829398, 2997475647258, 924143073106, 50509530253, 0, 0, 0] := by
  rw [show D2M8K2.u3721 = KTree.node D2M8K2.u3717 (nat_lit 8509509) (nat_lit 1470583704) (nat_lit 0) D2M8K2.u3720 from rfl, totK_node, atot3717, atot3720]
  decide +kernel

theorem arows3729 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3729 = true := by
  rw [show D2M8K2.u3729 = KTree.node D2M8K2.u3725 (nat_lit 8516556) (nat_lit 2959468138) (nat_lit 0) D2M8K2.u3728 from rfl, allE_node, arows3725, irow3729, arows3728]
  all_goals rfl

theorem atot3729 : totK PD2M8K2 D2M8K2.u3729 = [922333018483, 3075063962053, 2753663690470, 540448792666, 16865863894, 0, 0, 0] := by
  rw [show D2M8K2.u3729 = KTree.node D2M8K2.u3725 (nat_lit 8516556) (nat_lit 2959468138) (nat_lit 0) D2M8K2.u3728 from rfl, totK_node, atot3725, atot3728]
  decide +kernel

theorem arows3736 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3736 = true := by
  rw [show D2M8K2.u3736 = KTree.node D2M8K2.u3732 (nat_lit 8527155) (nat_lit 3658164141) (nat_lit 0) D2M8K2.u3735 from rfl, allE_node, arows3732, irow3736, arows3735]
  all_goals rfl

theorem atot3736 : totK PD2M8K2 D2M8K2.u3736 = [19691318959, 1164478298554, 3077319071705, 2337389973733, 618479009462, 36921873854, 0, 0] := by
  rw [show D2M8K2.u3736 = KTree.node D2M8K2.u3732 (nat_lit 8527155) (nat_lit 3658164141) (nat_lit 0) D2M8K2.u3735 from rfl, totK_node, atot3732, atot3735]
  decide +kernel

theorem arows3745 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3745 = true := by
  rw [show D2M8K2.u3745 = KTree.node D2M8K2.u3741 (nat_lit 8533800) (nat_lit 3529314369) (nat_lit 0) D2M8K2.u3744 from rfl, allE_node, arows3741, irow3745, arows3744]
  all_goals rfl

theorem atot3745 : totK PD2M8K2 D2M8K2.u3745 = [0, 899637670967, 3075257094987, 2757698287251, 505380918089, 10378741320, 0, 0] := by
  rw [show D2M8K2.u3745 = KTree.node D2M8K2.u3741 (nat_lit 8533800) (nat_lit 3529314369) (nat_lit 0) D2M8K2.u3744 from rfl, totK_node, atot3741, atot3744]
  decide +kernel

theorem arows3752 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3752 = true := by
  rw [show D2M8K2.u3752 = KTree.node D2M8K2.u3748 (nat_lit 8541308) (nat_lit 2614928932) (nat_lit 0) D2M8K2.u3751 from rfl, allE_node, arows3748, irow3752, arows3751]
  all_goals rfl

theorem atot3752 : totK PD2M8K2 D2M8K2.u3752 = [378822834728, 1478356949734, 2642289013518, 2266483393021, 465665244922, 10717512769, 0, 0] := by
  rw [show D2M8K2.u3752 = KTree.node D2M8K2.u3748 (nat_lit 8541308) (nat_lit 2614928932) (nat_lit 0) D2M8K2.u3751 from rfl, totK_node, atot3748, atot3751]
  decide +kernel

theorem arows3760 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3760 = true := by
  rw [show D2M8K2.u3760 = KTree.node D2M8K2.u3756 (nat_lit 8548821) (nat_lit 1652169926) (nat_lit 0) D2M8K2.u3759 from rfl, allE_node, arows3756, irow3760, arows3759]
  all_goals rfl

theorem atot3760 : totK PD2M8K2 D2M8K2.u3760 = [787265908857, 2825469483019, 2860277339079, 777625086111, 38930019324, 0, 0, 0] := by
  rw [show D2M8K2.u3760 = KTree.node D2M8K2.u3756 (nat_lit 8548821) (nat_lit 1652169926) (nat_lit 0) D2M8K2.u3759 from rfl, totK_node, atot3756, atot3759]
  decide +kernel

theorem arows3767 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3767 = true := by
  rw [show D2M8K2.u3767 = KTree.node D2M8K2.u3763 (nat_lit 8558383) (nat_lit 1982763235) (nat_lit 0) D2M8K2.u3766 from rfl, allE_node, arows3763, irow3767, arows3766]
  all_goals rfl

theorem atot3767 : totK PD2M8K2 D2M8K2.u3767 = [825163310470, 2972715652002, 2846055128530, 575794408410, 18030242193, 0, 0, 0] := by
  rw [show D2M8K2.u3767 = KTree.node D2M8K2.u3763 (nat_lit 8558383) (nat_lit 1982763235) (nat_lit 0) D2M8K2.u3766 from rfl, totK_node, atot3763, atot3766]
  decide +kernel

theorem arows3777 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3777 = true := by
  rw [show D2M8K2.u3777 = KTree.node D2M8K2.u3773 (nat_lit 8565771) (nat_lit 476998184) (nat_lit 0) D2M8K2.u3776 from rfl, allE_node, arows3773, irow3777, arows3776]
  all_goals rfl

theorem atot3777 : totK PD2M8K2 D2M8K2.u3777 = [0, 1297315467729, 3591689791198, 2070735538059, 188841920428, 1206465782, 0, 0] := by
  rw [show D2M8K2.u3777 = KTree.node D2M8K2.u3773 (nat_lit 8565771) (nat_lit 476998184) (nat_lit 0) D2M8K2.u3776 from rfl, totK_node, atot3773, atot3776]
  decide +kernel

theorem arows3784 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3784 = true := by
  rw [show D2M8K2.u3784 = KTree.node D2M8K2.u3780 (nat_lit 8578148) (nat_lit 3349800251) (nat_lit 0) D2M8K2.u3783 from rfl, allE_node, arows3780, irow3784, arows3783]
  all_goals rfl

theorem atot3784 : totK PD2M8K2 D2M8K2.u3784 = [0, 889039605979, 3074017847674, 2624928462360, 496669269709, 17590593026, 0, 0] := by
  rw [show D2M8K2.u3784 = KTree.node D2M8K2.u3780 (nat_lit 8578148) (nat_lit 3349800251) (nat_lit 0) D2M8K2.u3783 from rfl, totK_node, atot3780, atot3783]
  decide +kernel

theorem arows3792 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3792 = true := by
  rw [show D2M8K2.u3792 = KTree.node D2M8K2.u3788 (nat_lit 8587701) (nat_lit 1740192550) (nat_lit 0) D2M8K2.u3791 from rfl, allE_node, arows3788, irow3792, arows3791]
  all_goals rfl

theorem atot3792 : totK PD2M8K2 D2M8K2.u3792 = [799704190451, 2821984890078, 2802579184898, 801954883186, 48195274583, 0, 0, 0] := by
  rw [show D2M8K2.u3792 = KTree.node D2M8K2.u3788 (nat_lit 8587701) (nat_lit 1740192550) (nat_lit 0) D2M8K2.u3791 from rfl, totK_node, atot3788, atot3791]
  decide +kernel

theorem arows3799 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3799 = true := by
  rw [show D2M8K2.u3799 = KTree.node D2M8K2.u3795 (nat_lit 8597672) (nat_lit 3554683412) (nat_lit 0) D2M8K2.u3798 from rfl, allE_node, arows3795, irow3799, arows3798]
  all_goals rfl

theorem atot3799 : totK PD2M8K2 D2M8K2.u3799 = [765668592719, 2867369203742, 2918107831358, 681636706034, 22556487037, 0, 0, 0] := by
  rw [show D2M8K2.u3799 = KTree.node D2M8K2.u3795 (nat_lit 8597672) (nat_lit 3554683412) (nat_lit 0) D2M8K2.u3798 from rfl, totK_node, atot3795, atot3798]
  decide +kernel

theorem arows3808 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3808 = true := by
  rw [show D2M8K2.u3808 = KTree.node D2M8K2.u3804 (nat_lit 8604726) (nat_lit 3700954370) (nat_lit 0) D2M8K2.u3807 from rfl, allE_node, arows3804, irow3808, arows3807]
  all_goals rfl

theorem atot3808 : totK PD2M8K2 D2M8K2.u3808 = [426423859968, 1938748346040, 3066873378487, 1560876298484, 147012492827, 1239866073, 0, 0] := by
  rw [show D2M8K2.u3808 = KTree.node D2M8K2.u3804 (nat_lit 8604726) (nat_lit 3700954370) (nat_lit 0) D2M8K2.u3807 from rfl, totK_node, atot3804, atot3807]
  decide +kernel

theorem arows3815 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3815 = true := by
  rw [show D2M8K2.u3815 = KTree.node D2M8K2.u3811 (nat_lit 8617112) (nat_lit 3606797827) (nat_lit 0) D2M8K2.u3814 from rfl, allE_node, arows3811, irow3815, arows3814]
  all_goals rfl

theorem atot3815 : totK PD2M8K2 D2M8K2.u3815 = [0, 1157094461227, 3316776532216, 2345372287864, 384761013388, 13105450397, 0, 0] := by
  rw [show D2M8K2.u3815 = KTree.node D2M8K2.u3811 (nat_lit 8617112) (nat_lit 3606797827) (nat_lit 0) D2M8K2.u3814 from rfl, totK_node, atot3811, atot3814]
  decide +kernel

theorem arows3823 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3823 = true := by
  rw [show D2M8K2.u3823 = KTree.node D2M8K2.u3819 (nat_lit 8667758) (nat_lit 1347969689) (nat_lit 0) D2M8K2.u3822 from rfl, allE_node, arows3819, irow3823, arows3822]
  all_goals rfl

theorem atot3823 : totK PD2M8K2 D2M8K2.u3823 = [521196355946, 2111942826159, 2883745536008, 1441090767510, 195851662626, 4720618446, 0, 0] := by
  rw [show D2M8K2.u3823 = KTree.node D2M8K2.u3819 (nat_lit 8667758) (nat_lit 1347969689) (nat_lit 0) D2M8K2.u3822 from rfl, totK_node, atot3819, atot3822]
  decide +kernel

theorem arows3830 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3830 = true := by
  rw [show D2M8K2.u3830 = KTree.node D2M8K2.u3826 (nat_lit 8674536) (nat_lit 2880418021) (nat_lit 0) D2M8K2.u3829 from rfl, allE_node, arows3826, irow3830, arows3829]
  all_goals rfl

theorem atot3830 : totK PD2M8K2 D2M8K2.u3830 = [720252416698, 2690009217773, 2877607846964, 883352086996, 50432975716, 0, 0, 0] := by
  rw [show D2M8K2.u3830 = KTree.node D2M8K2.u3826 (nat_lit 8674536) (nat_lit 2880418021) (nat_lit 0) D2M8K2.u3829 from rfl, totK_node, atot3826, atot3829]
  decide +kernel

theorem arows3842 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3842 = true := by
  rw [show D2M8K2.u3842 = KTree.node D2M8K2.u3838 (nat_lit 8681074) (nat_lit 2720325618) (nat_lit 0) D2M8K2.u3841 from rfl, allE_node, arows3838, irow3842, arows3841]
  all_goals rfl

theorem atot3842 : totK PD2M8K2 D2M8K2.u3842 = [867070346516, 2979760403071, 2788741852011, 601344455051, 18060071081, 0, 0, 0] := by
  rw [show D2M8K2.u3842 = KTree.node D2M8K2.u3838 (nat_lit 8681074) (nat_lit 2720325618) (nat_lit 0) D2M8K2.u3841 from rfl, totK_node, atot3838, atot3841]
  decide +kernel

theorem arows3849 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3849 = true := by
  rw [show D2M8K2.u3849 = KTree.node D2M8K2.u3845 (nat_lit 8691115) (nat_lit 1556393835) (nat_lit 0) D2M8K2.u3848 from rfl, allE_node, arows3845, irow3849, arows3848]
  all_goals rfl

theorem atot3849 : totK PD2M8K2 D2M8K2.u3849 = [0, 1248352955317, 3493979582107, 2225918783756, 219373308886, 1310285577, 0, 0] := by
  rw [show D2M8K2.u3849 = KTree.node D2M8K2.u3845 (nat_lit 8691115) (nat_lit 1556393835) (nat_lit 0) D2M8K2.u3848 from rfl, totK_node, atot3845, atot3848]
  decide +kernel

theorem arows3857 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3857 = true := by
  rw [show D2M8K2.u3857 = KTree.node D2M8K2.u3853 (nat_lit 8699862) (nat_lit 3867271593) (nat_lit 0) D2M8K2.u3856 from rfl, allE_node, arows3853, irow3857, arows3856]
  all_goals rfl

theorem atot3857 : totK PD2M8K2 D2M8K2.u3857 = [0, 891518959935, 3128037069880, 2659882613728, 432617138929, 9811245038, 0, 0] := by
  rw [show D2M8K2.u3857 = KTree.node D2M8K2.u3853 (nat_lit 8699862) (nat_lit 3867271593) (nat_lit 0) D2M8K2.u3856 from rfl, totK_node, atot3853, atot3856]
  decide +kernel

theorem arows3864 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3864 = true := by
  rw [show D2M8K2.u3864 = KTree.node D2M8K2.u3860 (nat_lit 8710085) (nat_lit 1792536005) (nat_lit 0) D2M8K2.u3863 from rfl, allE_node, arows3860, irow3864, arows3863]
  all_goals rfl

theorem atot3864 : totK PD2M8K2 D2M8K2.u3864 = [0, 801818420500, 2943812912689, 2797705201864, 590961605393, 23120318498, 0, 0] := by
  rw [show D2M8K2.u3864 = KTree.node D2M8K2.u3860 (nat_lit 8710085) (nat_lit 1792536005) (nat_lit 0) D2M8K2.u3863 from rfl, totK_node, atot3860, atot3863]
  decide +kernel

theorem arows3873 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3873 = true := by
  rw [show D2M8K2.u3873 = KTree.node D2M8K2.u3869 (nat_lit 8720790) (nat_lit 3581696511) (nat_lit 0) D2M8K2.u3872 from rfl, allE_node, arows3869, irow3873, arows3872]
  all_goals rfl

theorem atot3873 : totK PD2M8K2 D2M8K2.u3873 = [0, 882861427581, 3040785790102, 2746640325316, 505884422656, 10401747658, 0, 0] := by
  rw [show D2M8K2.u3873 = KTree.node D2M8K2.u3869 (nat_lit 8720790) (nat_lit 3581696511) (nat_lit 0) D2M8K2.u3872 from rfl, totK_node, atot3869, atot3872]
  decide +kernel

theorem arows3880 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3880 = true := by
  rw [show D2M8K2.u3880 = KTree.node D2M8K2.u3876 (nat_lit 8730985) (nat_lit 1446174803) (nat_lit 0) D2M8K2.u3879 from rfl, allE_node, arows3876, irow3880, arows3879]
  all_goals rfl

theorem atot3880 : totK PD2M8K2 D2M8K2.u3880 = [0, 92937627352, 1478062553079, 3505574924440, 1785857874595, 155940123469, 1369150432, 0] := by
  rw [show D2M8K2.u3880 = KTree.node D2M8K2.u3876 (nat_lit 8730985) (nat_lit 1446174803) (nat_lit 0) D2M8K2.u3879 from rfl, totK_node, atot3876, atot3879]
  decide +kernel

theorem arows3888 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3888 = true := by
  rw [show D2M8K2.u3888 = KTree.node D2M8K2.u3884 (nat_lit 8748153) (nat_lit 1280807303) (nat_lit 0) D2M8K2.u3887 from rfl, allE_node, arows3884, irow3888, arows3887]
  all_goals rfl

theorem atot3888 : totK PD2M8K2 D2M8K2.u3888 = [0, 445310450810, 2182108292578, 3249133902318, 1280399795781, 76400630499, 0, 0] := by
  rw [show D2M8K2.u3888 = KTree.node D2M8K2.u3884 (nat_lit 8748153) (nat_lit 1280807303) (nat_lit 0) D2M8K2.u3887 from rfl, totK_node, atot3884, atot3887]
  decide +kernel

theorem arows3895 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3895 = true := by
  rw [show D2M8K2.u3895 = KTree.node D2M8K2.u3891 (nat_lit 8759362) (nat_lit 4064866416) (nat_lit 0) D2M8K2.u3894 from rfl, allE_node, arows3891, irow3895, arows3894]
  all_goals rfl

theorem atot3895 : totK PD2M8K2 D2M8K2.u3895 = [0, 830161172305, 2851245826319, 2805888961519, 730768736767, 25167970012, 0, 0] := by
  rw [show D2M8K2.u3895 = KTree.node D2M8K2.u3891 (nat_lit 8759362) (nat_lit 4064866416) (nat_lit 0) D2M8K2.u3894 from rfl, totK_node, atot3891, atot3894]
  decide +kernel

theorem arows3905 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3905 = true := by
  rw [show D2M8K2.u3905 = KTree.node D2M8K2.u3901 (nat_lit 8767008) (nat_lit 2853383548) (nat_lit 0) D2M8K2.u3904 from rfl, allE_node, arows3901, irow3905, arows3904]
  all_goals rfl

theorem atot3905 : totK PD2M8K2 D2M8K2.u3905 = [0, 774418830667, 2940849721707, 2957267416441, 613358635264, 11857568180, 0, 0] := by
  rw [show D2M8K2.u3905 = KTree.node D2M8K2.u3901 (nat_lit 8767008) (nat_lit 2853383548) (nat_lit 0) D2M8K2.u3904 from rfl, totK_node, atot3901, atot3904]
  decide +kernel

theorem arows3912 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3912 = true := by
  rw [show D2M8K2.u3912 = KTree.node D2M8K2.u3908 (nat_lit 8794748) (nat_lit 2640017717) (nat_lit 0) D2M8K2.u3911 from rfl, allE_node, arows3908, irow3912, arows3911]
  all_goals rfl

theorem atot3912 : totK PD2M8K2 D2M8K2.u3912 = [0, 799332780726, 2833108090603, 2782091360396, 755504572218, 45380168537, 0, 0] := by
  rw [show D2M8K2.u3912 = KTree.node D2M8K2.u3908 (nat_lit 8794748) (nat_lit 2640017717) (nat_lit 0) D2M8K2.u3911 from rfl, totK_node, atot3908, atot3911]
  decide +kernel

theorem arows3920 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3920 = true := by
  rw [show D2M8K2.u3920 = KTree.node D2M8K2.u3916 (nat_lit 8801049) (nat_lit 1804613175) (nat_lit 0) D2M8K2.u3919 from rfl, allE_node, arows3916, irow3920, arows3919]
  all_goals rfl

theorem atot3920 : totK PD2M8K2 D2M8K2.u3920 = [0, 764868124390, 2827490561112, 2898169868292, 688924553357, 23548286881, 0, 0] := by
  rw [show D2M8K2.u3920 = KTree.node D2M8K2.u3916 (nat_lit 8801049) (nat_lit 1804613175) (nat_lit 0) D2M8K2.u3919 from rfl, totK_node, atot3916, atot3919]
  decide +kernel

theorem arows3927 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3927 = true := by
  rw [show D2M8K2.u3927 = KTree.node D2M8K2.u3923 (nat_lit 8811977) (nat_lit 1206925856) (nat_lit 0) D2M8K2.u3926 from rfl, allE_node, arows3923, irow3927, arows3926]
  all_goals rfl

theorem atot3927 : totK PD2M8K2 D2M8K2.u3927 = [0, 426024804024, 1978503365814, 3107767296612, 1446394205728, 115346592053, 1166720416, 0] := by
  rw [show D2M8K2.u3927 = KTree.node D2M8K2.u3923 (nat_lit 8811977) (nat_lit 1206925856) (nat_lit 0) D2M8K2.u3926 from rfl, totK_node, atot3923, atot3926]
  decide +kernel

theorem arows3936 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3936 = true := by
  rw [show D2M8K2.u3936 = KTree.node D2M8K2.u3932 (nat_lit 8821419) (nat_lit 3373153974) (nat_lit 0) D2M8K2.u3935 from rfl, allE_node, arows3932, irow3936, arows3935]
  all_goals rfl

theorem atot3936 : totK PD2M8K2 D2M8K2.u3936 = [0, 0, 1368712970015, 3504525432676, 1972029361075, 237206124537, 5134755853, 0] := by
  rw [show D2M8K2.u3936 = KTree.node D2M8K2.u3932 (nat_lit 8821419) (nat_lit 3373153974) (nat_lit 0) D2M8K2.u3935 from rfl, totK_node, atot3932, atot3935]
  decide +kernel

theorem arows3943 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3943 = true := by
  rw [show D2M8K2.u3943 = KTree.node D2M8K2.u3939 (nat_lit 8836171) (nat_lit 1696342550) (nat_lit 0) D2M8K2.u3942 from rfl, allE_node, arows3939, irow3943, arows3942]
  all_goals rfl

theorem atot3943 : totK PD2M8K2 D2M8K2.u3943 = [0, 799500920788, 2833725914698, 2792763214315, 768932804388, 45018141573, 0, 0] := by
  rw [show D2M8K2.u3943 = KTree.node D2M8K2.u3939 (nat_lit 8836171) (nat_lit 1696342550) (nat_lit 0) D2M8K2.u3942 from rfl, totK_node, atot3939, atot3942]
  decide +kernel

theorem arows3951 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3951 = true := by
  rw [show D2M8K2.u3951 = KTree.node D2M8K2.u3947 (nat_lit 8845879) (nat_lit 2214148709) (nat_lit 0) D2M8K2.u3950 from rfl, allE_node, arows3947, irow3951, arows3950]
  all_goals rfl

theorem atot3951 : totK PD2M8K2 D2M8K2.u3951 = [0, 765202710297, 2811176245912, 2892378647812, 724106348889, 26362348786, 0, 0] := by
  rw [show D2M8K2.u3951 = KTree.node D2M8K2.u3947 (nat_lit 8845879) (nat_lit 2214148709) (nat_lit 0) D2M8K2.u3950 from rfl, totK_node, atot3947, atot3950]
  decide +kernel

theorem arows3958 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3958 = true := by
  rw [show D2M8K2.u3958 = KTree.node D2M8K2.u3954 (nat_lit 8853417) (nat_lit 1663055714) (nat_lit 0) D2M8K2.u3957 from rfl, allE_node, arows3954, irow3958, arows3957]
  all_goals rfl

theorem atot3958 : totK PD2M8K2 D2M8K2.u3958 = [0, 426073805952, 2000615696710, 3121007451213, 1411934826127, 110395617750, 1200365979, 0] := by
  rw [show D2M8K2.u3958 = KTree.node D2M8K2.u3954 (nat_lit 8853417) (nat_lit 1663055714) (nat_lit 0) D2M8K2.u3957 from rfl, totK_node, atot3954, atot3957]
  decide +kernel

theorem arows3969 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3969 = true := by
  rw [show D2M8K2.u3969 = KTree.node D2M8K2.u3965 (nat_lit 8866246) (nat_lit 3374887878) (nat_lit 0) D2M8K2.u3968 from rfl, allE_node, arows3965, irow3969, arows3968]
  all_goals rfl

theorem atot3969 : totK PD2M8K2 D2M8K2.u3969 = [0, 0, 1405216965096, 3487491950272, 1981833700435, 243640500600, 5163565574, 0] := by
  rw [show D2M8K2.u3969 = KTree.node D2M8K2.u3965 (nat_lit 8866246) (nat_lit 3374887878) (nat_lit 0) D2M8K2.u3968 from rfl, totK_node, atot3965, atot3968]
  decide +kernel

theorem arows3976 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3976 = true := by
  rw [show D2M8K2.u3976 = KTree.node D2M8K2.u3972 (nat_lit 8918892) (nat_lit 3040634269) (nat_lit 0) D2M8K2.u3975 from rfl, allE_node, arows3972, irow3976, arows3975]
  all_goals rfl

theorem atot3976 : totK PD2M8K2 D2M8K2.u3976 = [0, 825969492826, 2873040012118, 2749547288920, 728438389015, 43976828047, 0, 0] := by
  rw [show D2M8K2.u3976 = KTree.node D2M8K2.u3972 (nat_lit 8918892) (nat_lit 3040634269) (nat_lit 0) D2M8K2.u3975 from rfl, totK_node, atot3972, atot3975]
  decide +kernel

theorem arows3984 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3984 = true := by
  rw [show D2M8K2.u3984 = KTree.node D2M8K2.u3980 (nat_lit 8925272) (nat_lit 3318114937) (nat_lit 0) D2M8K2.u3983 from rfl, allE_node, arows3980, irow3984, arows3983]
  all_goals rfl

theorem atot3984 : totK PD2M8K2 D2M8K2.u3984 = [0, 837929676367, 2872515716232, 2768685752244, 672771095880, 20240857102, 0, 0] := by
  rw [show D2M8K2.u3984 = KTree.node D2M8K2.u3980 (nat_lit 8925272) (nat_lit 3318114937) (nat_lit 0) D2M8K2.u3983 from rfl, totK_node, atot3980, atot3983]
  decide +kernel

theorem arows3991 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3991 = true := by
  rw [show D2M8K2.u3991 = KTree.node D2M8K2.u3987 (nat_lit 8935465) (nat_lit 1451707094) (nat_lit 0) D2M8K2.u3990 from rfl, allE_node, arows3987, irow3991, arows3990]
  all_goals rfl

theorem atot3991 : totK PD2M8K2 D2M8K2.u3991 = [0, 447505906754, 2317424705553, 3303799059418, 1029458777037, 41026424422, 0, 0] := by
  rw [show D2M8K2.u3991 = KTree.node D2M8K2.u3987 (nat_lit 8935465) (nat_lit 1451707094) (nat_lit 0) D2M8K2.u3990 from rfl, totK_node, atot3987, atot3990]
  decide +kernel

theorem arows4000 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4000 = true := by
  rw [show D2M8K2.u4000 = KTree.node D2M8K2.u3996 (nat_lit 8944283) (nat_lit 2719002186) (nat_lit 0) D2M8K2.u3999 from rfl, allE_node, arows3996, irow4000, arows3999]
  all_goals rfl

theorem atot4000 : totK PD2M8K2 D2M8K2.u4000 = [0, 0, 1003228731642, 3232506042398, 2461425379012, 339335451067, 6075545519, 0] := by
  rw [show D2M8K2.u4000 = KTree.node D2M8K2.u3996 (nat_lit 8944283) (nat_lit 2719002186) (nat_lit 0) D2M8K2.u3999 from rfl, totK_node, atot3996, atot3999]
  decide +kernel

theorem arows4007 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4007 = true := by
  rw [show D2M8K2.u4007 = KTree.node D2M8K2.u4003 (nat_lit 8955100) (nat_lit 3950157591) (nat_lit 0) D2M8K2.u4006 from rfl, allE_node, arows4003, irow4007, arows4006]
  all_goals rfl

theorem atot4007 : totK PD2M8K2 D2M8K2.u4007 = [0, 94445126902, 942451378344, 2821450166064, 2606150063251, 597213669937, 26589411484, 0] := by
  rw [show D2M8K2.u4007 = KTree.node D2M8K2.u4003 (nat_lit 8955100) (nat_lit 3950157591) (nat_lit 0) D2M8K2.u4006 from rfl, totK_node, atot4003, atot4006]
  decide +kernel

theorem arows4015 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4015 = true := by
  rw [show D2M8K2.u4015 = KTree.node D2M8K2.u4011 (nat_lit 9503770) (nat_lit 4003915680) (nat_lit 0) D2M8K2.u4014 from rfl, allE_node, arows4011, irow4015, arows4014]
  all_goals rfl

theorem atot4015 : totK PD2M8K2 D2M8K2.u4015 = [0, 778248402785, 2778056814703, 2860613974689, 845808856292, 45763587462, 0, 0] := by
  rw [show D2M8K2.u4015 = KTree.node D2M8K2.u4011 (nat_lit 9503770) (nat_lit 4003915680) (nat_lit 0) D2M8K2.u4014 from rfl, totK_node, atot4011, atot4014]
  decide +kernel

theorem arows4022 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4022 = true := by
  rw [show D2M8K2.u4022 = KTree.node D2M8K2.u4018 (nat_lit 9510378) (nat_lit 3819174699) (nat_lit 0) D2M8K2.u4021 from rfl, allE_node, arows4018, irow4022, arows4021]
  all_goals rfl

theorem atot4022 : totK PD2M8K2 D2M8K2.u4022 = [0, 843336327398, 2994810501813, 2828432920589, 570414586721, 14744183502, 0, 0] := by
  rw [show D2M8K2.u4022 = KTree.node D2M8K2.u4018 (nat_lit 9510378) (nat_lit 3819174699) (nat_lit 0) D2M8K2.u4021 from rfl, totK_node, atot4018, atot4021]
  decide +kernel

theorem arows4032 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4032 = true := by
  rw [show D2M8K2.u4032 = KTree.node D2M8K2.u4028 (nat_lit 9516994) (nat_lit 4005049729) (nat_lit 0) D2M8K2.u4031 from rfl, allE_node, arows4028, irow4032, arows4031]
  all_goals rfl

theorem atot4032 : totK PD2M8K2 D2M8K2.u4032 = [0, 425375799150, 2064795292658, 3106845642120, 1450388764180, 239288978900, 21385604922, 0] := by
  rw [show D2M8K2.u4032 = KTree.node D2M8K2.u4028 (nat_lit 9516994) (nat_lit 4005049729) (nat_lit 0) D2M8K2.u4031 from rfl, totK_node, atot4028, atot4031]
  decide +kernel

theorem arows4039 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4039 = true := by
  rw [show D2M8K2.u4039 = KTree.node D2M8K2.u4035 (nat_lit 9526445) (nat_lit 2149376973) (nat_lit 0) D2M8K2.u4038 from rfl, allE_node, arows4035, irow4039, arows4038]
  all_goals rfl

theorem atot4039 : totK PD2M8K2 D2M8K2.u4039 = [0, 0, 841886666463, 2920136436131, 2791828499690, 645434442226, 20696137567, 0] := by
  rw [show D2M8K2.u4039 = KTree.node D2M8K2.u4035 (nat_lit 9526445) (nat_lit 2149376973) (nat_lit 0) D2M8K2.u4038 from rfl, totK_node, atot4035, atot4038]
  decide +kernel

theorem arows4047 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4047 = true := by
  rw [show D2M8K2.u4047 = KTree.node D2M8K2.u4043 (nat_lit 9533703) (nat_lit 3638013176) (nat_lit 0) D2M8K2.u4046 from rfl, allE_node, arows4043, irow4047, arows4046]
  all_goals rfl

theorem atot4047 : totK PD2M8K2 D2M8K2.u4047 = [0, 0, 841874049150, 3128751318052, 2824323096653, 451217157498, 6634014755, 0] := by
  rw [show D2M8K2.u4047 = KTree.node D2M8K2.u4043 (nat_lit 9533703) (nat_lit 3638013176) (nat_lit 0) D2M8K2.u4046 from rfl, totK_node, atot4043, atot4046]
  decide +kernel

theorem arows4054 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4054 = true := by
  rw [show D2M8K2.u4054 = KTree.node D2M8K2.u4050 (nat_lit 9542345) (nat_lit 1804861965) (nat_lit 0) D2M8K2.u4053 from rfl, allE_node, arows4050, irow4054, arows4053]
  all_goals rfl

theorem atot4054 : totK PD2M8K2 D2M8K2.u4054 = [0, 753865312788, 2580868988347, 2507520152087, 1125224074372, 271327640009, 9302370699, 0] := by
  rw [show D2M8K2.u4054 = KTree.node D2M8K2.u4050 (nat_lit 9542345) (nat_lit 1804861965) (nat_lit 0) D2M8K2.u4053 from rfl, totK_node, atot4050, atot4053]
  decide +kernel

theorem arows4063 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4063 = true := by
  rw [show D2M8K2.u4063 = KTree.node D2M8K2.u4059 (nat_lit 9547900) (nat_lit 3961990416) (nat_lit 0) D2M8K2.u4062 from rfl, allE_node, arows4059, irow4063, arows4062]
  all_goals rfl

theorem atot4063 : totK PD2M8K2 D2M8K2.u4063 = [0, 850794831217, 2932691190704, 2802004073436, 634742890807, 22356163970, 0, 0] := by
  rw [show D2M8K2.u4063 = KTree.node D2M8K2.u4059 (nat_lit 9547900) (nat_lit 3961990416) (nat_lit 0) D2M8K2.u4062 from rfl, totK_node, atot4059, atot4062]
  decide +kernel

theorem arows4070 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4070 = true := by
  rw [show D2M8K2.u4070 = KTree.node D2M8K2.u4066 (nat_lit 9558276) (nat_lit 3212332077) (nat_lit 0) D2M8K2.u4069 from rfl, allE_node, arows4066, irow4070, arows4069]
  all_goals rfl

theorem atot4070 : totK PD2M8K2 D2M8K2.u4070 = [0, 416299879234, 2089338909615, 3201303994933, 1390233549097, 91731188826, 0, 0] := by
  rw [show D2M8K2.u4070 = KTree.node D2M8K2.u4066 (nat_lit 9558276) (nat_lit 3212332077) (nat_lit 0) D2M8K2.u4069 from rfl, totK_node, atot4066, atot4069]
  decide +kernel

theorem arows4078 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4078 = true := by
  rw [show D2M8K2.u4078 = KTree.node D2M8K2.u4074 (nat_lit 9567654) (nat_lit 3167563886) (nat_lit 0) D2M8K2.u4077 from rfl, allE_node, arows4074, irow4078, arows4077]
  all_goals rfl

theorem atot4078 : totK PD2M8K2 D2M8K2.u4078 = [0, 0, 1111138801401, 3356579711533, 2348800046085, 358694719445, 9072174562, 0] := by
  rw [show D2M8K2.u4078 = KTree.node D2M8K2.u4074 (nat_lit 9567654) (nat_lit 3167563886) (nat_lit 0) D2M8K2.u4077 from rfl, totK_node, atot4074, atot4077]
  decide +kernel

theorem arows4085 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4085 = true := by
  rw [show D2M8K2.u4085 = KTree.node D2M8K2.u4081 (nat_lit 9578240) (nat_lit 1949604577) (nat_lit 0) D2M8K2.u4084 from rfl, allE_node, arows4081, irow4085, arows4084]
  all_goals rfl

theorem atot4085 : totK PD2M8K2 D2M8K2.u4085 = [0, 564060001896, 2174688749533, 2855061947903, 1439535840151, 173655622563, 2340352732, 0] := by
  rw [show D2M8K2.u4085 = KTree.node D2M8K2.u4081 (nat_lit 9578240) (nat_lit 1949604577) (nat_lit 0) D2M8K2.u4084 from rfl, totK_node, atot4081, atot4084]
  decide +kernel

theorem arows4101 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4101 = true := by
  rw [show D2M8K2.u4101 = KTree.node D2M8K2.u4097 (nat_lit 9590726) (nat_lit 4180272124) (nat_lit 0) D2M8K2.u4100 from rfl, allE_node, arows4097, irow4101, arows4100]
  all_goals rfl

theorem atot4101 : totK PD2M8K2 D2M8K2.u4101 = [0, 680961197353, 2633997392031, 2965830254393, 929894805571, 50845775260, 0, 0] := by
  rw [show D2M8K2.u4101 = KTree.node D2M8K2.u4097 (nat_lit 9590726) (nat_lit 4180272124) (nat_lit 0) D2M8K2.u4100 from rfl, totK_node, atot4097, atot4100]
  decide +kernel

theorem arows4108 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4108 = true := by
  rw [show D2M8K2.u4108 = KTree.node D2M8K2.u4104 (nat_lit 9597537) (nat_lit 1606038479) (nat_lit 0) D2M8K2.u4107 from rfl, allE_node, arows4104, irow4108, arows4107]
  all_goals rfl

theorem atot4108 : totK PD2M8K2 D2M8K2.u4108 = [0, 773183840503, 2882850173569, 2888582738174, 670329357801, 25520220551, 0, 0] := by
  rw [show D2M8K2.u4108 = KTree.node D2M8K2.u4104 (nat_lit 9597537) (nat_lit 1606038479) (nat_lit 0) D2M8K2.u4107 from rfl, totK_node, atot4104, atot4107]
  decide +kernel

theorem arows4116 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4116 = true := by
  rw [show D2M8K2.u4116 = KTree.node D2M8K2.u4112 (nat_lit 9605340) (nat_lit 2644778135) (nat_lit 0) D2M8K2.u4115 from rfl, allE_node, arows4112, irow4116, arows4115]
  all_goals rfl

theorem atot4116 : totK PD2M8K2 D2M8K2.u4116 = [0, 0, 1171914546534, 3515472199679, 2318850295066, 214877373516, 0, 0] := by
  rw [show D2M8K2.u4116 = KTree.node D2M8K2.u4112 (nat_lit 9605340) (nat_lit 2644778135) (nat_lit 0) D2M8K2.u4115 from rfl, totK_node, atot4112, atot4115]
  decide +kernel

theorem arows4123 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4123 = true := by
  rw [show D2M8K2.u4123 = KTree.node D2M8K2.u4119 (nat_lit 9616965) (nat_lit 1475695603) (nat_lit 0) D2M8K2.u4122 from rfl, allE_node, arows4119, irow4123, arows4122]
  all_goals rfl

theorem atot4123 : totK PD2M8K2 D2M8K2.u4123 = [0, 190813401391, 1266778927261, 2947788097272, 2301931316350, 400722019521, 11552853615, 0] := by
  rw [show D2M8K2.u4123 = KTree.node D2M8K2.u4119 (nat_lit 9616965) (nat_lit 1475695603) (nat_lit 0) D2M8K2.u4122 from rfl, totK_node, atot4119, atot4122]
  decide +kernel

theorem arows4132 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4132 = true := by
  rw [show D2M8K2.u4132 = KTree.node D2M8K2.u4128 (nat_lit 9626576) (nat_lit 3129186728) (nat_lit 0) D2M8K2.u4131 from rfl, allE_node, arows4128, irow4132, arows4131]
  all_goals rfl

theorem atot4132 : totK PD2M8K2 D2M8K2.u4132 = [0, 837879648557, 2916627218624, 2765707062154, 716963067060, 37601708222, 0, 0] := by
  rw [show D2M8K2.u4132 = KTree.node D2M8K2.u4128 (nat_lit 9626576) (nat_lit 3129186728) (nat_lit 0) D2M8K2.u4131 from rfl, totK_node, atot4128, atot4131]
  decide +kernel

theorem arows4139 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4139 = true := by
  rw [show D2M8K2.u4139 = KTree.node D2M8K2.u4135 (nat_lit 9633024) (nat_lit 3686612343) (nat_lit 0) D2M8K2.u4138 from rfl, allE_node, arows4135, irow4139, arows4138]
  all_goals rfl

theorem atot4139 : totK PD2M8K2 D2M8K2.u4139 = [0, 802474718840, 2874405515146, 2849649051222, 657727367025, 26300412495, 0, 0] := by
  rw [show D2M8K2.u4139 = KTree.node D2M8K2.u4135 (nat_lit 9633024) (nat_lit 3686612343) (nat_lit 0) D2M8K2.u4138 from rfl, totK_node, atot4135, atot4138]
  decide +kernel

theorem arows4147 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4147 = true := by
  rw [show D2M8K2.u4147 = KTree.node D2M8K2.u4143 (nat_lit 9643423) (nat_lit 2220253905) (nat_lit 0) D2M8K2.u4146 from rfl, allE_node, arows4143, irow4147, arows4146]
  all_goals rfl

theorem atot4147 : totK PD2M8K2 D2M8K2.u4147 = [0, 180183318095, 1746182418035, 3488629912122, 1624128832270, 117414129327, 0, 0] := by
  rw [show D2M8K2.u4147 = KTree.node D2M8K2.u4143 (nat_lit 9643423) (nat_lit 2220253905) (nat_lit 0) D2M8K2.u4146 from rfl, totK_node, atot4143, atot4146]
  decide +kernel

theorem arows4154 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4154 = true := by
  rw [show D2M8K2.u4154 = KTree.node D2M8K2.u4150 (nat_lit 9654286) (nat_lit 3046213580) (nat_lit 0) D2M8K2.u4153 from rfl, allE_node, arows4150, irow4154, arows4153]
  all_goals rfl

theorem atot4154 : totK PD2M8K2 D2M8K2.u4154 = [0, 28842453189, 1219830660360, 3453090118261, 2217370366204, 259768546783, 2586295899, 0] := by
  rw [show D2M8K2.u4154 = KTree.node D2M8K2.u4150 (nat_lit 9654286) (nat_lit 3046213580) (nat_lit 0) D2M8K2.u4153 from rfl, totK_node, atot4150, atot4153]
  decide +kernel

theorem arows4164 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4164 = true := by
  rw [show D2M8K2.u4164 = KTree.node D2M8K2.u4160 (nat_lit 9667441) (nat_lit 1401464946) (nat_lit 0) D2M8K2.u4163 from rfl, allE_node, arows4160, irow4164, arows4163]
  all_goals rfl

theorem atot4164 : totK PD2M8K2 D2M8K2.u4164 = [0, 871188452968, 2955079939089, 2741091972348, 701685402215, 37589446790, 0, 0] := by
  rw [show D2M8K2.u4164 = KTree.node D2M8K2.u4160 (nat_lit 9667441) (nat_lit 1401464946) (nat_lit 0) D2M8K2.u4163 from rfl, totK_node, atot4160, atot4163]
  decide +kernel

theorem arows4171 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4171 = true := by
  rw [show D2M8K2.u4171 = KTree.node D2M8K2.u4167 (nat_lit 9673718) (nat_lit 3999417673) (nat_lit 0) D2M8K2.u4170 from rfl, allE_node, arows4167, irow4171, arows4170]
  all_goals rfl

theorem atot4171 : totK PD2M8K2 D2M8K2.u4171 = [0, 784213002852, 2898637124312, 2887128403955, 656204408107, 23390571289, 0, 0] := by
  rw [show D2M8K2.u4171 = KTree.node D2M8K2.u4167 (nat_lit 9673718) (nat_lit 3999417673) (nat_lit 0) D2M8K2.u4170 from rfl, totK_node, atot4167, atot4170]
  decide +kernel

theorem arows4179 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4179 = true := by
  rw [show D2M8K2.u4179 = KTree.node D2M8K2.u4175 (nat_lit 9683653) (nat_lit 1032721676) (nat_lit 0) D2M8K2.u4178 from rfl, allE_node, arows4175, irow4179, arows4178]
  all_goals rfl

theorem atot4179 : totK PD2M8K2 D2M8K2.u4179 = [0, 340088530745, 1905019569199, 3267104729442, 1637611213284, 119242095157, 0, 0] := by
  rw [show D2M8K2.u4179 = KTree.node D2M8K2.u4175 (nat_lit 9683653) (nat_lit 1032721676) (nat_lit 0) D2M8K2.u4178 from rfl, totK_node, atot4175, atot4178]
  decide +kernel

theorem arows4186 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4186 = true := by
  rw [show D2M8K2.u4186 = KTree.node D2M8K2.u4182 (nat_lit 9692939) (nat_lit 2748472794) (nat_lit 0) D2M8K2.u4185 from rfl, allE_node, arows4182, irow4186, arows4185]
  all_goals rfl

theorem atot4186 : totK PD2M8K2 D2M8K2.u4186 = [0, 0, 1006944389540, 3292335304800, 2579031790209, 334512978003, 2516941024, 0] := by
  rw [show D2M8K2.u4186 = KTree.node D2M8K2.u4182 (nat_lit 9692939) (nat_lit 2748472794) (nat_lit 0) D2M8K2.u4185 from rfl, totK_node, atot4182, atot4185]
  decide +kernel

theorem arows4195 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4195 = true := by
  rw [show D2M8K2.u4195 = KTree.node D2M8K2.u4191 (nat_lit 9703565) (nat_lit 1924327865) (nat_lit 0) D2M8K2.u4194 from rfl, allE_node, arows4191, irow4195, arows4194]
  all_goals rfl

theorem atot4195 : totK PD2M8K2 D2M8K2.u4195 = [0, 0, 890706924542, 2958914712542, 2696987755049, 667266309868, 35831606233, 0] := by
  rw [show D2M8K2.u4195 = KTree.node D2M8K2.u4191 (nat_lit 9703565) (nat_lit 1924327865) (nat_lit 0) D2M8K2.u4194 from rfl, totK_node, atot4191, atot4194]
  decide +kernel

theorem arows4202 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4202 = true := by
  rw [show D2M8K2.u4202 = KTree.node D2M8K2.u4198 (nat_lit 9754450) (nat_lit 4052776618) (nat_lit 0) D2M8K2.u4201 from rfl, allE_node, arows4198, irow4202, arows4201]
  all_goals rfl

theorem atot4202 : totK PD2M8K2 D2M8K2.u4202 = [0, 0, 845726118887, 2845437135140, 2786792189277, 741952947306, 28017909267, 0] := by
  rw [show D2M8K2.u4202 = KTree.node D2M8K2.u4198 (nat_lit 9754450) (nat_lit 4052776618) (nat_lit 0) D2M8K2.u4201 from rfl, totK_node, atot4198, atot4201]
  decide +kernel

theorem arows4210 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4210 = true := by
  rw [show D2M8K2.u4210 = KTree.node D2M8K2.u4206 (nat_lit 9760964) (nat_lit 3401468245) (nat_lit 0) D2M8K2.u4209 from rfl, allE_node, arows4206, irow4210, arows4209]
  all_goals rfl

theorem atot4210 : totK PD2M8K2 D2M8K2.u4210 = [0, 0, 845744674632, 3015323070591, 2809937382947, 543595564556, 11323144342, 0] := by
  rw [show D2M8K2.u4210 = KTree.node D2M8K2.u4206 (nat_lit 9760964) (nat_lit 3401468245) (nat_lit 0) D2M8K2.u4209 from rfl, totK_node, atot4206, atot4209]
  decide +kernel

theorem arows4217 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4217 = true := by
  rw [show D2M8K2.u4217 = KTree.node D2M8K2.u4213 (nat_lit 9771413) (nat_lit 2084101037) (nat_lit 0) D2M8K2.u4216 from rfl, allE_node, arows4213, irow4217, arows4216]
  all_goals rfl

theorem atot4217 : totK PD2M8K2 D2M8K2.u4217 = [0, 0, 0, 1149708010552, 3093467197433, 2322219250479, 614701867216, 36921873854] := by
  rw [show D2M8K2.u4217 = KTree.node D2M8K2.u4213 (nat_lit 9771413) (nat_lit 2084101037) (nat_lit 0) D2M8K2.u4216 from rfl, totK_node, atot4213, atot4216]
  decide +kernel

theorem arows4228 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4228 = true := by
  rw [show D2M8K2.u4228 = KTree.node D2M8K2.u4224 (nat_lit 9778066) (nat_lit 3968270893) (nat_lit 0) D2M8K2.u4227 from rfl, allE_node, arows4224, irow4228, arows4227]
  all_goals rfl

theorem atot4228 : totK PD2M8K2 D2M8K2.u4228 = [0, 0, 0, 896664482751, 3073006309818, 2663263412967, 451734644051, 10194375460] := by
  rw [show D2M8K2.u4228 = KTree.node D2M8K2.u4224 (nat_lit 9778066) (nat_lit 3968270893) (nat_lit 0) D2M8K2.u4227 from rfl, totK_node, atot4224, atot4227]
  decide +kernel

theorem arows4235 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4235 = true := by
  rw [show D2M8K2.u4235 = KTree.node D2M8K2.u4231 (nat_lit 9785383) (nat_lit 2187737404) (nat_lit 0) D2M8K2.u4234 from rfl, allE_node, arows4231, irow4235, arows4234]
  all_goals rfl

theorem atot4235 : totK PD2M8K2 D2M8K2.u4235 = [0, 0, 320804550429, 1411495223292, 2700012237617, 2270145530080, 424167199355, 10531122277] := by
  rw [show D2M8K2.u4235 = KTree.node D2M8K2.u4231 (nat_lit 9785383) (nat_lit 2187737404) (nat_lit 0) D2M8K2.u4234 from rfl, totK_node, atot4231, atot4234]
  decide +kernel

theorem arows4243 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4243 = true := by
  rw [show D2M8K2.u4243 = KTree.node D2M8K2.u4239 (nat_lit 9793399) (nat_lit 1171435104) (nat_lit 0) D2M8K2.u4242 from rfl, allE_node, arows4239, irow4243, arows4242]
  all_goals rfl

theorem atot4243 : totK PD2M8K2 D2M8K2.u4243 = [0, 0, 870844908760, 2946745932674, 2724387645730, 701903613688, 37487326182, 0] := by
  rw [show D2M8K2.u4243 = KTree.node D2M8K2.u4239 (nat_lit 9793399) (nat_lit 1171435104) (nat_lit 0) D2M8K2.u4242 from rfl, totK_node, atot4239, atot4242]
  decide +kernel

theorem arows4250 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4250 = true := by
  rw [show D2M8K2.u4250 = KTree.node D2M8K2.u4246 (nat_lit 9803060) (nat_lit 3663048984) (nat_lit 0) D2M8K2.u4249 from rfl, allE_node, arows4246, irow4250, arows4249]
  all_goals rfl

theorem atot4250 : totK PD2M8K2 D2M8K2.u4250 = [0, 0, 825588880077, 2958405981213, 2862559333143, 577084825430, 11680927122, 0] := by
  rw [show D2M8K2.u4250 = KTree.node D2M8K2.u4246 (nat_lit 9803060) (nat_lit 3663048984) (nat_lit 0) D2M8K2.u4249 from rfl, totK_node, atot4246, atot4249]
  decide +kernel

theorem arows4259 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4259 = true := by
  rw [show D2M8K2.u4259 = KTree.node D2M8K2.u4255 (nat_lit 9812674) (nat_lit 3822482093) (nat_lit 0) D2M8K2.u4258 from rfl, allE_node, arows4255, irow4259, arows4258]
  all_goals rfl

theorem atot4259 : totK PD2M8K2 D2M8K2.u4259 = [0, 0, 0, 1487860782080, 3735018485000, 1823668045069, 121574212554, 0] := by
  rw [show D2M8K2.u4259 = KTree.node D2M8K2.u4255 (nat_lit 9812674) (nat_lit 3822482093) (nat_lit 0) D2M8K2.u4258 from rfl, totK_node, atot4255, atot4258]
  decide +kernel

theorem arows4266 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4266 = true := by
  rw [show D2M8K2.u4266 = KTree.node D2M8K2.u4262 (nat_lit 9824981) (nat_lit 1779741267) (nat_lit 2) D2M8K2.u4265 from rfl, allE_node, arows4262, irow4266, arows4265]
  all_goals rfl

theorem atot4266 : totK PD2M8K2 D2M8K2.u4266 = [0, 0, 320954541705, 1628753876777, 2963314123514, 1901151468930, 273077003993, 6546549506] := by
  rw [show D2M8K2.u4266 = KTree.node D2M8K2.u4262 (nat_lit 9824981) (nat_lit 1779741267) (nat_lit 2) D2M8K2.u4265 from rfl, totK_node, atot4262, atot4265]
  decide +kernel

theorem arows4274 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4274 = true := by
  rw [show D2M8K2.u4274 = KTree.node D2M8K2.u4270 (nat_lit 9834832) (nat_lit 3612267483) (nat_lit 0) D2M8K2.u4273 from rfl, allE_node, arows4270, irow4274, arows4273]
  all_goals rfl

theorem atot4274 : totK PD2M8K2 D2M8K2.u4274 = [0, 0, 871055086642, 2951807138548, 2734192805876, 701171495107, 37485699534, 0] := by
  rw [show D2M8K2.u4274 = KTree.node D2M8K2.u4270 (nat_lit 9834832) (nat_lit 3612267483) (nat_lit 0) D2M8K2.u4273 from rfl, totK_node, atot4270, atot4273]
  decide +kernel

theorem arows4281 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4281 = true := by
  rw [show D2M8K2.u4281 = KTree.node D2M8K2.u4277 (nat_lit 9844484) (nat_lit 3284071475) (nat_lit 0) D2M8K2.u4280 from rfl, allE_node, arows4277, irow4281, arows4280]
  all_goals rfl

theorem atot4281 : totK PD2M8K2 D2M8K2.u4281 = [0, 0, 825738586748, 2969222396412, 2856008916174, 570161720922, 11784327261, 0] := by
  rw [show D2M8K2.u4281 = KTree.node D2M8K2.u4277 (nat_lit 9844484) (nat_lit 3284071475) (nat_lit 0) D2M8K2.u4280 from rfl, totK_node, atot4277, atot4280]
  decide +kernel

theorem arows4291 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4291 = true := by
  rw [show D2M8K2.u4291 = KTree.node D2M8K2.u4287 (nat_lit 9854167) (nat_lit 2366229031) (nat_lit 0) D2M8K2.u4290 from rfl, allE_node, arows4287, irow4291, arows4290]
  all_goals rfl

theorem atot4291 : totK PD2M8K2 D2M8K2.u4291 = [0, 0, 0, 1511721035095, 3687353795657, 1856564408181, 127567248366, 0] := by
  rw [show D2M8K2.u4291 = KTree.node D2M8K2.u4287 (nat_lit 9854167) (nat_lit 2366229031) (nat_lit 0) D2M8K2.u4290 from rfl, totK_node, atot4287, atot4290]
  decide +kernel

theorem arows4298 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4298 = true := by
  rw [show D2M8K2.u4298 = KTree.node D2M8K2.u4294 (nat_lit 9866476) (nat_lit 2432072162) (nat_lit 0) D2M8K2.u4297 from rfl, allE_node, arows4294, irow4298, arows4297]
  all_goals rfl

theorem atot4298 : totK PD2M8K2 D2M8K2.u4298 = [0, 0, 319053168236, 1604024923360, 2946079113352, 1926022939258, 276859447262, 6624648996] := by
  rw [show D2M8K2.u4298 = KTree.node D2M8K2.u4294 (nat_lit 9866476) (nat_lit 2432072162) (nat_lit 0) D2M8K2.u4297 from rfl, totK_node, atot4294, atot4297]
  decide +kernel

theorem arows4306 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4306 = true := by
  rw [show D2M8K2.u4306 = KTree.node D2M8K2.u4302 (nat_lit 9876233) (nat_lit 1571233714) (nat_lit 0) D2M8K2.u4305 from rfl, allE_node, arows4302, irow4306, arows4305]
  all_goals rfl

theorem atot4306 : totK PD2M8K2 D2M8K2.u4306 = [0, 0, 842653940905, 2914900431555, 2752117479072, 705716927352, 37491288561, 0] := by
  rw [show D2M8K2.u4306 = KTree.node D2M8K2.u4302 (nat_lit 9876233) (nat_lit 1571233714) (nat_lit 0) D2M8K2.u4305 from rfl, totK_node, atot4302, atot4305]
  decide +kernel

theorem arows4313 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4313 = true := by
  rw [show D2M8K2.u4313 = KTree.node D2M8K2.u4309 (nat_lit 9882651) (nat_lit 1587811752) (nat_lit 0) D2M8K2.u4312 from rfl, allE_node, arows4309, irow4313, arows4312]
  all_goals rfl

theorem atot4313 : totK PD2M8K2 D2M8K2.u4313 = [0, 0, 849935416618, 2958177512786, 2767432417855, 604774046331, 18310713090, 0] := by
  rw [show D2M8K2.u4313 = KTree.node D2M8K2.u4309 (nat_lit 9882651) (nat_lit 1587811752) (nat_lit 0) D2M8K2.u4312 from rfl, totK_node, atot4309, atot4312]
  decide +kernel

theorem arows4322 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4322 = true := by
  rw [show D2M8K2.u4322 = KTree.node D2M8K2.u4318 (nat_lit 9895484) (nat_lit 3375134809) (nat_lit 0) D2M8K2.u4321 from rfl, allE_node, arows4318, irow4322, arows4321]
  all_goals rfl

theorem atot4322 : totK PD2M8K2 D2M8K2.u4322 = [0, 0, 0, 1703879475365, 3941302936731, 1469835249601, 72992064647, 0] := by
  rw [show D2M8K2.u4322 = KTree.node D2M8K2.u4318 (nat_lit 9895484) (nat_lit 3375134809) (nat_lit 0) D2M8K2.u4321 from rfl, totK_node, atot4318, atot4321]
  decide +kernel

theorem arows4329 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4329 = true := by
  rw [show D2M8K2.u4329 = KTree.node D2M8K2.u4325 (nat_lit 9906946) (nat_lit 3697148776) (nat_lit 0) D2M8K2.u4328 from rfl, allE_node, arows4325, irow4329, arows4328]
  all_goals rfl

theorem atot4329 : totK PD2M8K2 D2M8K2.u4329 = [0, 0, 416375132788, 1968599245733, 3073805068136, 1581006073797, 163182494061, 1429815836] := by
  rw [show D2M8K2.u4329 = KTree.node D2M8K2.u4325 (nat_lit 9906946) (nat_lit 3697148776) (nat_lit 0) D2M8K2.u4328 from rfl, totK_node, atot4325, atot4328]
  decide +kernel

theorem arows4337 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4337 = true := by
  rw [show D2M8K2.u4337 = KTree.node D2M8K2.u4333 (nat_lit 9918556) (nat_lit 3887696092) (nat_lit 0) D2M8K2.u4336 from rfl, allE_node, arows4333, irow4337, arows4336]
  all_goals rfl

theorem atot4337 : totK PD2M8K2 D2M8K2.u4337 = [0, 0, 751283339581, 2723931859392, 2876261040477, 851695864440, 44062675809, 0] := by
  rw [show D2M8K2.u4337 = KTree.node D2M8K2.u4333 (nat_lit 9918556) (nat_lit 3887696092) (nat_lit 0) D2M8K2.u4336 from rfl, totK_node, atot4333, atot4336]
  decide +kernel

theorem arows4344 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4344 = true := by
  rw [show D2M8K2.u4344 = KTree.node D2M8K2.u4340 (nat_lit 9925422) (nat_lit 4048482758) (nat_lit 0) D2M8K2.u4343 from rfl, allE_node, arows4340, irow4344, arows4343]
  all_goals rfl

theorem atot4344 : totK PD2M8K2 D2M8K2.u4344 = [0, 0, 855835788588, 2992315682698, 2830233819122, 581292370485, 9073582858, 0] := by
  rw [show D2M8K2.u4344 = KTree.node D2M8K2.u4340 (nat_lit 9925422) (nat_lit 4048482758) (nat_lit 0) D2M8K2.u4343 from rfl, totK_node, atot4340, atot4343]
  decide +kernel

theorem arows4356 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4356 = true := by
  rw [show D2M8K2.u4356 = KTree.node D2M8K2.u4352 (nat_lit 9939601) (nat_lit 1557112149) (nat_lit 0) D2M8K2.u4355 from rfl, allE_node, arows4352, irow4356, arows4355]
  all_goals rfl

theorem atot4356 : totK PD2M8K2 D2M8K2.u4356 = [0, 0, 0, 1416056854657, 3513554945015, 2073241374579, 201208983674, 1323630408] := by
  rw [show D2M8K2.u4356 = KTree.node D2M8K2.u4352 (nat_lit 9939601) (nat_lit 1557112149) (nat_lit 0) D2M8K2.u4355 from rfl, totK_node, atot4352, atot4355]
  decide +kernel

theorem arows4363 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4363 = true := by
  rw [show D2M8K2.u4363 = KTree.node D2M8K2.u4359 (nat_lit 9950824) (nat_lit 3257325699) (nat_lit 0) D2M8K2.u4362 from rfl, allE_node, arows4359, irow4363, arows4362]
  all_goals rfl

theorem atot4363 : totK PD2M8K2 D2M8K2.u4363 = [0, 327677273344, 744594656918, 973245841357, 2474422152628, 2224303482172, 374142797683, 10866219959] := by
  rw [show D2M8K2.u4363 = KTree.node D2M8K2.u4359 (nat_lit 9950824) (nat_lit 3257325699) (nat_lit 0) D2M8K2.u4362 from rfl, totK_node, atot4359, atot4362]
  decide +kernel

theorem arows4371 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4371 = true := by
  rw [show D2M8K2.u4371 = KTree.node D2M8K2.u4367 (nat_lit 9961605) (nat_lit 1725962346) (nat_lit 0) D2M8K2.u4370 from rfl, allE_node, arows4367, irow4371, arows4370]
  all_goals rfl

theorem atot4371 : totK PD2M8K2 D2M8K2.u4371 = [0, 826283657910, 3025635993160, 2809192590785, 516092146280, 14418877666, 0, 0] := by
  rw [show D2M8K2.u4371 = KTree.node D2M8K2.u4367 (nat_lit 9961605) (nat_lit 1725962346) (nat_lit 0) D2M8K2.u4370 from rfl, totK_node, atot4367, atot4370]
  decide +kernel

theorem arows4378 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4378 = true := by
  rw [show D2M8K2.u4378 = KTree.node D2M8K2.u4374 (nat_lit 9972133) (nat_lit 1366036621) (nat_lit 0) D2M8K2.u4377 from rfl, allE_node, arows4374, irow4378, arows4377]
  all_goals rfl

theorem atot4378 : totK PD2M8K2 D2M8K2.u4378 = [0, 493589057864, 2475697464448, 3276551021887, 888371434109, 33541235863, 0, 0] := by
  rw [show D2M8K2.u4378 = KTree.node D2M8K2.u4374 (nat_lit 9972133) (nat_lit 1366036621) (nat_lit 0) D2M8K2.u4377 from rfl, totK_node, atot4374, atot4377]
  decide +kernel

theorem arows4387 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4387 = true := by
  rw [show D2M8K2.u4387 = KTree.node D2M8K2.u4383 (nat_lit 9987956) (nat_lit 3666590483) (nat_lit 0) D2M8K2.u4386 from rfl, allE_node, arows4383, irow4387, arows4386]
  all_goals rfl

theorem atot4387 : totK PD2M8K2 D2M8K2.u4387 = [0, 0, 1239272437529, 3613625066585, 2068660796185, 171948628771, 1369150432, 0] := by
  rw [show D2M8K2.u4387 = KTree.node D2M8K2.u4383 (nat_lit 9987956) (nat_lit 3666590483) (nat_lit 0) D2M8K2.u4386 from rfl, totK_node, atot4383, atot4386]
  decide +kernel

theorem arows4394 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4394 = true := by
  rw [show D2M8K2.u4394 = KTree.node D2M8K2.u4390 (nat_lit 10001097) (nat_lit 1834682607) (nat_lit 0) D2M8K2.u4393 from rfl, allE_node, arows4390, irow4394, arows4393]
  all_goals rfl

theorem atot4394 : totK PD2M8K2 D2M8K2.u4394 = [0, 871790450706, 2889195460735, 2752206628180, 781166171737, 45866246325, 0, 0] := by
  rw [show D2M8K2.u4394 = KTree.node D2M8K2.u4390 (nat_lit 10001097) (nat_lit 1834682607) (nat_lit 0) D2M8K2.u4393 from rfl, totK_node, atot4390, atot4393]
  decide +kernel

theorem arows4402 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4402 = true := by
  rw [show D2M8K2.u4402 = KTree.node D2M8K2.u4398 (nat_lit 10008152) (nat_lit 3517071465) (nat_lit 0) D2M8K2.u4401 from rfl, allE_node, arows4398, irow4402, arows4401]
  all_goals rfl

theorem atot4402 : totK PD2M8K2 D2M8K2.u4402 = [0, 758867390222, 2913789272680, 2966509932072, 634309605140, 22144658573, 0, 0] := by
  rw [show D2M8K2.u4402 = KTree.node D2M8K2.u4398 (nat_lit 10008152) (nat_lit 3517071465) (nat_lit 0) D2M8K2.u4401 from rfl, totK_node, atot4398, atot4401]
  decide +kernel

theorem arows4409 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4409 = true := by
  rw [show D2M8K2.u4409 = KTree.node D2M8K2.u4405 (nat_lit 10014893) (nat_lit 1529859789) (nat_lit 0) D2M8K2.u4408 from rfl, allE_node, arows4405, irow4409, arows4408]
  all_goals rfl

theorem atot4409 : totK PD2M8K2 D2M8K2.u4409 = [0, 417475016712, 1939851442216, 2990567338176, 1597047752986, 327314343683, 25191558099, 0] := by
  rw [show D2M8K2.u4409 = KTree.node D2M8K2.u4405 (nat_lit 10014893) (nat_lit 1529859789) (nat_lit 0) D2M8K2.u4408 from rfl, totK_node, atot4405, atot4408]
  decide +kernel

theorem arows4419 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4419 = true := by
  rw [show D2M8K2.u4419 = KTree.node D2M8K2.u4415 (nat_lit 10024502) (nat_lit 3941030750) (nat_lit 0) D2M8K2.u4418 from rfl, allE_node, arows4415, irow4419, arows4418]
  all_goals rfl

theorem atot4419 : totK PD2M8K2 D2M8K2.u4419 = [0, 0, 771011785176, 2867910044493, 2931530392406, 679916320015, 20922116152, 0] := by
  rw [show D2M8K2.u4419 = KTree.node D2M8K2.u4415 (nat_lit 10024502) (nat_lit 3941030750) (nat_lit 0) D2M8K2.u4418 from rfl, totK_node, atot4415, atot4418]
  decide +kernel

theorem arows4426 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4426 = true := by
  rw [show D2M8K2.u4426 = KTree.node D2M8K2.u4422 (nat_lit 10032309) (nat_lit 1741952189) (nat_lit 0) D2M8K2.u4425 from rfl, allE_node, arows4422, irow4426, arows4425]
  all_goals rfl

theorem atot4426 : totK PD2M8K2 D2M8K2.u4426 = [0, 0, 827235949617, 3051713409610, 2884556237547, 488816266913, 5086161850, 0] := by
  rw [show D2M8K2.u4426 = KTree.node D2M8K2.u4422 (nat_lit 10032309) (nat_lit 1741952189) (nat_lit 0) D2M8K2.u4425 from rfl, totK_node, atot4422, atot4425]
  decide +kernel

theorem arows4434 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4434 = true := by
  rw [show D2M8K2.u4434 = KTree.node D2M8K2.u4430 (nat_lit 10040142) (nat_lit 3851970610) (nat_lit 0) D2M8K2.u4433 from rfl, allE_node, arows4430, irow4434, arows4433]
  all_goals rfl

theorem atot4434 : totK PD2M8K2 D2M8K2.u4434 = [0, 824384233447, 2878649552636, 2711963664229, 700274163497, 104070388212, 6818291842, 0] := by
  rw [show D2M8K2.u4434 = KTree.node D2M8K2.u4430 (nat_lit 10040142) (nat_lit 3851970610) (nat_lit 0) D2M8K2.u4433 from rfl, totK_node, atot4430, atot4433]
  decide +kernel

theorem arows4441 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4441 = true := by
  rw [show D2M8K2.u4441 = KTree.node D2M8K2.u4437 (nat_lit 10046020) (nat_lit 3715339663) (nat_lit 0) D2M8K2.u4440 from rfl, allE_node, arows4437, irow4441, arows4440]
  all_goals rfl

theorem atot4441 : totK PD2M8K2 D2M8K2.u4441 = [0, 861939549384, 2986251092401, 2777930472983, 582905400612, 20923642019, 0, 0] := by
  rw [show D2M8K2.u4441 = KTree.node D2M8K2.u4437 (nat_lit 10046020) (nat_lit 3715339663) (nat_lit 0) D2M8K2.u4440 from rfl, totK_node, atot4437, atot4440]
  decide +kernel

theorem arows4450 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4450 = true := by
  rw [show D2M8K2.u4450 = KTree.node D2M8K2.u4446 (nat_lit 10056005) (nat_lit 2366851252) (nat_lit 0) D2M8K2.u4449 from rfl, allE_node, arows4446, irow4450, arows4449]
  all_goals rfl

theorem atot4450 : totK PD2M8K2 D2M8K2.u4450 = [0, 420804927456, 2020800845539, 3109585473355, 1402920707692, 126789083895, 1206465782, 0] := by
  rw [show D2M8K2.u4450 = KTree.node D2M8K2.u4446 (nat_lit 10056005) (nat_lit 2366851252) (nat_lit 0) D2M8K2.u4449 from rfl, totK_node, atot4446, atot4449]
  decide +kernel

theorem arows4457 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4457 = true := by
  rw [show D2M8K2.u4457 = KTree.node D2M8K2.u4453 (nat_lit 10064624) (nat_lit 3654073635) (nat_lit 0) D2M8K2.u4456 from rfl, allE_node, arows4453, irow4457, arows4456]
  all_goals rfl

theorem atot4457 : totK PD2M8K2 D2M8K2.u4457 = [0, 0, 1104688304567, 3311094189953, 2379042220106, 384843106311, 13016197374, 0] := by
  rw [show D2M8K2.u4457 = KTree.node D2M8K2.u4453 (nat_lit 10064624) (nat_lit 3654073635) (nat_lit 0) D2M8K2.u4456 from rfl, totK_node, atot4453, atot4456]
  decide +kernel

theorem arows4465 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4465 = true := by
  rw [show D2M8K2.u4465 = KTree.node D2M8K2.u4461 (nat_lit 10075087) (nat_lit 1629666731) (nat_lit 0) D2M8K2.u4464 from rfl, allE_node, arows4461, irow4465, arows4464]
  all_goals rfl

theorem atot4465 : totK PD2M8K2 D2M8K2.u4465 = [0, 376987030740, 1838387335229, 2988934410235, 1643408178019, 208712801283, 4574395652, 0] := by
  rw [show D2M8K2.u4465 = KTree.node D2M8K2.u4461 (nat_lit 10075087) (nat_lit 1629666731) (nat_lit 0) D2M8K2.u4464 from rfl, totK_node, atot4461, atot4464]
  decide +kernel

theorem arows4472 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4472 = true := by
  rw [show D2M8K2.u4472 = KTree.node D2M8K2.u4468 (nat_lit 10125468) (nat_lit 2011247330) (nat_lit 0) D2M8K2.u4471 from rfl, allE_node, arows4468, irow4472, arows4471]
  all_goals rfl

theorem atot4472 : totK PD2M8K2 D2M8K2.u4472 = [0, 843268018972, 2873082060754, 2772889804671, 754408957360, 38732586595, 0, 0] := by
  rw [show D2M8K2.u4472 = KTree.node D2M8K2.u4468 (nat_lit 10125468) (nat_lit 2011247330) (nat_lit 0) D2M8K2.u4471 from rfl, totK_node, atot4468, atot4471]
  decide +kernel

theorem arows4483 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4483 = true := by
  rw [show D2M8K2.u4483 = KTree.node D2M8K2.u4479 (nat_lit 10132515) (nat_lit 3639380560) (nat_lit 0) D2M8K2.u4482 from rfl, allE_node, arows4479, irow4483, arows4482]
  all_goals rfl

theorem atot4483 : totK PD2M8K2 D2M8K2.u4483 = [0, 762937489528, 2899860231308, 2904200148963, 627993916969, 25034524587, 0, 0] := by
  rw [show D2M8K2.u4483 = KTree.node D2M8K2.u4479 (nat_lit 10132515) (nat_lit 3639380560) (nat_lit 0) D2M8K2.u4482 from rfl, totK_node, atot4479, atot4482]
  decide +kernel

theorem arows4490 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4490 = true := by
  rw [show D2M8K2.u4490 = KTree.node D2M8K2.u4486 (nat_lit 10143963) (nat_lit 3765844345) (nat_lit 0) D2M8K2.u4489 from rfl, allE_node, arows4486, irow4490, arows4489]
  all_goals rfl

theorem atot4490 : totK PD2M8K2 D2M8K2.u4490 = [0, 0, 1253743690039, 3600009948131, 2081702407620, 179270007293, 1138244013, 0] := by
  rw [show D2M8K2.u4490 = KTree.node D2M8K2.u4486 (nat_lit 10143963) (nat_lit 3765844345) (nat_lit 0) D2M8K2.u4489 from rfl, totK_node, atot4486, atot4489]
  decide +kernel

theorem arows4498 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4498 = true := by
  rw [show D2M8K2.u4498 = KTree.node D2M8K2.u4494 (nat_lit 10155105) (nat_lit 1845086237) (nat_lit 0) D2M8K2.u4497 from rfl, allE_node, arows4494, irow4498, arows4497]
  all_goals rfl

theorem atot4498 : totK PD2M8K2 D2M8K2.u4498 = [0, 379032392427, 1799218366815, 2957017133129, 1726523183984, 248272047540, 4977114383, 0] := by
  rw [show D2M8K2.u4498 = KTree.node D2M8K2.u4494 (nat_lit 10155105) (nat_lit 1845086237) (nat_lit 0) D2M8K2.u4497 from rfl, totK_node, atot4494, atot4497]
  decide +kernel

theorem arows4505 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4505 = true := by
  rw [show D2M8K2.u4505 = KTree.node D2M8K2.u4501 (nat_lit 10166443) (nat_lit 1635903698) (nat_lit 0) D2M8K2.u4504 from rfl, allE_node, arows4501, irow4505, arows4504]
  all_goals rfl

theorem atot4505 : totK PD2M8K2 D2M8K2.u4505 = [0, 845607258704, 2897939355245, 2797764323037, 745524815353, 38923874675, 0, 0] := by
  rw [show D2M8K2.u4505 = KTree.node D2M8K2.u4501 (nat_lit 10166443) (nat_lit 1635903698) (nat_lit 0) D2M8K2.u4504 from rfl, totK_node, atot4501, atot4504]
  decide +kernel

theorem arows4514 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4514 = true := by
  rw [show D2M8K2.u4514 = KTree.node D2M8K2.u4510 (nat_lit 10173069) (nat_lit 1433742690) (nat_lit 0) D2M8K2.u4513 from rfl, allE_node, arows4510, irow4514, arows4513]
  all_goals rfl

theorem atot4514 : totK PD2M8K2 D2M8K2.u4514 = [0, 770562027082, 2864262926054, 2948062695183, 673849640583, 22567804483, 0, 0] := by
  rw [show D2M8K2.u4514 = KTree.node D2M8K2.u4510 (nat_lit 10173069) (nat_lit 1433742690) (nat_lit 0) D2M8K2.u4513 from rfl, totK_node, atot4510, atot4513]
  decide +kernel

theorem arows4521 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4521 = true := by
  rw [show D2M8K2.u4521 = KTree.node D2M8K2.u4517 (nat_lit 10183714) (nat_lit 3865247755) (nat_lit 0) D2M8K2.u4520 from rfl, allE_node, arows4517, irow4521, arows4520]
  all_goals rfl

theorem atot4521 : totK PD2M8K2 D2M8K2.u4521 = [0, 0, 1254516465235, 3542027325039, 2197999035599, 206279476186, 1310285577, 0] := by
  rw [show D2M8K2.u4521 = KTree.node D2M8K2.u4517 (nat_lit 10183714) (nat_lit 3865247755) (nat_lit 0) D2M8K2.u4520 from rfl, totK_node, atot4517, atot4520]
  decide +kernel

theorem arows4529 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4529 = true := by
  rw [show D2M8K2.u4529 = KTree.node D2M8K2.u4525 (nat_lit 10192724) (nat_lit 3495090639) (nat_lit 0) D2M8K2.u4528 from rfl, allE_node, arows4525, irow4529, arows4528]
  all_goals rfl

theorem atot4529 : totK PD2M8K2 D2M8K2.u4529 = [0, 0, 1019904815294, 3281876141859, 2560425584179, 368544272540, 6324401156, 0] := by
  rw [show D2M8K2.u4529 = KTree.node D2M8K2.u4525 (nat_lit 10192724) (nat_lit 3495090639) (nat_lit 0) D2M8K2.u4528 from rfl, totK_node, atot4525, atot4528]
  decide +kernel

theorem arows4536 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4536 = true := by
  rw [show D2M8K2.u4536 = KTree.node D2M8K2.u4532 (nat_lit 10203560) (nat_lit 2760260434) (nat_lit 0) D2M8K2.u4535 from rfl, allE_node, arows4532, irow4536, arows4535]
  all_goals rfl

theorem atot4536 : totK PD2M8K2 D2M8K2.u4536 = [0, 0, 841376919299, 3000031259749, 2738168957265, 524144440654, 19383303073, 0] := by
  rw [show D2M8K2.u4536 = KTree.node D2M8K2.u4532 (nat_lit 10203560) (nat_lit 2760260434) (nat_lit 0) D2M8K2.u4535 from rfl, totK_node, atot4532, atot4535]
  decide +kernel

theorem arows4546 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4546 = true := by
  rw [show D2M8K2.u4546 = KTree.node D2M8K2.u4542 (nat_lit 10217983) (nat_lit 2013475577) (nat_lit 0) D2M8K2.u4545 from rfl, allE_node, arows4542, irow4546, arows4545]
  all_goals rfl

theorem atot4546 : totK PD2M8K2 D2M8K2.u4546 = [0, 0, 1011569188555, 3316242980167, 2598481657483, 289456243001, 2260824724, 0] := by
  rw [show D2M8K2.u4546 = KTree.node D2M8K2.u4542 (nat_lit 10217983) (nat_lit 2013475577) (nat_lit 0) D2M8K2.u4545 from rfl, totK_node, atot4542, atot4545]
  decide +kernel

theorem arows4553 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4553 = true := by
  rw [show D2M8K2.u4553 = KTree.node D2M8K2.u4549 (nat_lit 10250738) (nat_lit 3049191528) (nat_lit 0) D2M8K2.u4552 from rfl, allE_node, arows4549, irow4553, arows4552]
  all_goals rfl

theorem atot4553 : totK PD2M8K2 D2M8K2.u4553 = [0, 0, 747205095077, 2734645629258, 2894729070708, 857584737390, 46586918653, 0] := by
  rw [show D2M8K2.u4553 = KTree.node D2M8K2.u4549 (nat_lit 10250738) (nat_lit 3049191528) (nat_lit 0) D2M8K2.u4552 from rfl, totK_node, atot4549, atot4552]
  decide +kernel

theorem arows4561 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4561 = true := by
  rw [show D2M8K2.u4561 = KTree.node D2M8K2.u4557 (nat_lit 10258086) (nat_lit 3058419716) (nat_lit 0) D2M8K2.u4560 from rfl, allE_node, arows4557, irow4561, arows4560]
  all_goals rfl

theorem atot4561 : totK PD2M8K2 D2M8K2.u4561 = [0, 0, 941062428499, 3190462553389, 2719631485438, 457211496591, 8024043508, 0] := by
  rw [show D2M8K2.u4561 = KTree.node D2M8K2.u4557 (nat_lit 10258086) (nat_lit 3058419716) (nat_lit 0) D2M8K2.u4560 from rfl, totK_node, atot4557, atot4560]
  decide +kernel

theorem arows4568 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4568 = true := by
  rw [show D2M8K2.u4568 = KTree.node D2M8K2.u4564 (nat_lit 10286215) (nat_lit 2310181643) (nat_lit 0) D2M8K2.u4567 from rfl, allE_node, arows4564, irow4568, arows4567]
  all_goals rfl

theorem atot4568 : totK PD2M8K2 D2M8K2.u4568 = [0, 0, 873743928246, 3018579413301, 2742194885218, 535028429674, 14969034330, 0] := by
  rw [show D2M8K2.u4568 = KTree.node D2M8K2.u4564 (nat_lit 10286215) (nat_lit 2310181643) (nat_lit 0) D2M8K2.u4567 from rfl, totK_node, atot4564, atot4567]
  decide +kernel

theorem arows4577 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4577 = true := by
  rw [show D2M8K2.u4577 = KTree.node D2M8K2.u4573 (nat_lit 10292719) (nat_lit 1608942558) (nat_lit 0) D2M8K2.u4576 from rfl, allE_node, arows4573, irow4577, arows4576]
  all_goals rfl

theorem atot4577 : totK PD2M8K2 D2M8K2.u4577 = [0, 0, 718820766077, 2729659968058, 2945992194518, 807094031666, 37138651511, 0] := by
  rw [show D2M8K2.u4577 = KTree.node D2M8K2.u4573 (nat_lit 10292719) (nat_lit 1608942558) (nat_lit 0) D2M8K2.u4576 from rfl, totK_node, atot4573, atot4576]
  decide +kernel

theorem arows4584 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4584 = true := by
  rw [show D2M8K2.u4584 = KTree.node D2M8K2.u4580 (nat_lit 10303036) (nat_lit 3954847455) (nat_lit 0) D2M8K2.u4583 from rfl, allE_node, arows4580, irow4584, arows4583]
  all_goals rfl

theorem atot4584 : totK PD2M8K2 D2M8K2.u4584 = [0, 0, 642027063142, 2716184804192, 3034875956139, 728723303351, 23284566937, 0] := by
  rw [show D2M8K2.u4584 = KTree.node D2M8K2.u4580 (nat_lit 10303036) (nat_lit 3954847455) (nat_lit 0) D2M8K2.u4583 from rfl, totK_node, atot4580, atot4583]
  decide +kernel

theorem arows4592 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4592 = true := by
  rw [show D2M8K2.u4592 = KTree.node D2M8K2.u4588 (nat_lit 10313380) (nat_lit 3881538657) (nat_lit 0) D2M8K2.u4591 from rfl, allE_node, arows4588, irow4592, arows4591]
  all_goals rfl

theorem atot4592 : totK PD2M8K2 D2M8K2.u4592 = [0, 0, 0, 1270307676918, 3485179054685, 2069912138738, 272866049800, 5717851365] := by
  rw [show D2M8K2.u4592 = KTree.node D2M8K2.u4588 (nat_lit 10313380) (nat_lit 3881538657) (nat_lit 0) D2M8K2.u4591 from rfl, totK_node, atot4588, atot4591]
  decide +kernel

theorem arows4599 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4599 = true := by
  rw [show D2M8K2.u4599 = KTree.node D2M8K2.u4595 (nat_lit 10324676) (nat_lit 1444773680) (nat_lit 0) D2M8K2.u4598 from rfl, allE_node, arows4595, irow4599, arows4598]
  all_goals rfl

theorem atot4599 : totK PD2M8K2 D2M8K2.u4599 = [0, 0, 478410727792, 2110144358121, 3018232564001, 1300384179443, 131499484848, 1330264907] := by
  rw [show D2M8K2.u4599 = KTree.node D2M8K2.u4595 (nat_lit 10324676) (nat_lit 1444773680) (nat_lit 0) D2M8K2.u4598 from rfl, totK_node, atot4595, atot4598]
  decide +kernel

theorem arows4612 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4612 = true := by
  rw [show D2M8K2.u4612 = KTree.node D2M8K2.u4608 (nat_lit 10375183) (nat_lit 904874083) (nat_lit 0) D2M8K2.u4611 from rfl, allE_node, arows4608, irow4612, arows4611]
  all_goals rfl

theorem atot4612 : totK PD2M8K2 D2M8K2.u4612 = [0, 0, 802637393699, 2874080666064, 2823867003623, 699711655605, 28063716506, 0] := by
  rw [show D2M8K2.u4612 = KTree.node D2M8K2.u4608 (nat_lit 10375183) (nat_lit 904874083) (nat_lit 0) D2M8K2.u4611 from rfl, totK_node, atot4608, atot4611]
  decide +kernel

theorem arows4619 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4619 = true := by
  rw [show D2M8K2.u4619 = KTree.node D2M8K2.u4615 (nat_lit 10382656) (nat_lit 3287509502) (nat_lit 0) D2M8K2.u4618 from rfl, allE_node, arows4615, irow4619, arows4618]
  all_goals rfl

theorem atot4619 : totK PD2M8K2 D2M8K2.u4619 = [0, 0, 695597720785, 2883388681184, 3002503371427, 598384969821, 12097165849, 0] := by
  rw [show D2M8K2.u4619 = KTree.node D2M8K2.u4615 (nat_lit 10382656) (nat_lit 3287509502) (nat_lit 0) D2M8K2.u4618 from rfl, totK_node, atot4615, atot4618]
  decide +kernel

theorem arows4627 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4627 = true := by
  rw [show D2M8K2.u4627 = KTree.node D2M8K2.u4623 (nat_lit 10397156) (nat_lit 2792831110) (nat_lit 0) D2M8K2.u4626 from rfl, allE_node, arows4623, irow4627, arows4626]
  all_goals rfl

theorem atot4627 : totK PD2M8K2 D2M8K2.u4627 = [0, 0, 0, 1623714761504, 3775393477246, 1611577335140, 93200267753, 0] := by
  rw [show D2M8K2.u4627 = KTree.node D2M8K2.u4623 (nat_lit 10397156) (nat_lit 2792831110) (nat_lit 0) D2M8K2.u4626 from rfl, totK_node, atot4623, atot4626]
  decide +kernel

theorem arows4634 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4634 = true := by
  rw [show D2M8K2.u4634 = KTree.node D2M8K2.u4630 (nat_lit 10413401) (nat_lit 1700293131) (nat_lit 0) D2M8K2.u4633 from rfl, allE_node, arows4630, irow4634, arows4633]
  all_goals rfl

theorem atot4634 : totK PD2M8K2 D2M8K2.u4634 = [0, 0, 797685631964, 2709640457698, 2746313952952, 899527858159, 93911576245, 1394496256] := by
  rw [show D2M8K2.u4634 = KTree.node D2M8K2.u4630 (nat_lit 10413401) (nat_lit 1700293131) (nat_lit 0) D2M8K2.u4633 from rfl, totK_node, atot4630, atot4633]
  decide +kernel

theorem arows4643 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4643 = true := by
  rw [show D2M8K2.u4643 = KTree.node D2M8K2.u4639 (nat_lit 10419593) (nat_lit 1784557193) (nat_lit 0) D2M8K2.u4642 from rfl, allE_node, arows4639, irow4643, arows4642]
  all_goals rfl

theorem atot4643 : totK PD2M8K2 D2M8K2.u4643 = [0, 0, 979849938791, 3100102031986, 2673803875452, 543884834154, 16487985863, 0] := by
  rw [show D2M8K2.u4643 = KTree.node D2M8K2.u4639 (nat_lit 10419593) (nat_lit 1784557193) (nat_lit 0) D2M8K2.u4642 from rfl, totK_node, atot4639, atot4642]
  decide +kernel

theorem arows4650 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4650 = true := by
  rw [show D2M8K2.u4650 = KTree.node D2M8K2.u4646 (nat_lit 10451658) (nat_lit 3073000810) (nat_lit 0) D2M8K2.u4649 from rfl, allE_node, arows4646, irow4650, arows4649]
  all_goals rfl

theorem atot4650 : totK PD2M8K2 D2M8K2.u4650 = [0, 599936696520, 2132268700012, 2523233085898, 1539964401549, 403479921628, 18207879604, 0] := by
  rw [show D2M8K2.u4650 = KTree.node D2M8K2.u4646 (nat_lit 10451658) (nat_lit 3073000810) (nat_lit 0) D2M8K2.u4649 from rfl, totK_node, atot4646, atot4649]
  decide +kernel

theorem arows4658 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4658 = true := by
  rw [show D2M8K2.u4658 = KTree.node D2M8K2.u4654 (nat_lit 10465265) (nat_lit 1723839615) (nat_lit 0) D2M8K2.u4657 from rfl, allE_node, arows4654, irow4658, arows4657]
  all_goals rfl

theorem atot4658 : totK PD2M8K2 D2M8K2.u4658 = [0, 864731243707, 2971988619479, 2769981689671, 558026830710, 18231200220, 0, 0] := by
  rw [show D2M8K2.u4658 = KTree.node D2M8K2.u4654 (nat_lit 10465265) (nat_lit 1723839615) (nat_lit 0) D2M8K2.u4657 from rfl, totK_node, atot4654, atot4657]
  decide +kernel

theorem arows4665 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4665 = true := by
  rw [show D2M8K2.u4665 = KTree.node D2M8K2.u4661 (nat_lit 10472665) (nat_lit 1496130000) (nat_lit 0) D2M8K2.u4664 from rfl, allE_node, arows4661, irow4665, arows4664]
  all_goals rfl

theorem atot4665 : totK PD2M8K2 D2M8K2.u4665 = [0, 179036101606, 1687788661889, 3409322138892, 1685770845612, 150244870521, 1369150432, 0] := by
  rw [show D2M8K2.u4665 = KTree.node D2M8K2.u4661 (nat_lit 10472665) (nat_lit 1496130000) (nat_lit 0) D2M8K2.u4664 from rfl, totK_node, atot4661, atot4664]
  decide +kernel

theorem arows4675 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4675 = true := by
  rw [show D2M8K2.u4675 = KTree.node D2M8K2.u4671 (nat_lit 10489748) (nat_lit 2117098667) (nat_lit 0) D2M8K2.u4674 from rfl, allE_node, arows4671, irow4675, arows4674]
  all_goals rfl

theorem atot4675 : totK PD2M8K2 D2M8K2.u4675 = [0, 445106442645, 2143478693700, 3254497257274, 1319587376980, 78274981643, 0, 0] := by
  rw [show D2M8K2.u4675 = KTree.node D2M8K2.u4671 (nat_lit 10489748) (nat_lit 2117098667) (nat_lit 0) D2M8K2.u4674 from rfl, totK_node, atot4671, atot4674]
  decide +kernel

theorem arows4682 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4682 = true := by
  rw [show D2M8K2.u4682 = KTree.node D2M8K2.u4678 (nat_lit 10501465) (nat_lit 1141133420) (nat_lit 0) D2M8K2.u4681 from rfl, allE_node, arows4678, irow4682, arows4681]
  all_goals rfl

theorem atot4682 : totK PD2M8K2 D2M8K2.u4682 = [0, 773803482367, 2789348703394, 2931091263305, 802309470166, 30674758752, 0, 0] := by
  rw [show D2M8K2.u4682 = KTree.node D2M8K2.u4678 (nat_lit 10501465) (nat_lit 1141133420) (nat_lit 0) D2M8K2.u4681 from rfl, totK_node, atot4678, atot4681]
  decide +kernel

theorem arows4690 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4690 = true := by
  rw [show D2M8K2.u4690 = KTree.node D2M8K2.u4686 (nat_lit 10508291) (nat_lit 2664896153) (nat_lit 0) D2M8K2.u4689 from rfl, allE_node, arows4686, irow4690, arows4689]
  all_goals rfl

theorem atot4690 : totK PD2M8K2 D2M8K2.u4690 = [0, 829394532047, 2979519952218, 2850626286351, 587944148988, 18285006710, 0, 0] := by
  rw [show D2M8K2.u4690 = KTree.node D2M8K2.u4686 (nat_lit 10508291) (nat_lit 2664896153) (nat_lit 0) D2M8K2.u4689 from rfl, totK_node, atot4686, atot4689]
  decide +kernel

theorem arows4697 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4697 = true := by
  rw [show D2M8K2.u4697 = KTree.node D2M8K2.u4693 (nat_lit 10518665) (nat_lit 1794605220) (nat_lit 0) D2M8K2.u4696 from rfl, allE_node, arows4693, irow4697, arows4696]
  all_goals rfl

theorem atot4697 : totK PD2M8K2 D2M8K2.u4697 = [0, 0, 1083017554069, 3108428366847, 2445013367274, 628391822330, 36921873854, 0] := by
  rw [show D2M8K2.u4697 = KTree.node D2M8K2.u4693 (nat_lit 10518665) (nat_lit 1794605220) (nat_lit 0) D2M8K2.u4696 from rfl, totK_node, atot4693, atot4696]
  decide +kernel

theorem arows4706 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4706 = true := by
  rw [show D2M8K2.u4706 = KTree.node D2M8K2.u4702 (nat_lit 10525346) (nat_lit 2762252210) (nat_lit 0) D2M8K2.u4705 from rfl, allE_node, arows4702, irow4706, arows4705]
  all_goals rfl

theorem atot4706 : totK PD2M8K2 D2M8K2.u4706 = [0, 0, 836150852195, 3063715307070, 2820384796199, 499807850772, 10378741320, 0] := by
  rw [show D2M8K2.u4706 = KTree.node D2M8K2.u4702 (nat_lit 10525346) (nat_lit 2762252210) (nat_lit 0) D2M8K2.u4705 from rfl, totK_node, atot4702, atot4705]
  decide +kernel

theorem arows4713 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4713 = true := by
  rw [show D2M8K2.u4713 = KTree.node D2M8K2.u4709 (nat_lit 10532840) (nat_lit 3617431565) (nat_lit 0) D2M8K2.u4712 from rfl, allE_node, arows4709, irow4713, arows4712]
  all_goals rfl

theorem atot4713 : totK PD2M8K2 D2M8K2.u4713 = [0, 397564749128, 1618262439353, 2645652966079, 2099275619653, 435074996146, 10717512769, 0] := by
  rw [show D2M8K2.u4713 = KTree.node D2M8K2.u4709 (nat_lit 10532840) (nat_lit 3617431565) (nat_lit 0) D2M8K2.u4712 from rfl, totK_node, atot4709, atot4712]
  decide +kernel

theorem arows4721 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4721 = true := by
  rw [show D2M8K2.u4721 = KTree.node D2M8K2.u4717 (nat_lit 10581421) (nat_lit 1213519231) (nat_lit 0) D2M8K2.u4720 from rfl, allE_node, arows4717, irow4721, arows4720]
  all_goals rfl

theorem atot4721 : totK PD2M8K2 D2M8K2.u4721 = [0, 872994368376, 2956569444484, 2755057466236, 703678113919, 37536932523, 0, 0] := by
  rw [show D2M8K2.u4721 = KTree.node D2M8K2.u4717 (nat_lit 10581421) (nat_lit 1213519231) (nat_lit 0) D2M8K2.u4720 from rfl, totK_node, atot4717, atot4720]
  decide +kernel

theorem arows4728 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4728 = true := by
  rw [show D2M8K2.u4728 = KTree.node D2M8K2.u4724 (nat_lit 10590921) (nat_lit 1836876593) (nat_lit 0) D2M8K2.u4727 from rfl, allE_node, arows4724, irow4728, arows4727]
  all_goals rfl

theorem atot4728 : totK PD2M8K2 D2M8K2.u4728 = [0, 837001742390, 2948185272259, 2817720461675, 582575296473, 18231200220, 0, 0] := by
  rw [show D2M8K2.u4728 = KTree.node D2M8K2.u4724 (nat_lit 10590921) (nat_lit 1836876593) (nat_lit 0) D2M8K2.u4727 from rfl, totK_node, atot4724, atot4727]
  decide +kernel

theorem arows4739 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4739 = true := by
  rw [show D2M8K2.u4739 = KTree.node D2M8K2.u4735 (nat_lit 10597766) (nat_lit 2499652027) (nat_lit 0) D2M8K2.u4738 from rfl, allE_node, arows4735, irow4739, arows4738]
  all_goals rfl

theorem atot4739 : totK PD2M8K2 D2M8K2.u4739 = [0, 0, 1291953708297, 3561840493993, 2072614899214, 191443350706, 1239866073, 0] := by
  rw [show D2M8K2.u4739 = KTree.node D2M8K2.u4735 (nat_lit 10597766) (nat_lit 2499652027) (nat_lit 0) D2M8K2.u4738 from rfl, totK_node, atot4735, atot4738]
  decide +kernel

theorem arows4746 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4746 = true := by
  rw [show D2M8K2.u4746 = KTree.node D2M8K2.u4742 (nat_lit 10609978) (nat_lit 1786416063) (nat_lit 0) D2M8K2.u4745 from rfl, allE_node, arows4742, irow4746, arows4745]
  all_goals rfl

theorem atot4746 : totK PD2M8K2 D2M8K2.u4746 = [0, 0, 855165489284, 3050183152098, 2646529703174, 497253319348, 17826068843, 0] := by
  rw [show D2M8K2.u4746 = KTree.node D2M8K2.u4742 (nat_lit 10609978) (nat_lit 1786416063) (nat_lit 0) D2M8K2.u4745 from rfl, totK_node, atot4742, atot4745]
  decide +kernel

theorem arows4754 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4754 = true := by
  rw [show D2M8K2.u4754 = KTree.node D2M8K2.u4750 (nat_lit 10618542) (nat_lit 3755673942) (nat_lit 0) D2M8K2.u4753 from rfl, allE_node, arows4750, irow4754, arows4753]
  all_goals rfl

theorem atot4754 : totK PD2M8K2 D2M8K2.u4754 = [0, 796724878130, 2843128791453, 2797851409444, 775283268144, 50591429678, 0, 0] := by
  rw [show D2M8K2.u4754 = KTree.node D2M8K2.u4750 (nat_lit 10618542) (nat_lit 3755673942) (nat_lit 0) D2M8K2.u4753 from rfl, totK_node, atot4750, atot4753]
  decide +kernel

theorem arows4761 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4761 = true := by
  rw [show D2M8K2.u4761 = KTree.node D2M8K2.u4757 (nat_lit 10625809) (nat_lit 1213705439) (nat_lit 0) D2M8K2.u4760 from rfl, allE_node, arows4757, irow4761, arows4760]
  all_goals rfl

theorem atot4761 : totK PD2M8K2 D2M8K2.u4761 = [0, 750923452992, 2706592457694, 2858714494076, 866112670047, 43633803674, 0, 0] := by
  rw [show D2M8K2.u4761 = KTree.node D2M8K2.u4757 (nat_lit 10625809) (nat_lit 1213705439) (nat_lit 0) D2M8K2.u4760 from rfl, totK_node, atot4757, atot4760]
  decide +kernel

theorem arows4770 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4770 = true := by
  rw [show D2M8K2.u4770 = KTree.node D2M8K2.u4766 (nat_lit 10632600) (nat_lit 3462157730) (nat_lit 0) D2M8K2.u4769 from rfl, allE_node, arows4766, irow4770, arows4769]
  all_goals rfl

theorem atot4770 : totK PD2M8K2 D2M8K2.u4770 = [0, 435739754619, 2204843109032, 3170927303132, 1199119469070, 99228129434, 1138244013, 0] := by
  rw [show D2M8K2.u4770 = KTree.node D2M8K2.u4766 (nat_lit 10632600) (nat_lit 3462157730) (nat_lit 0) D2M8K2.u4769 from rfl, totK_node, atot4766, atot4769]
  decide +kernel

theorem arows4777 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4777 = true := by
  rw [show D2M8K2.u4777 = KTree.node D2M8K2.u4773 (nat_lit 10645312) (nat_lit 3289551508) (nat_lit 0) D2M8K2.u4776 from rfl, allE_node, arows4773, irow4777, arows4776]
  all_goals rfl

theorem atot4777 : totK PD2M8K2 D2M8K2.u4777 = [0, 0, 1420975041440, 3732110427234, 1931823034358, 134052927361, 0, 0] := by
  rw [show D2M8K2.u4777 = KTree.node D2M8K2.u4773 (nat_lit 10645312) (nat_lit 3289551508) (nat_lit 0) D2M8K2.u4776 from rfl, totK_node, atot4773, atot4776]
  decide +kernel

theorem arows4785 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4785 = true := by
  rw [show D2M8K2.u4785 = KTree.node D2M8K2.u4781 (nat_lit 10659467) (nat_lit 2634223692) (nat_lit 0) D2M8K2.u4784 from rfl, allE_node, arows4781, irow4785, arows4784]
  all_goals rfl

theorem atot4785 : totK PD2M8K2 D2M8K2.u4785 = [0, 744545921313, 2435906870671, 2575358014463, 1213488072682, 209195417434, 4977114383, 0] := by
  rw [show D2M8K2.u4785 = KTree.node D2M8K2.u4781 (nat_lit 10659467) (nat_lit 2634223692) (nat_lit 0) D2M8K2.u4784 from rfl, totK_node, atot4781, atot4784]
  decide +kernel

theorem arows4792 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4792 = true := by
  rw [show D2M8K2.u4792 = KTree.node D2M8K2.u4788 (nat_lit 10666066) (nat_lit 4093410283) (nat_lit 0) D2M8K2.u4791 from rfl, allE_node, arows4788, irow4792, arows4791]
  all_goals rfl

theorem atot4792 : totK PD2M8K2 D2M8K2.u4792 = [0, 810586241080, 2794816056855, 2833011625822, 835774387232, 45736792395, 0, 0] := by
  rw [show D2M8K2.u4792 = KTree.node D2M8K2.u4788 (nat_lit 10666066) (nat_lit 4093410283) (nat_lit 0) D2M8K2.u4791 from rfl, totK_node, atot4788, atot4791]
  decide +kernel

theorem arows4802 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4802 = true := by
  rw [show D2M8K2.u4802 = KTree.node D2M8K2.u4798 (nat_lit 10677056) (nat_lit 3109429099) (nat_lit 0) D2M8K2.u4801 from rfl, allE_node, arows4798, irow4802, arows4801]
  all_goals rfl

theorem atot4802 : totK PD2M8K2 D2M8K2.u4802 = [0, 440288014109, 2349559169216, 3319137277675, 1034406698909, 44647116226, 0, 0] := by
  rw [show D2M8K2.u4802 = KTree.node D2M8K2.u4798 (nat_lit 10677056) (nat_lit 3109429099) (nat_lit 0) D2M8K2.u4801 from rfl, totK_node, atot4798, atot4801]
  decide +kernel

theorem arows4809 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4809 = true := by
  rw [show D2M8K2.u4809 = KTree.node D2M8K2.u4805 (nat_lit 10684110) (nat_lit 3843012589) (nat_lit 0) D2M8K2.u4808 from rfl, allE_node, arows4805, irow4809, arows4808]
  all_goals rfl

theorem atot4809 : totK PD2M8K2 D2M8K2.u4809 = [0, 0, 1008360342712, 3316978274112, 2626645820956, 320711716167, 2745449626, 0] := by
  rw [show D2M8K2.u4809 = KTree.node D2M8K2.u4805 (nat_lit 10684110) (nat_lit 3843012589) (nat_lit 0) D2M8K2.u4808 from rfl, totK_node, atot4805, atot4808]
  decide +kernel

theorem arows4817 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4817 = true := by
  rw [show D2M8K2.u4817 = KTree.node D2M8K2.u4813 (nat_lit 10696965) (nat_lit 1380688449) (nat_lit 0) D2M8K2.u4816 from rfl, allE_node, arows4813, irow4817, arows4816]
  all_goals rfl

theorem atot4817 : totK PD2M8K2 D2M8K2.u4817 = [0, 0, 852547515370, 2960890575438, 2717544094353, 592301200105, 23015728707, 0] := by
  rw [show D2M8K2.u4817 = KTree.node D2M8K2.u4813 (nat_lit 10696965) (nat_lit 1380688449) (nat_lit 0) D2M8K2.u4816 from rfl, totK_node, atot4813, atot4816]
  decide +kernel

theorem arows4824 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4824 = true := by
  rw [show D2M8K2.u4824 = KTree.node D2M8K2.u4820 (nat_lit 10711124) (nat_lit 3665217836) (nat_lit 0) D2M8K2.u4823 from rfl, allE_node, arows4820, irow4824, arows4823]
  all_goals rfl

theorem atot4824 : totK PD2M8K2 D2M8K2.u4824 = [0, 0, 1077391125595, 3381342962936, 2406492317863, 256595480835, 2465655536, 0] := by
  rw [show D2M8K2.u4824 = KTree.node D2M8K2.u4820 (nat_lit 10711124) (nat_lit 3665217836) (nat_lit 0) D2M8K2.u4823 from rfl, totK_node, atot4820, atot4823]
  decide +kernel

theorem arows4833 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4833 = true := by
  rw [show D2M8K2.u4833 = KTree.node D2M8K2.u4829 (nat_lit 10745794) (nat_lit 3925838041) (nat_lit 0) D2M8K2.u4832 from rfl, allE_node, arows4829, irow4833, arows4832]
  all_goals rfl

theorem atot4833 : totK PD2M8K2 D2M8K2.u4833 = [0, 0, 951340493232, 2979776633889, 2678044776089, 690190134974, 37500007640, 0] := by
  rw [show D2M8K2.u4833 = KTree.node D2M8K2.u4829 (nat_lit 10745794) (nat_lit 3925838041) (nat_lit 0) D2M8K2.u4832 from rfl, totK_node, atot4829, atot4832]
  decide +kernel

theorem arows4840 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4840 = true := by
  rw [show D2M8K2.u4840 = KTree.node D2M8K2.u4836 (nat_lit 10752727) (nat_lit 2375701447) (nat_lit 0) D2M8K2.u4839 from rfl, allE_node, arows4836, irow4840, arows4839]
  all_goals rfl

theorem atot4840 : totK PD2M8K2 D2M8K2.u4840 = [0, 0, 900335232954, 3069810222652, 2729612936691, 555917621699, 14561142384, 0] := by
  rw [show D2M8K2.u4840 = KTree.node D2M8K2.u4836 (nat_lit 10752727) (nat_lit 2375701447) (nat_lit 0) D2M8K2.u4839 from rfl, totK_node, atot4836, atot4839]
  decide +kernel

theorem arows4848 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4848 = true := by
  rw [show D2M8K2.u4848 = KTree.node D2M8K2.u4844 (nat_lit 10759531) (nat_lit 1620840820) (nat_lit 0) D2M8K2.u4847 from rfl, allE_node, arows4844, irow4848, arows4847]
  all_goals rfl

theorem atot4848 : totK PD2M8K2 D2M8K2.u4848 = [0, 0, 902687305469, 3016196847086, 2724921587729, 575346496008, 16235932839, 0] := by
  rw [show D2M8K2.u4848 = KTree.node D2M8K2.u4844 (nat_lit 10759531) (nat_lit 1620840820) (nat_lit 0) D2M8K2.u4847 from rfl, totK_node, atot4844, atot4847]
  decide +kernel

theorem arows4855 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4855 = true := by
  rw [show D2M8K2.u4855 = KTree.node D2M8K2.u4851 (nat_lit 10829161) (nat_lit 1386289400) (nat_lit 0) D2M8K2.u4854 from rfl, allE_node, arows4851, irow4855, arows4854]
  all_goals rfl

theorem atot4855 : totK PD2M8K2 D2M8K2.u4855 = [0, 0, 779872063171, 2852416422566, 2862695311791, 712899986010, 31520323406, 0] := by
  rw [show D2M8K2.u4855 = KTree.node D2M8K2.u4851 (nat_lit 10829161) (nat_lit 1386289400) (nat_lit 0) D2M8K2.u4854 from rfl, totK_node, atot4851, atot4854]
  decide +kernel

theorem arows4867 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4867 = true := by
  rw [show D2M8K2.u4867 = KTree.node D2M8K2.u4863 (nat_lit 10838645) (nat_lit 2362644619) (nat_lit 0) D2M8K2.u4866 from rfl, allE_node, arows4863, irow4867, arows4866]
  all_goals rfl

theorem atot4867 : totK PD2M8K2 D2M8K2.u4867 = [0, 0, 825027495387, 2960778208754, 2797769587953, 564185266572, 18231200220, 0] := by
  rw [show D2M8K2.u4867 = KTree.node D2M8K2.u4863 (nat_lit 10838645) (nat_lit 2362644619) (nat_lit 0) D2M8K2.u4866 from rfl, totK_node, atot4863, atot4866]
  decide +kernel

theorem arows4874 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4874 = true := by
  rw [show D2M8K2.u4874 = KTree.node D2M8K2.u4870 (nat_lit 10846063) (nat_lit 2050546543) (nat_lit 512) D2M8K2.u4873 from rfl, allE_node, arows4870, irow4874, arows4873]
  all_goals rfl

theorem atot4874 : totK PD2M8K2 D2M8K2.u4874 = [0, 0, 182137505762, 1940272190821, 3626079065535, 1336457512007, 68253649309, 0] := by
  rw [show D2M8K2.u4874 = KTree.node D2M8K2.u4870 (nat_lit 10846063) (nat_lit 2050546543) (nat_lit 512) D2M8K2.u4873 from rfl, totK_node, atot4870, atot4873]
  decide +kernel

theorem arows4882 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4882 = true := by
  rw [show D2M8K2.u4882 = KTree.node D2M8K2.u4878 (nat_lit 10859574) (nat_lit 2835708951) (nat_lit 0) D2M8K2.u4881 from rfl, allE_node, arows4878, irow4882, arows4881]
  all_goals rfl

theorem atot4882 : totK PD2M8K2 D2M8K2.u4882 = [0, 0, 0, 1026861990627, 3296559237703, 2357062626428, 349231147874, 7105533120] := by
  rw [show D2M8K2.u4882 = KTree.node D2M8K2.u4878 (nat_lit 10859574) (nat_lit 2835708951) (nat_lit 0) D2M8K2.u4881 from rfl, totK_node, atot4878, atot4881]
  decide +kernel

theorem arows4889 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4889 = true := by
  rw [show D2M8K2.u4889 = KTree.node D2M8K2.u4885 (nat_lit 10869737) (nat_lit 1813608217) (nat_lit 0) D2M8K2.u4888 from rfl, allE_node, arows4885, irow4889, arows4888]
  all_goals rfl

theorem atot4889 : totK PD2M8K2 D2M8K2.u4889 = [0, 0, 901689708030, 3007625712393, 2677875578516, 609339192620, 25419901180, 0] := by
  rw [show D2M8K2.u4889 = KTree.node D2M8K2.u4885 (nat_lit 10869737) (nat_lit 1813608217) (nat_lit 0) D2M8K2.u4888 from rfl, totK_node, atot4885, atot4888]
  decide +kernel

theorem arows4898 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4898 = true := by
  rw [show D2M8K2.u4898 = KTree.node D2M8K2.u4894 (nat_lit 10877249) (nat_lit 2143832574) (nat_lit 0) D2M8K2.u4897 from rfl, allE_node, arows4894, irow4898, arows4897]
  all_goals rfl

theorem atot4898 : totK PD2M8K2 D2M8K2.u4898 = [0, 0, 907797251916, 3071225449612, 2699752333409, 499662237452, 14539166547, 0] := by
  rw [show D2M8K2.u4898 = KTree.node D2M8K2.u4894 (nat_lit 10877249) (nat_lit 2143832574) (nat_lit 0) D2M8K2.u4897 from rfl, totK_node, atot4894, atot4897]
  decide +kernel

theorem arows4905 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4905 = true := by
  rw [show D2M8K2.u4905 = KTree.node D2M8K2.u4901 (nat_lit 10887775) (nat_lit 2367182170) (nat_lit 0) D2M8K2.u4904 from rfl, allE_node, arows4901, irow4905, arows4904]
  all_goals rfl

theorem atot4905 : totK PD2M8K2 D2M8K2.u4905 = [0, 0, 167115188431, 2153695352236, 3662341787825, 1134323096579, 40808436318, 0] := by
  rw [show D2M8K2.u4905 = KTree.node D2M8K2.u4901 (nat_lit 10887775) (nat_lit 2367182170) (nat_lit 0) D2M8K2.u4904 from rfl, totK_node, atot4901, atot4904]
  decide +kernel

theorem arows4913 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4913 = true := by
  rw [show D2M8K2.u4913 = KTree.node D2M8K2.u4909 (nat_lit 10902533) (nat_lit 2327739443) (nat_lit 0) D2M8K2.u4912 from rfl, allE_node, arows4909, irow4913, arows4912]
  all_goals rfl

theorem atot4913 : totK PD2M8K2 D2M8K2.u4913 = [0, 0, 454235855139, 1982020134394, 3093518548873, 1425350990832, 136220171950, 1430229726] := by
  rw [show D2M8K2.u4913 = KTree.node D2M8K2.u4909 (nat_lit 10902533) (nat_lit 2327739443) (nat_lit 0) D2M8K2.u4912 from rfl, totK_node, atot4909, atot4912]
  decide +kernel

theorem arows4920 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4920 = true := by
  rw [show D2M8K2.u4920 = KTree.node D2M8K2.u4916 (nat_lit 10913832) (nat_lit 3239182337) (nat_lit 0) D2M8K2.u4919 from rfl, allE_node, arows4916, irow4920, arows4919]
  all_goals rfl

theorem atot4920 : totK PD2M8K2 D2M8K2.u4920 = [0, 0, 855590061285, 2916215841822, 2804083230091, 734816061916, 34305770152, 0] := by
  rw [show D2M8K2.u4920 = KTree.node D2M8K2.u4916 (nat_lit 10913832) (nat_lit 3239182337) (nat_lit 0) D2M8K2.u4919 from rfl, totK_node, atot4916, atot4919]
  decide +kernel

theorem arows4930 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4930 = true := by
  rw [show D2M8K2.u4930 = KTree.node D2M8K2.u4926 (nat_lit 10924952) (nat_lit 3120570072) (nat_lit 0) D2M8K2.u4929 from rfl, allE_node, arows4926, irow4930, arows4929]
  all_goals rfl

theorem atot4930 : totK PD2M8K2 D2M8K2.u4930 = [0, 91454885225, 889084615206, 2678928604692, 2815219700776, 729994166715, 27852771540, 0] := by
  rw [show D2M8K2.u4930 = KTree.node D2M8K2.u4926 (nat_lit 10924952) (nat_lit 3120570072) (nat_lit 0) D2M8K2.u4929 from rfl, totK_node, atot4926, atot4929]
  decide +kernel

theorem arows4937 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4937 = true := by
  rw [show D2M8K2.u4937 = KTree.node D2M8K2.u4933 (nat_lit 10955995) (nat_lit 1598303711) (nat_lit 0) D2M8K2.u4936 from rfl, allE_node, arows4933, irow4937, arows4936]
  all_goals rfl

theorem atot4937 : totK PD2M8K2 D2M8K2.u4937 = [0, 884740472709, 3054549625060, 2730574628124, 488857838181, 14418877666, 0, 0] := by
  rw [show D2M8K2.u4937 = KTree.node D2M8K2.u4933 (nat_lit 10955995) (nat_lit 1598303711) (nat_lit 0) D2M8K2.u4936 from rfl, totK_node, atot4933, atot4936]
  decide +kernel

theorem arows4945 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4945 = true := by
  rw [show D2M8K2.u4945 = KTree.node D2M8K2.u4941 (nat_lit 10962955) (nat_lit 1741892440) (nat_lit 0) D2M8K2.u4944 from rfl, allE_node, arows4941, irow4945, arows4944]
  all_goals rfl

theorem atot4945 : totK PD2M8K2 D2M8K2.u4945 = [0, 668131208094, 2727785558601, 3029921555268, 711399730939, 27842113783, 0, 0] := by
  rw [show D2M8K2.u4945 = KTree.node D2M8K2.u4941 (nat_lit 10962955) (nat_lit 1741892440) (nat_lit 0) D2M8K2.u4944 from rfl, totK_node, atot4941, atot4944]
  decide +kernel

theorem arows4952 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4952 = true := by
  rw [show D2M8K2.u4952 = KTree.node D2M8K2.u4948 (nat_lit 10977483) (nat_lit 1327919075) (nat_lit 0) D2M8K2.u4951 from rfl, allE_node, arows4948, irow4952, arows4951]
  all_goals rfl

theorem atot4952 : totK PD2M8K2 D2M8K2.u4952 = [0, 0, 1286987843881, 3670317291443, 1957880309783, 153494563365, 1369150432, 0] := by
  rw [show D2M8K2.u4952 = KTree.node D2M8K2.u4948 (nat_lit 10977483) (nat_lit 1327919075) (nat_lit 0) D2M8K2.u4951 from rfl, totK_node, atot4948, atot4951]
  decide +kernel

theorem arows4961 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4961 = true := by
  rw [show D2M8K2.u4961 = KTree.node D2M8K2.u4957 (nat_lit 10995828) (nat_lit 740315035) (nat_lit 0) D2M8K2.u4960 from rfl, allE_node, arows4957, irow4961, arows4960]
  all_goals rfl

theorem atot4961 : totK PD2M8K2 D2M8K2.u4961 = [0, 858866047482, 2791460469091, 2734689974414, 872540452355, 51484162708, 0, 0] := by
  rw [show D2M8K2.u4961 = KTree.node D2M8K2.u4957 (nat_lit 10995828) (nat_lit 740315035) (nat_lit 0) D2M8K2.u4960 from rfl, totK_node, atot4957, atot4960]
  decide +kernel

theorem arows4968 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4968 = true := by
  rw [show D2M8K2.u4968 = KTree.node D2M8K2.u4964 (nat_lit 11002044) (nat_lit 2589455329) (nat_lit 0) D2M8K2.u4967 from rfl, allE_node, arows4964, irow4968, arows4967]
  all_goals rfl

theorem atot4968 : totK PD2M8K2 D2M8K2.u4968 = [0, 804539462013, 2866772223246, 2878453928992, 665700699194, 26274535774, 0, 0] := by
  rw [show D2M8K2.u4968 = KTree.node D2M8K2.u4964 (nat_lit 11002044) (nat_lit 2589455329) (nat_lit 0) D2M8K2.u4967 from rfl, totK_node, atot4964, atot4967]
  decide +kernel

theorem arows4976 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4976 = true := by
  rw [show D2M8K2.u4976 = KTree.node D2M8K2.u4972 (nat_lit 11009466) (nat_lit 3895382182) (nat_lit 0) D2M8K2.u4975 from rfl, allE_node, arows4972, irow4976, arows4975]
  all_goals rfl

theorem atot4976 : totK PD2M8K2 D2M8K2.u4976 = [0, 378543555504, 2258276933893, 3385315706772, 1248916564292, 80353609028, 0, 0] := by
  rw [show D2M8K2.u4976 = KTree.node D2M8K2.u4972 (nat_lit 11009466) (nat_lit 3895382182) (nat_lit 0) D2M8K2.u4975 from rfl, totK_node, atot4972, atot4975]
  decide +kernel

theorem arows4983 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4983 = true := by
  rw [show D2M8K2.u4983 = KTree.node D2M8K2.u4979 (nat_lit 11019082) (nat_lit 3247204777) (nat_lit 0) D2M8K2.u4982 from rfl, allE_node, arows4979, irow4983, arows4982]
  all_goals rfl

theorem atot4983 : totK PD2M8K2 D2M8K2.u4983 = [0, 0, 777114088428, 2760570537935, 2850027823847, 794832795438, 42081742489, 0] := by
  rw [show D2M8K2.u4983 = KTree.node D2M8K2.u4979 (nat_lit 11019082) (nat_lit 3247204777) (nat_lit 0) D2M8K2.u4982 from rfl, totK_node, atot4979, atot4982]
  decide +kernel

theorem arows4994 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4994 = true := by
  rw [show D2M8K2.u4994 = KTree.node D2M8K2.u4990 (nat_lit 11025891) (nat_lit 3679374307) (nat_lit 0) D2M8K2.u4993 from rfl, allE_node, arows4990, irow4994, arows4993]
  all_goals rfl

theorem atot4994 : totK PD2M8K2 D2M8K2.u4994 = [0, 0, 819571158798, 3100594454849, 2899453201452, 472652427976, 6634014755, 0] := by
  rw [show D2M8K2.u4994 = KTree.node D2M8K2.u4990 (nat_lit 11025891) (nat_lit 3679374307) (nat_lit 0) D2M8K2.u4993 from rfl, totK_node, atot4990, atot4993]
  decide +kernel

theorem arows5001 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5001 = true := by
  rw [show D2M8K2.u5001 = KTree.node D2M8K2.u4997 (nat_lit 11034246) (nat_lit 3791869430) (nat_lit 0) D2M8K2.u5000 from rfl, allE_node, arows4997, irow5001, arows5000]
  all_goals rfl

theorem atot5001 : totK PD2M8K2 D2M8K2.u5001 = [0, 797183534328, 2653576478287, 2485717936291, 1039752204304, 245653605475, 9302370699, 0] := by
  rw [show D2M8K2.u5001 = KTree.node D2M8K2.u4997 (nat_lit 11034246) (nat_lit 3791869430) (nat_lit 0) D2M8K2.u5000 from rfl, totK_node, atot4997, atot5000]
  decide +kernel

theorem arows5009 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5009 = true := by
  rw [show D2M8K2.u5009 = KTree.node D2M8K2.u5005 (nat_lit 11040539) (nat_lit 2820249337) (nat_lit 0) D2M8K2.u5008 from rfl, allE_node, arows5005, irow5009, arows5008]
  all_goals rfl

theorem atot5009 : totK PD2M8K2 D2M8K2.u5009 = [0, 859573835446, 2894739981449, 2741339751532, 685011619232, 26353095110, 0, 0] := by
  rw [show D2M8K2.u5009 = KTree.node D2M8K2.u5005 (nat_lit 11040539) (nat_lit 2820249337) (nat_lit 0) D2M8K2.u5008 from rfl, totK_node, atot5005, atot5008]
  decide +kernel

theorem arows5016 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5016 = true := by
  rw [show D2M8K2.u5016 = KTree.node D2M8K2.u5012 (nat_lit 11051275) (nat_lit 1412180792) (nat_lit 0) D2M8K2.u5015 from rfl, allE_node, arows5012, irow5016, arows5015]
  all_goals rfl

theorem atot5016 : totK PD2M8K2 D2M8K2.u5016 = [0, 330025283572, 1927044647235, 3247488487084, 1505884485038, 129637149846, 1206465782, 0] := by
  rw [show D2M8K2.u5016 = KTree.node D2M8K2.u5012 (nat_lit 11051275) (nat_lit 1412180792) (nat_lit 0) D2M8K2.u5015 from rfl, totK_node, atot5012, atot5015]
  decide +kernel

theorem arows5025 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5025 = true := by
  rw [show D2M8K2.u5025 = KTree.node D2M8K2.u5021 (nat_lit 11060546) (nat_lit 3954947043) (nat_lit 0) D2M8K2.u5024 from rfl, allE_node, arows5021, irow5025, arows5024]
  all_goals rfl

theorem atot5025 : totK PD2M8K2 D2M8K2.u5025 = [0, 0, 1144308044835, 3347292752247, 2293942591958, 373853554498, 13016197374, 0] := by
  rw [show D2M8K2.u5025 = KTree.node D2M8K2.u5021 (nat_lit 11060546) (nat_lit 3954947043) (nat_lit 0) D2M8K2.u5024 from rfl, totK_node, atot5021, atot5024]
  decide +kernel

theorem arows5032 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5032 = true := by
  rw [show D2M8K2.u5032 = KTree.node D2M8K2.u5028 (nat_lit 11073097) (nat_lit 1519732958) (nat_lit 0) D2M8K2.u5031 from rfl, allE_node, arows5028, irow5032, arows5031]
  all_goals rfl

theorem atot5032 : totK PD2M8K2 D2M8K2.u5032 = [0, 536102949317, 2089258525620, 2851405543985, 1463157520799, 196400179124, 4574395652, 0] := by
  rw [show D2M8K2.u5032 = KTree.node D2M8K2.u5028 (nat_lit 11073097) (nat_lit 1519732958) (nat_lit 0) D2M8K2.u5031 from rfl, totK_node, atot5028, atot5031]
  decide +kernel

theorem arows5040 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5040 = true := by
  rw [show D2M8K2.u5040 = KTree.node D2M8K2.u5036 (nat_lit 11083484) (nat_lit 3335255375) (nat_lit 0) D2M8K2.u5039 from rfl, allE_node, arows5036, irow5040, arows5039]
  all_goals rfl

theorem atot5040 : totK PD2M8K2 D2M8K2.u5040 = [0, 699144977539, 2677971773725, 2931504227259, 911052337505, 50813180647, 0, 0] := by
  rw [show D2M8K2.u5040 = KTree.node D2M8K2.u5036 (nat_lit 11083484) (nat_lit 3335255375) (nat_lit 0) D2M8K2.u5039 from rfl, totK_node, atot5036, atot5039]
  decide +kernel

theorem arows5047 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5047 = true := by
  rw [show D2M8K2.u5047 = KTree.node D2M8K2.u5043 (nat_lit 11089944) (nat_lit 3226176481) (nat_lit 0) D2M8K2.u5046 from rfl, allE_node, arows5043, irow5047, arows5046]
  all_goals rfl

theorem atot5047 : totK PD2M8K2 D2M8K2.u5047 = [0, 752066519511, 2841163352453, 2932777190205, 676853884524, 23252149562, 0, 0] := by
  rw [show D2M8K2.u5047 = KTree.node D2M8K2.u5043 (nat_lit 11089944) (nat_lit 3226176481) (nat_lit 0) D2M8K2.u5046 from rfl, totK_node, atot5043, atot5046]
  decide +kernel

theorem arows5057 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5057 = true := by
  rw [show D2M8K2.u5057 = KTree.node D2M8K2.u5053 (nat_lit 11098299) (nat_lit 3452925158) (nat_lit 0) D2M8K2.u5056 from rfl, allE_node, arows5053, irow5057, arows5056]
  all_goals rfl

theorem atot5057 : totK PD2M8K2 D2M8K2.u5057 = [0, 0, 1108246849847, 3403690741754, 2377178689650, 271910079563, 2410950632, 0] := by
  rw [show D2M8K2.u5057 = KTree.node D2M8K2.u5053 (nat_lit 11098299) (nat_lit 3452925158) (nat_lit 0) D2M8K2.u5056 from rfl, totK_node, atot5053, atot5056]
  decide +kernel

theorem arows5064 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5064 = true := by
  rw [show D2M8K2.u5064 = KTree.node D2M8K2.u5060 (nat_lit 11109697) (nat_lit 1183962390) (nat_lit 0) D2M8K2.u5063 from rfl, allE_node, arows5060, irow5064, arows5063]
  all_goals rfl

theorem atot5064 : totK PD2M8K2 D2M8K2.u5064 = [0, 257732979108, 1329750682228, 2812594630317, 2252986910951, 426655579212, 16654984284, 0] := by
  rw [show D2M8K2.u5064 = KTree.node D2M8K2.u5060 (nat_lit 11109697) (nat_lit 1183962390) (nat_lit 0) D2M8K2.u5063 from rfl, totK_node, atot5060, atot5063]
  decide +kernel

theorem arows5072 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5072 = true := by
  rw [show D2M8K2.u5072 = KTree.node D2M8K2.u5068 (nat_lit 11119169) (nat_lit 2216843154) (nat_lit 0) D2M8K2.u5071 from rfl, allE_node, arows5068, irow5072, arows5071]
  all_goals rfl

theorem atot5072 : totK PD2M8K2 D2M8K2.u5072 = [0, 743109459900, 2782399514349, 2897756493942, 766983391686, 38928546222, 0, 0] := by
  rw [show D2M8K2.u5072 = KTree.node D2M8K2.u5068 (nat_lit 11119169) (nat_lit 2216843154) (nat_lit 0) D2M8K2.u5071 from rfl, totK_node, atot5068, atot5071]
  decide +kernel

theorem arows5079 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5079 = true := by
  rw [show D2M8K2.u5079 = KTree.node D2M8K2.u5075 (nat_lit 11125382) (nat_lit 3909376176) (nat_lit 0) D2M8K2.u5078 from rfl, allE_node, arows5075, irow5079, arows5078]
  all_goals rfl

theorem atot5079 : totK PD2M8K2 D2M8K2.u5079 = [0, 832331341262, 2878965148885, 2773218763061, 643471047991, 26300412495, 0, 0] := by
  rw [show D2M8K2.u5079 = KTree.node D2M8K2.u5075 (nat_lit 11125382) (nat_lit 3909376176) (nat_lit 0) D2M8K2.u5078 from rfl, totK_node, atot5075, atot5078]
  decide +kernel

theorem arows5088 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5088 = true := by
  rw [show D2M8K2.u5088 = KTree.node D2M8K2.u5084 (nat_lit 11135920) (nat_lit 3441116985) (nat_lit 0) D2M8K2.u5087 from rfl, allE_node, arows5084, irow5088, arows5087]
  all_goals rfl

theorem atot5088 : totK PD2M8K2 D2M8K2.u5088 = [0, 269119064056, 1878250774657, 3317552348621, 1514789105280, 145257439262, 1138244013, 0] := by
  rw [show D2M8K2.u5088 = KTree.node D2M8K2.u5084 (nat_lit 11135920) (nat_lit 3441116985) (nat_lit 0) D2M8K2.u5087 from rfl, totK_node, atot5084, atot5087]
  decide +kernel

theorem arows5095 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5095 = true := by
  rw [show D2M8K2.u5095 = KTree.node D2M8K2.u5091 (nat_lit 11146076) (nat_lit 3535497515) (nat_lit 0) D2M8K2.u5094 from rfl, allE_node, arows5091, irow5095, arows5094]
  all_goals rfl

theorem atot5095 : totK PD2M8K2 D2M8K2.u5095 = [0, 0, 1431970088642, 3761901754104, 1871860960440, 114088576446, 0, 0] := by
  rw [show D2M8K2.u5095 = KTree.node D2M8K2.u5091 (nat_lit 11146076) (nat_lit 3535497515) (nat_lit 0) D2M8K2.u5094 from rfl, totK_node, atot5091, atot5094]
  decide +kernel

theorem arows5103 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5103 = true := by
  rw [show D2M8K2.u5103 = KTree.node D2M8K2.u5099 (nat_lit 11199310) (nat_lit 3763380486) (nat_lit 0) D2M8K2.u5102 from rfl, allE_node, arows5099, irow5103, arows5102]
  all_goals rfl

theorem atot5103 : totK PD2M8K2 D2M8K2.u5103 = [0, 0, 819658120464, 3091354990157, 2799834164166, 410822540752, 7510584435, 0] := by
  rw [show D2M8K2.u5103 = KTree.node D2M8K2.u5099 (nat_lit 11199310) (nat_lit 3763380486) (nat_lit 0) D2M8K2.u5102 from rfl, totK_node, atot5099, atot5102]
  decide +kernel

theorem arows5110 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5110 = true := by
  rw [show D2M8K2.u5110 = KTree.node D2M8K2.u5106 (nat_lit 11211103) (nat_lit 2276198477) (nat_lit 0) D2M8K2.u5109 from rfl, allE_node, arows5106, irow5110, arows5109]
  all_goals rfl

theorem atot5110 : totK PD2M8K2 D2M8K2.u5110 = [0, 0, 913679457401, 3250700849276, 2730045373486, 296709442264, 2294578496, 0] := by
  rw [show D2M8K2.u5110 = KTree.node D2M8K2.u5106 (nat_lit 11211103) (nat_lit 2276198477) (nat_lit 0) D2M8K2.u5109 from rfl, totK_node, atot5106, atot5109]
  decide +kernel

theorem arows5124 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5124 = true := by
  rw [show D2M8K2.u5124 = KTree.node D2M8K2.u5120 (nat_lit 11245493) (nat_lit 2207012575) (nat_lit 0) D2M8K2.u5123 from rfl, allE_node, arows5120, irow5124, arows5123]
  all_goals rfl

theorem atot5124 : totK PD2M8K2 D2M8K2.u5124 = [0, 0, 763687698076, 2805611391674, 2877755022188, 804842177291, 44320128619, 0] := by
  rw [show D2M8K2.u5124 = KTree.node D2M8K2.u5120 (nat_lit 11245493) (nat_lit 2207012575) (nat_lit 0) D2M8K2.u5123 from rfl, totK_node, atot5120, atot5123]
  decide +kernel

theorem arows5131 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5131 = true := by
  rw [show D2M8K2.u5131 = KTree.node D2M8K2.u5127 (nat_lit 11252406) (nat_lit 3670938005) (nat_lit 0) D2M8K2.u5130 from rfl, allE_node, arows5127, irow5131, arows5130]
  all_goals rfl

theorem atot5131 : totK PD2M8K2 D2M8K2.u5131 = [0, 0, 837121645225, 3056806498943, 2839118604595, 524726072011, 11474941734, 0] := by
  rw [show D2M8K2.u5131 = KTree.node D2M8K2.u5127 (nat_lit 11252406) (nat_lit 3670938005) (nat_lit 0) D2M8K2.u5130 from rfl, totK_node, atot5127, atot5130]
  decide +kernel

theorem arows5139 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5139 = true := by
  rw [show D2M8K2.u5139 = KTree.node D2M8K2.u5135 (nat_lit 11280976) (nat_lit 3423385323) (nat_lit 0) D2M8K2.u5138 from rfl, allE_node, arows5135, irow5139, arows5138]
  all_goals rfl

theorem atot5139 : totK PD2M8K2 D2M8K2.u5139 = [0, 0, 950356907252, 3100597326112, 2713105576371, 487051020816, 13625741918, 0] := by
  rw [show D2M8K2.u5139 = KTree.node D2M8K2.u5135 (nat_lit 11280976) (nat_lit 3423385323) (nat_lit 0) D2M8K2.u5138 from rfl, totK_node, atot5135, atot5138]
  decide +kernel

theorem arows5146 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5146 = true := by
  rw [show D2M8K2.u5146 = KTree.node D2M8K2.u5142 (nat_lit 11287892) (nat_lit 3216006167) (nat_lit 0) D2M8K2.u5145 from rfl, allE_node, arows5142, irow5146, arows5145]
  all_goals rfl

theorem atot5146 : totK PD2M8K2 D2M8K2.u5146 = [0, 0, 800953947843, 2886363211282, 2851274604532, 701135114378, 28063716506, 0] := by
  rw [show D2M8K2.u5146 = KTree.node D2M8K2.u5142 (nat_lit 11287892) (nat_lit 3216006167) (nat_lit 0) D2M8K2.u5145 from rfl, totK_node, atot5142, atot5145]
  decide +kernel

theorem arows5155 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5155 = true := by
  rw [show D2M8K2.u5155 = KTree.node D2M8K2.u5151 (nat_lit 11298235) (nat_lit 1134316992) (nat_lit 0) D2M8K2.u5154 from rfl, allE_node, arows5151, irow5155, arows5154]
  all_goals rfl

theorem atot5155 : totK PD2M8K2 D2M8K2.u5155 = [0, 0, 957544354109, 3200175394724, 2647612085041, 410940664299, 6371641836, 0] := by
  rw [show D2M8K2.u5155 = KTree.node D2M8K2.u5151 (nat_lit 11298235) (nat_lit 1134316992) (nat_lit 0) D2M8K2.u5154 from rfl, totK_node, atot5151, atot5154]
  decide +kernel

theorem arows5162 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5162 = true := by
  rw [show D2M8K2.u5162 = KTree.node D2M8K2.u5158 (nat_lit 11327462) (nat_lit 4052209908) (nat_lit 0) D2M8K2.u5161 from rfl, allE_node, arows5158, irow5162, arows5161]
  all_goals rfl

theorem atot5162 : totK PD2M8K2 D2M8K2.u5162 = [0, 0, 857267677336, 3056116035343, 2836753550286, 550326771252, 16376849850, 0] := by
  rw [show D2M8K2.u5162 = KTree.node D2M8K2.u5158 (nat_lit 11327462) (nat_lit 4052209908) (nat_lit 0) D2M8K2.u5161 from rfl, totK_node, atot5158, atot5161]
  decide +kernel

theorem arows5170 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5170 = true := by
  rw [show D2M8K2.u5170 = KTree.node D2M8K2.u5166 (nat_lit 11336992) (nat_lit 2321430157) (nat_lit 0) D2M8K2.u5169 from rfl, allE_node, arows5166, irow5170, arows5169]
  all_goals rfl

theorem atot5170 : totK PD2M8K2 D2M8K2.u5170 = [0, 0, 751092424689, 2903079145006, 2943094403291, 605624970578, 18151190877, 0] := by
  rw [show D2M8K2.u5170 = KTree.node D2M8K2.u5166 (nat_lit 11336992) (nat_lit 2321430157) (nat_lit 0) D2M8K2.u5169 from rfl, totK_node, atot5166, atot5169]
  decide +kernel

theorem arows5177 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5177 = true := by
  rw [show D2M8K2.u5177 = KTree.node D2M8K2.u5173 (nat_lit 11366317) (nat_lit 1126510899) (nat_lit 0) D2M8K2.u5176 from rfl, allE_node, arows5173, irow5177, arows5176]
  all_goals rfl

theorem atot5177 : totK PD2M8K2 D2M8K2.u5177 = [0, 0, 819599820516, 2939039905653, 2788023115238, 594321595450, 25026805419, 0] := by
  rw [show D2M8K2.u5177 = KTree.node D2M8K2.u5173 (nat_lit 11366317) (nat_lit 1126510899) (nat_lit 0) D2M8K2.u5176 from rfl, totK_node, atot5173, atot5176]
  decide +kernel

theorem arows5187 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5187 = true := by
  rw [show D2M8K2.u5187 = KTree.node D2M8K2.u5183 (nat_lit 11372796) (nat_lit 2693120782) (nat_lit 0) D2M8K2.u5186 from rfl, allE_node, arows5183, irow5187, arows5186]
  all_goals rfl

theorem atot5187 : totK PD2M8K2 D2M8K2.u5187 = [0, 0, 833442042101, 2937192790236, 2797897199759, 568822523999, 16598325881, 0] := by
  rw [show D2M8K2.u5187 = KTree.node D2M8K2.u5183 (nat_lit 11372796) (nat_lit 2693120782) (nat_lit 0) D2M8K2.u5186 from rfl, totK_node, atot5183, atot5186]
  decide +kernel

theorem arows5194 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5194 = true := by
  rw [show D2M8K2.u5194 = KTree.node D2M8K2.u5190 (nat_lit 11379524) (nat_lit 3369024564) (nat_lit 0) D2M8K2.u5193 from rfl, allE_node, arows5190, irow5194, arows5193]
  all_goals rfl

theorem atot5194 : totK PD2M8K2 D2M8K2.u5194 = [0, 0, 443584338047, 2376565897952, 3296540975286, 990406296592, 45714175806, 0] := by
  rw [show D2M8K2.u5194 = KTree.node D2M8K2.u5190 (nat_lit 11379524) (nat_lit 3369024564) (nat_lit 0) D2M8K2.u5193 from rfl, totK_node, atot5190, atot5193]
  decide +kernel

theorem arows5202 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5202 = true := by
  rw [show D2M8K2.u5202 = KTree.node D2M8K2.u5198 (nat_lit 11395449) (nat_lit 1732667572) (nat_lit 0) D2M8K2.u5201 from rfl, allE_node, arows5198, irow5202, arows5201]
  all_goals rfl

theorem atot5202 : totK PD2M8K2 D2M8K2.u5202 = [0, 0, 0, 1413457183520, 3704022263440, 1838531337939, 135866844548, 0] := by
  rw [show D2M8K2.u5202 = KTree.node D2M8K2.u5198 (nat_lit 11395449) (nat_lit 1732667572) (nat_lit 0) D2M8K2.u5201 from rfl, totK_node, atot5198, atot5201]
  decide +kernel

theorem arows5209 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5209 = true := by
  rw [show D2M8K2.u5209 = KTree.node D2M8K2.u5205 (nat_lit 11449250) (nat_lit 3118659928) (nat_lit 0) D2M8K2.u5208 from rfl, allE_node, arows5205, irow5209, arows5208]
  all_goals rfl

theorem atot5209 : totK PD2M8K2 D2M8K2.u5209 = [0, 823190571224, 2899267794075, 2549917203455, 551524993625, 290009812356, 88149113051, 1493059870] := by
  rw [show D2M8K2.u5209 = KTree.node D2M8K2.u5205 (nat_lit 11449250) (nat_lit 3118659928) (nat_lit 0) D2M8K2.u5208 from rfl, totK_node, atot5205, atot5208]
  decide +kernel

theorem arows5218 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5218 = true := by
  rw [show D2M8K2.u5218 = KTree.node D2M8K2.u5214 (nat_lit 11463634) (nat_lit 3924280088) (nat_lit 0) D2M8K2.u5217 from rfl, allE_node, arows5214, irow5218, arows5217]
  all_goals rfl

theorem atot5218 : totK PD2M8K2 D2M8K2.u5218 = [0, 828007217789, 2946879842222, 2850541649204, 589955276007, 14166387570, 0, 0] := by
  rw [show D2M8K2.u5218 = KTree.node D2M8K2.u5214 (nat_lit 11463634) (nat_lit 3924280088) (nat_lit 0) D2M8K2.u5217 from rfl, totK_node, atot5214, atot5217]
  decide +kernel

theorem arows5225 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5225 = true := by
  rw [show D2M8K2.u5225 = KTree.node D2M8K2.u5221 (nat_lit 11474001) (nat_lit 1169649716) (nat_lit 512) D2M8K2.u5224 from rfl, allE_node, arows5221, irow5225, arows5224]
  all_goals rfl

theorem atot5225 : totK PD2M8K2 D2M8K2.u5225 = [0, 0, 1241481056243, 3572152722107, 2087234182607, 186923410684, 1369150432, 0] := by
  rw [show D2M8K2.u5225 = KTree.node D2M8K2.u5221 (nat_lit 11474001) (nat_lit 1169649716) (nat_lit 512) D2M8K2.u5224 from rfl, totK_node, atot5221, atot5224]
  decide +kernel

theorem arows5233 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5233 = true := by
  rw [show D2M8K2.u5233 = KTree.node D2M8K2.u5229 (nat_lit 11492356) (nat_lit 3479238390) (nat_lit 0) D2M8K2.u5232 from rfl, allE_node, arows5229, irow5233, arows5232]
  all_goals rfl

theorem atot5233 : totK PD2M8K2 D2M8K2.u5233 = [0, 601564969923, 2357446718698, 3045513174849, 1232791992445, 74942446546, 0, 0] := by
  rw [show D2M8K2.u5233 = KTree.node D2M8K2.u5229 (nat_lit 11492356) (nat_lit 3479238390) (nat_lit 0) D2M8K2.u5232 from rfl, totK_node, atot5229, atot5232]
  decide +kernel

theorem arows5240 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5240 = true := by
  rw [show D2M8K2.u5240 = KTree.node D2M8K2.u5236 (nat_lit 11498578) (nat_lit 3970467854) (nat_lit 0) D2M8K2.u5239 from rfl, allE_node, arows5236, irow5240, arows5239]
  all_goals rfl

theorem atot5240 : totK PD2M8K2 D2M8K2.u5240 = [0, 777719476136, 2864832935614, 2938791997947, 670137140356, 23385261119, 0, 0] := by
  rw [show D2M8K2.u5240 = KTree.node D2M8K2.u5236 (nat_lit 11498578) (nat_lit 3970467854) (nat_lit 0) D2M8K2.u5239 from rfl, totK_node, atot5236, atot5239]
  decide +kernel

theorem arows5251 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5251 = true := by
  rw [show D2M8K2.u5251 = KTree.node D2M8K2.u5247 (nat_lit 11505929) (nat_lit 1589236147) (nat_lit 0) D2M8K2.u5250 from rfl, allE_node, arows5247, irow5251, arows5250]
  all_goals rfl

theorem atot5251 : totK PD2M8K2 D2M8K2.u5251 = [0, 671280571781, 2693844419057, 3010396902738, 888708679689, 53076598243, 0, 0] := by
  rw [show D2M8K2.u5251 = KTree.node D2M8K2.u5247 (nat_lit 11505929) (nat_lit 1589236147) (nat_lit 0) D2M8K2.u5250 from rfl, totK_node, atot5247, atot5250]
  decide +kernel

theorem arows5258 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5258 = true := by
  rw [show D2M8K2.u5258 = KTree.node D2M8K2.u5254 (nat_lit 11515549) (nat_lit 1205972667) (nat_lit 0) D2M8K2.u5257 from rfl, allE_node, arows5254, irow5258, arows5257]
  all_goals rfl

theorem atot5258 : totK PD2M8K2 D2M8K2.u5258 = [0, 0, 773294002910, 2788430805733, 2850815723508, 787159719034, 42081742489, 0] := by
  rw [show D2M8K2.u5258 = KTree.node D2M8K2.u5254 (nat_lit 11515549) (nat_lit 1205972667) (nat_lit 0) D2M8K2.u5257 from rfl, totK_node, atot5254, atot5257]
  decide +kernel

theorem arows5266 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5266 = true := by
  rw [show D2M8K2.u5266 = KTree.node D2M8K2.u5262 (nat_lit 11522919) (nat_lit 3621750296) (nat_lit 0) D2M8K2.u5265 from rfl, allE_node, arows5262, irow5266, arows5265]
  all_goals rfl

theorem atot5266 : totK PD2M8K2 D2M8K2.u5266 = [0, 0, 959380283769, 3206888828110, 2718373440874, 432674816238, 6634014755, 0] := by
  rw [show D2M8K2.u5266 = KTree.node D2M8K2.u5262 (nat_lit 11522919) (nat_lit 3621750296) (nat_lit 0) D2M8K2.u5265 from rfl, totK_node, atot5262, atot5265]
  decide +kernel

theorem arows5273 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5273 = true := by
  rw [show D2M8K2.u5273 = KTree.node D2M8K2.u5269 (nat_lit 11530523) (nat_lit 1249659897) (nat_lit 0) D2M8K2.u5272 from rfl, allE_node, arows5269, irow5273, arows5272]
  all_goals rfl

theorem atot5273 : totK PD2M8K2 D2M8K2.u5273 = [0, 795345281950, 2441977880726, 2429900945057, 1265828158700, 293826002222, 9302370699, 0] := by
  rw [show D2M8K2.u5273 = KTree.node D2M8K2.u5269 (nat_lit 11530523) (nat_lit 1249659897) (nat_lit 0) D2M8K2.u5272 from rfl, totK_node, atot5269, atot5272]
  decide +kernel

theorem arows5282 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5282 = true := by
  rw [show D2M8K2.u5282 = KTree.node D2M8K2.u5278 (nat_lit 11536975) (nat_lit 1544377476) (nat_lit 0) D2M8K2.u5281 from rfl, allE_node, arows5278, irow5282, arows5281]
  all_goals rfl

theorem atot5282 : totK PD2M8K2 D2M8K2.u5282 = [0, 678845730202, 2645269957478, 2976938003485, 920047394479, 50610596126, 0, 0] := by
  rw [show D2M8K2.u5282 = KTree.node D2M8K2.u5278 (nat_lit 11536975) (nat_lit 1544377476) (nat_lit 0) D2M8K2.u5281 from rfl, totK_node, atot5278, atot5281]
  decide +kernel

theorem arows5289 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5289 = true := by
  rw [show D2M8K2.u5289 = KTree.node D2M8K2.u5285 (nat_lit 11548145) (nat_lit 1581600980) (nat_lit 0) D2M8K2.u5288 from rfl, allE_node, arows5285, irow5289, arows5288]
  all_goals rfl

theorem atot5289 : totK PD2M8K2 D2M8K2.u5289 = [0, 512866193935, 2493394188260, 3210911745612, 934105705982, 40746934634, 0, 0] := by
  rw [show D2M8K2.u5289 = KTree.node D2M8K2.u5285 (nat_lit 11548145) (nat_lit 1581600980) (nat_lit 0) D2M8K2.u5288 from rfl, totK_node, atot5285, atot5288]
  decide +kernel

theorem arows5297 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5297 = true := by
  rw [show D2M8K2.u5297 = KTree.node D2M8K2.u5293 (nat_lit 11557030) (nat_lit 2731372923) (nat_lit 0) D2M8K2.u5296 from rfl, allE_node, arows5293, irow5297, arows5296]
  all_goals rfl

theorem atot5297 : totK PD2M8K2 D2M8K2.u5297 = [0, 0, 922898116890, 3153287605627, 2631225803567, 436924900085, 10674011758, 0] := by
  rw [show D2M8K2.u5297 = KTree.node D2M8K2.u5293 (nat_lit 11557030) (nat_lit 2731372923) (nat_lit 0) D2M8K2.u5296 from rfl, totK_node, atot5293, atot5296]
  decide +kernel

theorem arows5304 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5304 = true := by
  rw [show D2M8K2.u5304 = KTree.node D2M8K2.u5300 (nat_lit 11568072) (nat_lit 3434090403) (nat_lit 0) D2M8K2.u5303 from rfl, allE_node, arows5300, irow5304, arows5303]
  all_goals rfl

theorem atot5304 : totK PD2M8K2 D2M8K2.u5304 = [0, 378914462040, 1925655532111, 3116553809592, 1608315720464, 157706408446, 1330264907, 0] := by
  rw [show D2M8K2.u5304 = KTree.node D2M8K2.u5300 (nat_lit 11568072) (nat_lit 3434090403) (nat_lit 0) D2M8K2.u5303 from rfl, totK_node, atot5300, atot5303]
  decide +kernel

theorem arows5314 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5314 = true := by
  rw [show D2M8K2.u5314 = KTree.node D2M8K2.u5310 (nat_lit 11576982) (nat_lit 3805491968) (nat_lit 0) D2M8K2.u5313 from rfl, allE_node, arows5310, irow5314, arows5313]
  all_goals rfl

theorem atot5314 : totK PD2M8K2 D2M8K2.u5314 = [0, 859109850115, 2895165209398, 2775352999867, 753417597428, 38757019681, 0, 0] := by
  rw [show D2M8K2.u5314 = KTree.node D2M8K2.u5310 (nat_lit 11576982) (nat_lit 3805491968) (nat_lit 0) D2M8K2.u5313 from rfl, totK_node, atot5310, atot5313]
  decide +kernel

theorem arows5321 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5321 = true := by
  rw [show D2M8K2.u5321 = KTree.node D2M8K2.u5317 (nat_lit 11587537) (nat_lit 1454138027) (nat_lit 0) D2M8K2.u5320 from rfl, allE_node, arows5317, irow5321, arows5320]
  all_goals rfl

theorem atot5321 : totK PD2M8K2 D2M8K2.u5321 = [0, 753772330983, 2857472907976, 2938260376153, 675217610986, 21966995249, 0, 0] := by
  rw [show D2M8K2.u5321 = KTree.node D2M8K2.u5317 (nat_lit 11587537) (nat_lit 1454138027) (nat_lit 0) D2M8K2.u5320 from rfl, totK_node, atot5317, atot5320]
  decide +kernel

theorem arows5329 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5329 = true := by
  rw [show D2M8K2.u5329 = KTree.node D2M8K2.u5325 (nat_lit 11595261) (nat_lit 1529907509) (nat_lit 0) D2M8K2.u5328 from rfl, allE_node, arows5325, irow5329, arows5328]
  all_goals rfl

theorem atot5329 : totK PD2M8K2 D2M8K2.u5329 = [0, 0, 1238365239541, 3546552006228, 2195779256667, 211612880049, 1239866073, 0] := by
  rw [show D2M8K2.u5329 = KTree.node D2M8K2.u5325 (nat_lit 11595261) (nat_lit 1529907509) (nat_lit 0) D2M8K2.u5328 from rfl, totK_node, atot5325, atot5328]
  decide +kernel

theorem arows5336 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5336 = true := by
  rw [show D2M8K2.u5336 = KTree.node D2M8K2.u5332 (nat_lit 11606627) (nat_lit 1583709010) (nat_lit 0) D2M8K2.u5335 from rfl, allE_node, arows5332, irow5336, arows5335]
  all_goals rfl

theorem atot5336 : totK PD2M8K2 D2M8K2.u5336 = [0, 121950136720, 1107597936647, 2994499311599, 2513282529728, 430315239797, 10903467235, 0] := by
  rw [show D2M8K2.u5336 = KTree.node D2M8K2.u5332 (nat_lit 11606627) (nat_lit 1583709010) (nat_lit 0) D2M8K2.u5335 from rfl, totK_node, atot5332, atot5335]
  decide +kernel

theorem arows5345 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5345 = true := by
  rw [show D2M8K2.u5345 = KTree.node D2M8K2.u5341 (nat_lit 11657913) (nat_lit 1730798329) (nat_lit 0) D2M8K2.u5344 from rfl, allE_node, arows5341, irow5345, arows5344]
  all_goals rfl

theorem atot5345 : totK PD2M8K2 D2M8K2.u5345 = [0, 787378990431, 2818759342410, 2847715851707, 754236775019, 38885768663, 0, 0] := by
  rw [show D2M8K2.u5345 = KTree.node D2M8K2.u5341 (nat_lit 11657913) (nat_lit 1730798329) (nat_lit 0) D2M8K2.u5344 from rfl, totK_node, atot5341, atot5344]
  decide +kernel

theorem arows5352 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5352 = true := by
  rw [show D2M8K2.u5352 = KTree.node D2M8K2.u5348 (nat_lit 11664108) (nat_lit 3173127261) (nat_lit 0) D2M8K2.u5351 from rfl, allE_node, arows5348, irow5352, arows5351]
  all_goals rfl

theorem atot5352 : totK PD2M8K2 D2M8K2.u5352 = [0, 774104878400, 2861736770225, 2881707761046, 657981724445, 23408478876, 0, 0] := by
  rw [show D2M8K2.u5352 = KTree.node D2M8K2.u5348 (nat_lit 11664108) (nat_lit 3173127261) (nat_lit 0) D2M8K2.u5351 from rfl, totK_node, atot5348, atot5351]
  decide +kernel

theorem arows5360 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5360 = true := by
  rw [show D2M8K2.u5360 = KTree.node D2M8K2.u5356 (nat_lit 11673773) (nat_lit 1538917808) (nat_lit 0) D2M8K2.u5359 from rfl, allE_node, arows5356, irow5360, arows5359]
  all_goals rfl

theorem atot5360 : totK PD2M8K2 D2M8K2.u5360 = [0, 429080094848, 1961729450639, 3055950333743, 1580877527559, 149318175187, 1310285577, 0] := by
  rw [show D2M8K2.u5360 = KTree.node D2M8K2.u5356 (nat_lit 11673773) (nat_lit 1538917808) (nat_lit 0) D2M8K2.u5359 from rfl, totK_node, atot5356, atot5359]
  decide +kernel

theorem arows5367 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5367 = true := by
  rw [show D2M8K2.u5367 = KTree.node D2M8K2.u5363 (nat_lit 11682530) (nat_lit 3892230770) (nat_lit 0) D2M8K2.u5366 from rfl, allE_node, arows5363, irow5367, arows5366]
  all_goals rfl

theorem atot5367 : totK PD2M8K2 D2M8K2.u5367 = [0, 0, 1177967911824, 3404093295846, 2318259897898, 292287135758, 4879840392, 0] := by
  rw [show D2M8K2.u5367 = KTree.node D2M8K2.u5363 (nat_lit 11682530) (nat_lit 3892230770) (nat_lit 0) D2M8K2.u5366 from rfl, totK_node, atot5363, atot5366]
  decide +kernel

theorem arows5379 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5379 = true := by
  rw [show D2M8K2.u5379 = KTree.node D2M8K2.u5375 (nat_lit 11693139) (nat_lit 3631486303) (nat_lit 0) D2M8K2.u5378 from rfl, allE_node, arows5375, irow5379, arows5378]
  all_goals rfl

theorem atot5379 : totK PD2M8K2 D2M8K2.u5379 = [0, 0, 837793809893, 2935837190210, 2725205319075, 605502608460, 26682572712, 0] := by
  rw [show D2M8K2.u5379 = KTree.node D2M8K2.u5375 (nat_lit 11693139) (nat_lit 3631486303) (nat_lit 0) D2M8K2.u5378 from rfl, totK_node, atot5375, atot5378]
  decide +kernel

theorem arows5386 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5386 = true := by
  rw [show D2M8K2.u5386 = KTree.node D2M8K2.u5382 (nat_lit 11703682) (nat_lit 3945797548) (nat_lit 0) D2M8K2.u5385 from rfl, allE_node, arows5382, irow5386, arows5385]
  all_goals rfl

theorem atot5386 : totK PD2M8K2 D2M8K2.u5386 = [0, 0, 1302152662079, 3548403393358, 2153372988220, 211213691644, 1369150432, 0] := by
  rw [show D2M8K2.u5386 = KTree.node D2M8K2.u5382 (nat_lit 11703682) (nat_lit 3945797548) (nat_lit 0) D2M8K2.u5385 from rfl, totK_node, atot5382, atot5385]
  decide +kernel

theorem arows5394 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5394 = true := by
  rw [show D2M8K2.u5394 = KTree.node D2M8K2.u5390 (nat_lit 11742725) (nat_lit 1697569177) (nat_lit 0) D2M8K2.u5393 from rfl, allE_node, arows5390, irow5394, arows5393]
  all_goals rfl

theorem atot5394 : totK PD2M8K2 D2M8K2.u5394 = [0, 0, 881513908384, 2947326461630, 2725635980977, 725324178735, 37500656948, 0] := by
  rw [show D2M8K2.u5394 = KTree.node D2M8K2.u5390 (nat_lit 11742725) (nat_lit 1697569177) (nat_lit 0) D2M8K2.u5393 from rfl, totK_node, atot5390, atot5393]
  decide +kernel

theorem arows5401 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5401 = true := by
  rw [show D2M8K2.u5401 = KTree.node D2M8K2.u5397 (nat_lit 11749574) (nat_lit 4118181002) (nat_lit 0) D2M8K2.u5400 from rfl, allE_node, arows5397, irow5401, arows5400]
  all_goals rfl

theorem atot5401 : totK PD2M8K2 D2M8K2.u5401 = [0, 0, 757094214637, 2933060265367, 2973677567786, 611753649999, 13240169684, 0] := by
  rw [show D2M8K2.u5401 = KTree.node D2M8K2.u5397 (nat_lit 11749574) (nat_lit 4118181002) (nat_lit 0) D2M8K2.u5400 from rfl, totK_node, atot5397, atot5400]
  decide +kernel

theorem arows5410 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5410 = true := by
  rw [show D2M8K2.u5410 = KTree.node D2M8K2.u5406 (nat_lit 11757044) (nat_lit 1799753168) (nat_lit 0) D2M8K2.u5409 from rfl, allE_node, arows5406, irow5410, arows5409]
  all_goals rfl

theorem atot5410 : totK PD2M8K2 D2M8K2.u5410 = [0, 0, 926663022511, 2959622142121, 2710407901813, 604787734393, 19050872497, 0] := by
  rw [show D2M8K2.u5410 = KTree.node D2M8K2.u5406 (nat_lit 11757044) (nat_lit 1799753168) (nat_lit 0) D2M8K2.u5409 from rfl, totK_node, atot5406, atot5409]
  decide +kernel

theorem arows5417 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5417 = true := by
  rw [show D2M8K2.u5417 = KTree.node D2M8K2.u5413 (nat_lit 11785016) (nat_lit 3688266149) (nat_lit 0) D2M8K2.u5416 from rfl, allE_node, arows5413, irow5417, arows5416]
  all_goals rfl

theorem atot5417 : totK PD2M8K2 D2M8K2.u5417 = [0, 0, 731670500972, 2731187643261, 2883950830754, 845797288630, 42248383843, 0] := by
  rw [show D2M8K2.u5417 = KTree.node D2M8K2.u5413 (nat_lit 11785016) (nat_lit 3688266149) (nat_lit 0) D2M8K2.u5416 from rfl, totK_node, atot5413, atot5416]
  decide +kernel

theorem arows5425 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5425 = true := by
  rw [show D2M8K2.u5425 = KTree.node D2M8K2.u5421 (nat_lit 11796048) (nat_lit 3669348837) (nat_lit 0) D2M8K2.u5424 from rfl, allE_node, arows5421, irow5425, arows5424]
  all_goals rfl

theorem atot5425 : totK PD2M8K2 D2M8K2.u5425 = [0, 0, 748124445496, 2781998598539, 2958211702691, 708706639890, 22121991658, 0] := by
  rw [show D2M8K2.u5425 = KTree.node D2M8K2.u5421 (nat_lit 11796048) (nat_lit 3669348837) (nat_lit 0) D2M8K2.u5424 from rfl, totK_node, atot5421, atot5424]
  decide +kernel

theorem arows5432 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5432 = true := by
  rw [show D2M8K2.u5432 = KTree.node D2M8K2.u5428 (nat_lit 11806900) (nat_lit 4012785417) (nat_lit 0) D2M8K2.u5431 from rfl, allE_node, arows5428, irow5432, arows5431]
  all_goals rfl

theorem atot5432 : totK PD2M8K2 D2M8K2.u5432 = [0, 0, 0, 1531254454274, 3652021762942, 1798376525159, 162562973725, 1501162176] := by
  rw [show D2M8K2.u5432 = KTree.node D2M8K2.u5428 (nat_lit 11806900) (nat_lit 4012785417) (nat_lit 0) D2M8K2.u5431 from rfl, totK_node, atot5428, atot5431]
  decide +kernel

theorem arows5442 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5442 = true := by
  rw [show D2M8K2.u5442 = KTree.node D2M8K2.u5438 (nat_lit 11822493) (nat_lit 1532090254) (nat_lit 0) D2M8K2.u5441 from rfl, allE_node, arows5438, irow5442, arows5441]
  all_goals rfl

theorem atot5442 : totK PD2M8K2 D2M8K2.u5442 = [0, 0, 796001692171, 2750118835561, 2817489150656, 841970908403, 47870224627, 0] := by
  rw [show D2M8K2.u5442 = KTree.node D2M8K2.u5438 (nat_lit 11822493) (nat_lit 1532090254) (nat_lit 0) D2M8K2.u5441 from rfl, totK_node, atot5438, atot5441]
  decide +kernel

theorem arows5449 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5449 = true := by
  rw [show D2M8K2.u5449 = KTree.node D2M8K2.u5445 (nat_lit 11832515) (nat_lit 2807666729) (nat_lit 0) D2M8K2.u5448 from rfl, allE_node, arows5445, irow5449, arows5448]
  all_goals rfl

theorem atot5449 : totK PD2M8K2 D2M8K2.u5449 = [0, 0, 840841629986, 2921769624847, 2829052015002, 640550421764, 19081622845, 0] := by
  rw [show D2M8K2.u5449 = KTree.node D2M8K2.u5445 (nat_lit 11832515) (nat_lit 2807666729) (nat_lit 0) D2M8K2.u5448 from rfl, totK_node, atot5445, atot5448]
  decide +kernel

theorem arows5457 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5457 = true := by
  rw [show D2M8K2.u5457 = KTree.node D2M8K2.u5453 (nat_lit 11840204) (nat_lit 919068221) (nat_lit 0) D2M8K2.u5456 from rfl, allE_node, arows5453, irow5457, arows5456]
  all_goals rfl

theorem atot5457 : totK PD2M8K2 D2M8K2.u5457 = [0, 0, 342011648963, 2297268163063, 3423602712629, 1095908230508, 43468781146, 0] := by
  rw [show D2M8K2.u5457 = KTree.node D2M8K2.u5453 (nat_lit 11840204) (nat_lit 919068221) (nat_lit 0) D2M8K2.u5456 from rfl, totK_node, atot5453, atot5456]
  decide +kernel

theorem arows5464 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5464 = true := by
  rw [show D2M8K2.u5464 = KTree.node D2M8K2.u5460 (nat_lit 11857606) (nat_lit 3731997504) (nat_lit 0) D2M8K2.u5463 from rfl, allE_node, arows5460, irow5464, arows5463]
  all_goals rfl

theorem atot5464 : totK PD2M8K2 D2M8K2.u5464 = [0, 0, 394317118174, 1914718595915, 3079754742431, 1605562812104, 161599192484, 1510868091] := by
  rw [show D2M8K2.u5464 = KTree.node D2M8K2.u5460 (nat_lit 11857606) (nat_lit 3731997504) (nat_lit 0) D2M8K2.u5463 from rfl, totK_node, atot5460, atot5463]
  decide +kernel

theorem arows5473 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5473 = true := by
  rw [show D2M8K2.u5473 = KTree.node D2M8K2.u5469 (nat_lit 11908061) (nat_lit 2234956051) (nat_lit 0) D2M8K2.u5472 from rfl, allE_node, arows5469, irow5473, arows5472]
  all_goals rfl

theorem atot5473 : totK PD2M8K2 D2M8K2.u5473 = [0, 0, 822836732652, 2858185969441, 2800068997642, 722678443907, 31776582721, 0] := by
  rw [show D2M8K2.u5473 = KTree.node D2M8K2.u5469 (nat_lit 11908061) (nat_lit 2234956051) (nat_lit 0) D2M8K2.u5472 from rfl, totK_node, atot5469, atot5472]
  decide +kernel

theorem arows5480 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5480 = true := by
  rw [show D2M8K2.u5480 = KTree.node D2M8K2.u5476 (nat_lit 11914395) (nat_lit 3642326178) (nat_lit 0) D2M8K2.u5479 from rfl, allE_node, arows5476, irow5480, arows5479]
  all_goals rfl

theorem atot5480 : totK PD2M8K2 D2M8K2.u5480 = [0, 0, 820238871706, 2948147889481, 2859962863220, 572778721552, 13024855736, 0] := by
  rw [show D2M8K2.u5480 = KTree.node D2M8K2.u5476 (nat_lit 11914395) (nat_lit 3642326178) (nat_lit 0) D2M8K2.u5479 from rfl, totK_node, atot5476, atot5479]
  decide +kernel

theorem arows5488 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5488 = true := by
  rw [show D2M8K2.u5488 = KTree.node D2M8K2.u5484 (nat_lit 11924666) (nat_lit 4018669560) (nat_lit 0) D2M8K2.u5487 from rfl, allE_node, arows5484, irow5488, arows5487]
  all_goals rfl

theorem atot5488 : totK PD2M8K2 D2M8K2.u5488 = [0, 0, 56835226932, 1778972863439, 3764640483743, 1465937184577, 75790338572, 0] := by
  rw [show D2M8K2.u5488 = KTree.node D2M8K2.u5484 (nat_lit 11924666) (nat_lit 4018669560) (nat_lit 0) D2M8K2.u5487 from rfl, totK_node, atot5484, atot5487]
  decide +kernel

theorem arows5495 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5495 = true := by
  rw [show D2M8K2.u5495 = KTree.node D2M8K2.u5491 (nat_lit 11935354) (nat_lit 3732324220) (nat_lit 0) D2M8K2.u5494 from rfl, allE_node, arows5491, irow5495, arows5494]
  all_goals rfl

theorem atot5495 : totK PD2M8K2 D2M8K2.u5495 = [0, 0, 0, 939718853480, 3368448738403, 2508000798759, 301127160648, 2822133622] := by
  rw [show D2M8K2.u5495 = KTree.node D2M8K2.u5491 (nat_lit 11935354) (nat_lit 3732324220) (nat_lit 0) D2M8K2.u5494 from rfl, totK_node, atot5491, atot5494]
  decide +kernel

theorem arows5506 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5506 = true := by
  rw [show D2M8K2.u5506 = KTree.node D2M8K2.u5502 (nat_lit 11945867) (nat_lit 2094083533) (nat_lit 0) D2M8K2.u5505 from rfl, allE_node, arows5502, irow5506, arows5505]
  all_goals rfl

theorem atot5506 : totK PD2M8K2 D2M8K2.u5506 = [863604381076, 2779792622823, 2172919135883, 297254354196, 250374937375, 617659404114, 235492752849, 10297110227] := by
  rw [show D2M8K2.u5506 = KTree.node D2M8K2.u5502 (nat_lit 11945867) (nat_lit 2094083533) (nat_lit 0) D2M8K2.u5505 from rfl, totK_node, atot5502, atot5505]
  decide +kernel

theorem arows5513 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5513 = true := by
  rw [show D2M8K2.u5513 = KTree.node D2M8K2.u5509 (nat_lit 11956436) (nat_lit 3637591942) (nat_lit 0) D2M8K2.u5512 from rfl, allE_node, arows5509, irow5513, arows5512]
  all_goals rfl

theorem atot5513 : totK PD2M8K2 D2M8K2.u5513 = [814154424544, 2855603996883, 2756091039425, 638768648238, 26232597979, 0, 0, 0] := by
  rw [show D2M8K2.u5513 = KTree.node D2M8K2.u5509 (nat_lit 11956436) (nat_lit 3637591942) (nat_lit 0) D2M8K2.u5512 from rfl, totK_node, atot5509, atot5512]
  decide +kernel

theorem arows5521 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5521 = true := by
  rw [show D2M8K2.u5521 = KTree.node D2M8K2.u5517 (nat_lit 11963289) (nat_lit 1268591649) (nat_lit 0) D2M8K2.u5520 from rfl, allE_node, arows5517, irow5521, arows5520]
  all_goals rfl

theorem atot5521 : totK PD2M8K2 D2M8K2.u5521 = [419234341778, 2240986349481, 3271361658948, 1134086035988, 62406777974, 0, 0, 0] := by
  rw [show D2M8K2.u5521 = KTree.node D2M8K2.u5517 (nat_lit 11963289) (nat_lit 1268591649) (nat_lit 0) D2M8K2.u5520 from rfl, totK_node, atot5517, atot5520]
  decide +kernel

theorem arows5528 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5528 = true := by
  rw [show D2M8K2.u5528 = KTree.node D2M8K2.u5524 (nat_lit 11975289) (nat_lit 1850068422) (nat_lit 0) D2M8K2.u5527 from rfl, allE_node, arows5524, irow5528, arows5527]
  all_goals rfl

theorem atot5528 : totK PD2M8K2 D2M8K2.u5528 = [0, 1232034327530, 3541926658950, 2078299340139, 202976034287, 1369150432, 0, 0] := by
  rw [show D2M8K2.u5528 = KTree.node D2M8K2.u5524 (nat_lit 11975289) (nat_lit 1850068422) (nat_lit 0) D2M8K2.u5527 from rfl, totK_node, atot5524, atot5527]
  decide +kernel

theorem arows5537 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5537 = true := by
  rw [show D2M8K2.u5537 = KTree.node D2M8K2.u5533 (nat_lit 12028249) (nat_lit 1404727685) (nat_lit 0) D2M8K2.u5536 from rfl, allE_node, arows5533, irow5537, arows5536]
  all_goals rfl

theorem atot5537 : totK PD2M8K2 D2M8K2.u5537 = [768819602542, 2823930069100, 2868757620918, 754622445067, 31102170454, 0, 0, 0] := by
  rw [show D2M8K2.u5537 = KTree.node D2M8K2.u5533 (nat_lit 12028249) (nat_lit 1404727685) (nat_lit 0) D2M8K2.u5536 from rfl, totK_node, atot5533, atot5536]
  decide +kernel

theorem arows5544 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5544 = true := by
  rw [show D2M8K2.u5544 = KTree.node D2M8K2.u5540 (nat_lit 12035370) (nat_lit 3593549233) (nat_lit 0) D2M8K2.u5543 from rfl, allE_node, arows5540, irow5544, arows5543]
  all_goals rfl

theorem atot5544 : totK PD2M8K2 D2M8K2.u5544 = [795828847061, 2754596911701, 2837396869600, 825389554482, 46367759598, 0, 0, 0] := by
  rw [show D2M8K2.u5544 = KTree.node D2M8K2.u5540 (nat_lit 12035370) (nat_lit 3593549233) (nat_lit 0) D2M8K2.u5543 from rfl, totK_node, atot5540, atot5543]
  decide +kernel

theorem arows5552 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5552 = true := by
  rw [show D2M8K2.u5552 = KTree.node D2M8K2.u5548 (nat_lit 12045734) (nat_lit 4024933322) (nat_lit 0) D2M8K2.u5551 from rfl, allE_node, arows5548, irow5552, arows5551]
  all_goals rfl

theorem atot5552 : totK PD2M8K2 D2M8K2.u5552 = [469810943695, 2402966963506, 3268311623682, 983053969707, 39128389862, 0, 0, 0] := by
  rw [show D2M8K2.u5552 = KTree.node D2M8K2.u5548 (nat_lit 12045734) (nat_lit 4024933322) (nat_lit 0) D2M8K2.u5551 from rfl, totK_node, atot5548, atot5551]
  decide +kernel

theorem arows5559 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5559 = true := by
  rw [show D2M8K2.u5559 = KTree.node D2M8K2.u5555 (nat_lit 12054679) (nat_lit 1630466065) (nat_lit 0) D2M8K2.u5558 from rfl, allE_node, arows5555, irow5559, arows5558]
  all_goals rfl

theorem atot5559 : totK PD2M8K2 D2M8K2.u5559 = [0, 907737841121, 3118447180394, 2645529138396, 459705358857, 14222663156, 0, 0] := by
  rw [show D2M8K2.u5559 = KTree.node D2M8K2.u5555 (nat_lit 12054679) (nat_lit 1630466065) (nat_lit 0) D2M8K2.u5558 from rfl, totK_node, atot5555, atot5558]
  decide +kernel

theorem arows5569 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5569 = true := by
  rw [show D2M8K2.u5569 = KTree.node D2M8K2.u5565 (nat_lit 12065217) (nat_lit 1552018831) (nat_lit 0) D2M8K2.u5568 from rfl, allE_node, arows5565, irow5569, arows5568]
  all_goals rfl

theorem atot5569 : totK PD2M8K2 D2M8K2.u5569 = [420970288622, 1817500878080, 2900761636305, 1748509289799, 219817454708, 4574395652, 0, 0] := by
  rw [show D2M8K2.u5569 = KTree.node D2M8K2.u5565 (nat_lit 12065217) (nat_lit 1552018831) (nat_lit 0) D2M8K2.u5568 from rfl, totK_node, atot5565, atot5568]
  decide +kernel

theorem arows5576 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5576 = true := by
  rw [show D2M8K2.u5576 = KTree.node D2M8K2.u5572 (nat_lit 12080512) (nat_lit 2722822718) (nat_lit 0) D2M8K2.u5575 from rfl, allE_node, arows5572, irow5576, arows5575]
  all_goals rfl

theorem atot5576 : totK PD2M8K2 D2M8K2.u5576 = [823857601559, 3002995324683, 2815948605920, 539732096756, 14619835693, 0, 0, 0] := by
  rw [show D2M8K2.u5576 = KTree.node D2M8K2.u5572 (nat_lit 12080512) (nat_lit 2722822718) (nat_lit 0) D2M8K2.u5575 from rfl, totK_node, atot5572, atot5575]
  decide +kernel

theorem arows5584 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5584 = true := by
  rw [show D2M8K2.u5584 = KTree.node D2M8K2.u5580 (nat_lit 12087497) (nat_lit 1554460371) (nat_lit 0) D2M8K2.u5583 from rfl, allE_node, arows5580, irow5584, arows5583]
  all_goals rfl

theorem atot5584 : totK PD2M8K2 D2M8K2.u5584 = [403614254217, 2234173347200, 3352551860645, 1120087959098, 50767129395, 0, 0, 0] := by
  rw [show D2M8K2.u5584 = KTree.node D2M8K2.u5580 (nat_lit 12087497) (nat_lit 1554460371) (nat_lit 0) D2M8K2.u5583 from rfl, totK_node, atot5580, atot5583]
  decide +kernel

theorem arows5591 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5591 = true := by
  rw [show D2M8K2.u5591 = KTree.node D2M8K2.u5587 (nat_lit 12101428) (nat_lit 2680090386) (nat_lit 0) D2M8K2.u5590 from rfl, allE_node, arows5587, irow5591, arows5590]
  all_goals rfl

theorem atot5591 : totK PD2M8K2 D2M8K2.u5591 = [0, 819897653915, 2990379536841, 2719348240762, 492572052005, 15398727635, 0, 0] := by
  rw [show D2M8K2.u5591 = KTree.node D2M8K2.u5587 (nat_lit 12101428) (nat_lit 2680090386) (nat_lit 0) D2M8K2.u5590 from rfl, totK_node, atot5587, atot5590]
  decide +kernel

theorem arows5600 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5600 = true := by
  rw [show D2M8K2.u5600 = KTree.node D2M8K2.u5596 (nat_lit 12110550) (nat_lit 2742033902) (nat_lit 0) D2M8K2.u5599 from rfl, allE_node, arows5596, irow5600, arows5599]
  all_goals rfl

theorem atot5600 : totK PD2M8K2 D2M8K2.u5600 = [592007481171, 2329666007993, 2850617630842, 1245630091003, 153099002483, 3667207281, 0, 0] := by
  rw [show D2M8K2.u5600 = KTree.node D2M8K2.u5596 (nat_lit 12110550) (nat_lit 2742033902) (nat_lit 0) D2M8K2.u5599 from rfl, totK_node, atot5596, atot5599]
  decide +kernel

theorem arows5607 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5607 = true := by
  rw [show D2M8K2.u5607 = KTree.node D2M8K2.u5603 (nat_lit 12117564) (nat_lit 2754251298) (nat_lit 0) D2M8K2.u5606 from rfl, allE_node, arows5603, irow5607, arows5606]
  all_goals rfl

theorem atot5607 : totK PD2M8K2 D2M8K2.u5607 = [806515067320, 2793785295047, 2785610226366, 792664294794, 43750249110, 0, 0, 0] := by
  rw [show D2M8K2.u5607 = KTree.node D2M8K2.u5603 (nat_lit 12117564) (nat_lit 2754251298) (nat_lit 0) D2M8K2.u5606 from rfl, totK_node, atot5603, atot5606]
  decide +kernel

theorem arows5615 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5615 = true := by
  rw [show D2M8K2.u5615 = KTree.node D2M8K2.u5611 (nat_lit 12124523) (nat_lit 2654669801) (nat_lit 0) D2M8K2.u5614 from rfl, allE_node, arows5611, irow5615, arows5614]
  all_goals rfl

theorem atot5615 : totK PD2M8K2 D2M8K2.u5615 = [575779815503, 2569052383594, 3103018721174, 841813982205, 36492763016, 0, 0, 0] := by
  rw [show D2M8K2.u5615 = KTree.node D2M8K2.u5611 (nat_lit 12124523) (nat_lit 2654669801) (nat_lit 0) D2M8K2.u5614 from rfl, totK_node, atot5611, atot5614]
  decide +kernel

theorem arows5622 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5622 = true := by
  rw [show D2M8K2.u5622 = KTree.node D2M8K2.u5618 (nat_lit 12137584) (nat_lit 3388048083) (nat_lit 0) D2M8K2.u5621 from rfl, allE_node, arows5618, irow5622, arows5621]
  all_goals rfl

theorem atot5622 : totK PD2M8K2 D2M8K2.u5622 = [0, 1259554600403, 3602585873078, 2093532634584, 183944102213, 1138244013, 0, 0] := by
  rw [show D2M8K2.u5622 = KTree.node D2M8K2.u5618 (nat_lit 12137584) (nat_lit 3388048083) (nat_lit 0) D2M8K2.u5621 from rfl, totK_node, atot5618, atot5621]
  decide +kernel

theorem arows5635 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5635 = true := by
  rw [show D2M8K2.u5635 = KTree.node D2M8K2.u5631 (nat_lit 12147510) (nat_lit 3571249101) (nat_lit 0) D2M8K2.u5634 from rfl, allE_node, arows5631, irow5635, arows5634]
  all_goals rfl

theorem atot5635 : totK PD2M8K2 D2M8K2.u5635 = [500825967538, 2038404494292, 2842736708300, 1498652160413, 228771927981, 4977114383, 0, 0] := by
  rw [show D2M8K2.u5635 = KTree.node D2M8K2.u5631 (nat_lit 12147510) (nat_lit 3571249101) (nat_lit 0) D2M8K2.u5634 from rfl, totK_node, atot5631, atot5634]
  decide +kernel

theorem arows5642 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5642 = true := by
  rw [show D2M8K2.u5642 = KTree.node D2M8K2.u5638 (nat_lit 12158561) (nat_lit 2212966594) (nat_lit 0) D2M8K2.u5641 from rfl, allE_node, arows5638, irow5642, arows5641]
  all_goals rfl

theorem atot5642 : totK PD2M8K2 D2M8K2.u5642 = [766009661152, 2772295647332, 2863881897247, 824825312147, 47877483080, 0, 0, 0] := by
  rw [show D2M8K2.u5642 = KTree.node D2M8K2.u5638 (nat_lit 12158561) (nat_lit 2212966594) (nat_lit 0) D2M8K2.u5641 from rfl, totK_node, atot5638, atot5641]
  decide +kernel

theorem arows5650 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5650 = true := by
  rw [show D2M8K2.u5650 = KTree.node D2M8K2.u5646 (nat_lit 12168984) (nat_lit 3029888638) (nat_lit 0) D2M8K2.u5649 from rfl, allE_node, arows5646, irow5650, arows5649]
  all_goals rfl

theorem atot5650 : totK PD2M8K2 D2M8K2.u5650 = [718275913541, 2736168373768, 2934908496407, 781800356058, 35292564006, 0, 0, 0] := by
  rw [show D2M8K2.u5650 = KTree.node D2M8K2.u5646 (nat_lit 12168984) (nat_lit 3029888638) (nat_lit 0) D2M8K2.u5649 from rfl, totK_node, atot5646, atot5649]
  decide +kernel

theorem arows5657 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5657 = true := by
  rw [show D2M8K2.u5657 = KTree.node D2M8K2.u5653 (nat_lit 12176030) (nat_lit 3831962033) (nat_lit 0) D2M8K2.u5656 from rfl, allE_node, arows5653, irow5657, arows5656]
  all_goals rfl

theorem atot5657 : totK PD2M8K2 D2M8K2.u5657 = [0, 1126257853301, 3426414821502, 2387366302526, 251049667430, 2385942608, 0, 0] := by
  rw [show D2M8K2.u5657 = KTree.node D2M8K2.u5653 (nat_lit 12176030) (nat_lit 3831962033) (nat_lit 0) D2M8K2.u5656 from rfl, totK_node, atot5653, atot5656]
  decide +kernel

theorem arows5666 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5666 = true := by
  rw [show D2M8K2.u5666 = KTree.node D2M8K2.u5662 (nat_lit 12185032) (nat_lit 1678963321) (nat_lit 0) D2M8K2.u5665 from rfl, allE_node, arows5662, irow5666, arows5665]
  all_goals rfl

theorem atot5666 : totK PD2M8K2 D2M8K2.u5666 = [0, 818734381502, 3009704995703, 2806788981365, 494623466768, 9977726607, 0, 0] := by
  rw [show D2M8K2.u5666 = KTree.node D2M8K2.u5662 (nat_lit 12185032) (nat_lit 1678963321) (nat_lit 0) D2M8K2.u5665 from rfl, totK_node, atot5662, atot5665]
  decide +kernel

theorem arows5673 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5673 = true := by
  rw [show D2M8K2.u5673 = KTree.node D2M8K2.u5669 (nat_lit 12194740) (nat_lit 3330597007) (nat_lit 0) D2M8K2.u5672 from rfl, allE_node, arows5669, irow5673, arows5672]
  all_goals rfl

theorem atot5673 : totK PD2M8K2 D2M8K2.u5673 = [0, 859829644001, 2995462789727, 2731469523687, 562966901421, 23042499518, 0, 0] := by
  rw [show D2M8K2.u5673 = KTree.node D2M8K2.u5669 (nat_lit 12194740) (nat_lit 3330597007) (nat_lit 0) D2M8K2.u5672 from rfl, totK_node, atot5669, atot5672]
  decide +kernel

theorem arows5681 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5681 = true := by
  rw [show D2M8K2.u5681 = KTree.node D2M8K2.u5677 (nat_lit 12205748) (nat_lit 3065378814) (nat_lit 0) D2M8K2.u5680 from rfl, allE_node, arows5677, irow5681, arows5680]
  all_goals rfl

theorem atot5681 : totK PD2M8K2 D2M8K2.u5681 = [0, 810037223220, 2865795122645, 2756300645107, 572415460205, 25916223298, 0, 0] := by
  rw [show D2M8K2.u5681 = KTree.node D2M8K2.u5677 (nat_lit 12205748) (nat_lit 3065378814) (nat_lit 0) D2M8K2.u5680 from rfl, totK_node, atot5677, atot5680]
  decide +kernel

theorem arows5688 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5688 = true := by
  rw [show D2M8K2.u5688 = KTree.node D2M8K2.u5684 (nat_lit 12212382) (nat_lit 2245188179) (nat_lit 0) D2M8K2.u5687 from rfl, allE_node, arows5684, irow5688, arows5687]
  all_goals rfl

theorem atot5688 : totK PD2M8K2 D2M8K2.u5688 = [0, 417509408390, 2173102568951, 3193402094808, 1166224261131, 107596616703, 1369150432, 0] := by
  rw [show D2M8K2.u5688 = KTree.node D2M8K2.u5684 (nat_lit 12212382) (nat_lit 2245188179) (nat_lit 0) D2M8K2.u5687 from rfl, totK_node, atot5684, atot5687]
  decide +kernel

theorem arows5698 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5698 = true := by
  rw [show D2M8K2.u5698 = KTree.node D2M8K2.u5694 (nat_lit 12224898) (nat_lit 3311549997) (nat_lit 0) D2M8K2.u5697 from rfl, allE_node, arows5694, irow5698, arows5697]
  all_goals rfl

theorem atot5698 : totK PD2M8K2 D2M8K2.u5698 = [0, 0, 1452280074999, 3667919097006, 1720214285855, 150081089032, 0, 0] := by
  rw [show D2M8K2.u5698 = KTree.node D2M8K2.u5694 (nat_lit 12224898) (nat_lit 3311549997) (nat_lit 0) D2M8K2.u5697 from rfl, totK_node, atot5694, atot5697]
  decide +kernel

theorem arows5705 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5705 = true := by
  rw [show D2M8K2.u5705 = KTree.node D2M8K2.u5701 (nat_lit 12278075) (nat_lit 2766824521) (nat_lit 0) D2M8K2.u5704 from rfl, allE_node, arows5701, irow5705, arows5704]
  all_goals rfl

theorem atot5705 : totK PD2M8K2 D2M8K2.u5705 = [0, 766109221512, 2840481051137, 2890849117473, 673710117185, 27708813079, 0, 0] := by
  rw [show D2M8K2.u5705 = KTree.node D2M8K2.u5701 (nat_lit 12278075) (nat_lit 2766824521) (nat_lit 0) D2M8K2.u5704 from rfl, totK_node, atot5701, atot5704]
  decide +kernel

theorem arows5713 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5713 = true := by
  rw [show D2M8K2.u5713 = KTree.node D2M8K2.u5709 (nat_lit 12285653) (nat_lit 2189044531) (nat_lit 0) D2M8K2.u5712 from rfl, allE_node, arows5709, irow5713, arows5712]
  all_goals rfl

theorem atot5713 : totK PD2M8K2 D2M8K2.u5713 = [0, 849032166629, 3039981597491, 2815427593620, 499753943866, 14146232338, 0, 0] := by
  rw [show D2M8K2.u5713 = KTree.node D2M8K2.u5709 (nat_lit 12285653) (nat_lit 2189044531) (nat_lit 0) D2M8K2.u5712 from rfl, totK_node, atot5709, atot5712]
  decide +kernel

theorem arows5720 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5720 = true := by
  rw [show D2M8K2.u5720 = KTree.node D2M8K2.u5716 (nat_lit 12296220) (nat_lit 3055663350) (nat_lit 0) D2M8K2.u5719 from rfl, allE_node, arows5716, irow5720, arows5719]
  all_goals rfl

theorem atot5720 : totK PD2M8K2 D2M8K2.u5720 = [0, 833357092312, 2954638744971, 2793939388804, 572011507375, 18874216992, 0, 0] := by
  rw [show D2M8K2.u5720 = KTree.node D2M8K2.u5716 (nat_lit 12296220) (nat_lit 3055663350) (nat_lit 0) D2M8K2.u5719 from rfl, totK_node, atot5716, atot5719]
  decide +kernel

theorem arows5729 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5729 = true := by
  rw [show D2M8K2.u5729 = KTree.node D2M8K2.u5725 (nat_lit 12330726) (nat_lit 3792361165) (nat_lit 0) D2M8K2.u5728 from rfl, allE_node, arows5725, irow5729, arows5728]
  all_goals rfl

theorem atot5729 : totK PD2M8K2 D2M8K2.u5729 = [0, 840538313572, 2949390619978, 2791681886499, 561108027420, 18088360733, 0, 0] := by
  rw [show D2M8K2.u5729 = KTree.node D2M8K2.u5725 (nat_lit 12330726) (nat_lit 3792361165) (nat_lit 0) D2M8K2.u5728 from rfl, totK_node, atot5725, atot5728]
  decide +kernel

theorem arows5736 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5736 = true := by
  rw [show D2M8K2.u5736 = KTree.node D2M8K2.u5732 (nat_lit 12358664) (nat_lit 3626183552) (nat_lit 0) D2M8K2.u5735 from rfl, allE_node, arows5732, irow5736, arows5735]
  all_goals rfl

theorem atot5736 : totK PD2M8K2 D2M8K2.u5736 = [0, 890207537929, 3042259396298, 2712339006386, 514541694000, 15083816312, 0, 0] := by
  rw [show D2M8K2.u5736 = KTree.node D2M8K2.u5732 (nat_lit 12358664) (nat_lit 3626183552) (nat_lit 0) D2M8K2.u5735 from rfl, totK_node, atot5732, atot5735]
  decide +kernel

theorem arows5744 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5744 = true := by
  rw [show D2M8K2.u5744 = KTree.node D2M8K2.u5740 (nat_lit 12366340) (nat_lit 4054154634) (nat_lit 0) D2M8K2.u5743 from rfl, allE_node, arows5740, irow5744, arows5743]
  all_goals rfl

theorem atot5744 : totK PD2M8K2 D2M8K2.u5744 = [0, 892774672681, 3060231007665, 2749846238763, 502707012571, 14393010609, 0, 0] := by
  rw [show D2M8K2.u5744 = KTree.node D2M8K2.u5740 (nat_lit 12366340) (nat_lit 4054154634) (nat_lit 0) D2M8K2.u5743 from rfl, totK_node, atot5740, atot5743]
  decide +kernel

theorem arows5751 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5751 = true := by
  rw [show D2M8K2.u5751 = KTree.node D2M8K2.u5747 (nat_lit 12373360) (nat_lit 2590991521) (nat_lit 0) D2M8K2.u5750 from rfl, allE_node, arows5747, irow5751, arows5750]
  all_goals rfl

theorem atot5751 : totK PD2M8K2 D2M8K2.u5751 = [0, 852761696873, 2982465241159, 2742800765401, 534234304086, 18164832359, 0, 0] := by
  rw [show D2M8K2.u5751 = KTree.node D2M8K2.u5747 (nat_lit 12373360) (nat_lit 2590991521) (nat_lit 0) D2M8K2.u5750 from rfl, totK_node, atot5747, atot5750]
  decide +kernel

theorem arows5762 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5762 = true := by
  rw [show D2M8K2.u5762 = KTree.node D2M8K2.u5758 (nat_lit 12405220) (nat_lit 4000457553) (nat_lit 0) D2M8K2.u5761 from rfl, allE_node, arows5758, irow5762, arows5761]
  all_goals rfl

theorem atot5762 : totK PD2M8K2 D2M8K2.u5762 = [0, 886971109989, 3062744986428, 2794218100304, 522983322994, 10944778055, 0, 0] := by
  rw [show D2M8K2.u5762 = KTree.node D2M8K2.u5758 (nat_lit 12405220) (nat_lit 4000457553) (nat_lit 0) D2M8K2.u5761 from rfl, totK_node, atot5758, atot5761]
  decide +kernel

theorem arows5769 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5769 = true := by
  rw [show D2M8K2.u5769 = KTree.node D2M8K2.u5765 (nat_lit 12412447) (nat_lit 2375047654) (nat_lit 0) D2M8K2.u5768 from rfl, allE_node, arows5765, irow5769, arows5768]
  all_goals rfl

theorem atot5769 : totK PD2M8K2 D2M8K2.u5769 = [0, 820841064491, 2958316956681, 2881766244822, 554115590309, 11581480607, 0, 0] := by
  rw [show D2M8K2.u5769 = KTree.node D2M8K2.u5765 (nat_lit 12412447) (nat_lit 2375047654) (nat_lit 0) D2M8K2.u5768 from rfl, totK_node, atot5765, atot5768]
  decide +kernel

theorem arows5777 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5777 = true := by
  rw [show D2M8K2.u5777 = KTree.node D2M8K2.u5773 (nat_lit 12488142) (nat_lit 3843012589) (nat_lit 0) D2M8K2.u5776 from rfl, allE_node, arows5773, irow5777, arows5776]
  all_goals rfl

theorem atot5777 : totK PD2M8K2 D2M8K2.u5777 = [715053144361, 2267719646722, 2481806111480, 1449519211498, 365522403098, 20647649770, 0, 0] := by
  rw [show D2M8K2.u5777 = KTree.node D2M8K2.u5773 (nat_lit 12488142) (nat_lit 3843012589) (nat_lit 0) D2M8K2.u5776 from rfl, totK_node, atot5773, atot5776]
  decide +kernel

theorem arows5784 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5784 = true := by
  rw [show D2M8K2.u5784 = KTree.node D2M8K2.u5780 (nat_lit 12494575) (nat_lit 2353934900) (nat_lit 0) D2M8K2.u5783 from rfl, allE_node, arows5780, irow5784, arows5783]
  all_goals rfl

theorem atot5784 : totK PD2M8K2 D2M8K2.u5784 = [799532159483, 2884451003830, 2845576754208, 648682022798, 24827743238, 0, 0, 0] := by
  rw [show D2M8K2.u5784 = KTree.node D2M8K2.u5780 (nat_lit 12494575) (nat_lit 2353934900) (nat_lit 0) D2M8K2.u5783 from rfl, totK_node, atot5780, atot5783]
  decide +kernel

theorem arows5793 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5793 = true := by
  rw [show D2M8K2.u5793 = KTree.node D2M8K2.u5789 (nat_lit 12501238) (nat_lit 3491975029) (nat_lit 0) D2M8K2.u5792 from rfl, allE_node, arows5789, irow5793, arows5792]
  all_goals rfl

theorem atot5793 : totK PD2M8K2 D2M8K2.u5793 = [598912855043, 2576536508268, 3066447206079, 925418289937, 53903982427, 0, 0, 0] := by
  rw [show D2M8K2.u5793 = KTree.node D2M8K2.u5789 (nat_lit 12501238) (nat_lit 3491975029) (nat_lit 0) D2M8K2.u5792 from rfl, totK_node, atot5789, atot5792]
  decide +kernel

theorem arows5800 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5800 = true := by
  rw [show D2M8K2.u5800 = KTree.node D2M8K2.u5796 (nat_lit 12510853) (nat_lit 1269587771) (nat_lit 0) D2M8K2.u5799 from rfl, allE_node, arows5796, irow5800, arows5799]
  all_goals rfl

theorem atot5800 : totK PD2M8K2 D2M8K2.u5800 = [0, 757285223151, 2777370814204, 2864089120517, 795856067049, 42081742489, 0, 0] := by
  rw [show D2M8K2.u5800 = KTree.node D2M8K2.u5796 (nat_lit 12510853) (nat_lit 1269587771) (nat_lit 0) D2M8K2.u5799 from rfl, totK_node, atot5796, atot5799]
  decide +kernel

theorem arows5808 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5808 = true := by
  rw [show D2M8K2.u5808 = KTree.node D2M8K2.u5804 (nat_lit 12518021) (nat_lit 2309236298) (nat_lit 0) D2M8K2.u5807 from rfl, allE_node, arows5804, irow5808, arows5807]
  all_goals rfl

theorem atot5808 : totK PD2M8K2 D2M8K2.u5808 = [0, 904306916751, 3134925985817, 2716187160568, 444420715332, 6634014755, 0, 0] := by
  rw [show D2M8K2.u5808 = KTree.node D2M8K2.u5804 (nat_lit 12518021) (nat_lit 2309236298) (nat_lit 0) D2M8K2.u5807 from rfl, totK_node, atot5804, atot5807]
  decide +kernel

theorem arows5815 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5815 = true := by
  rw [show D2M8K2.u5815 = KTree.node D2M8K2.u5811 (nat_lit 12525286) (nat_lit 2465141117) (nat_lit 0) D2M8K2.u5814 from rfl, allE_node, arows5811, irow5815, arows5814]
  all_goals rfl

theorem atot5815 : totK PD2M8K2 D2M8K2.u5815 = [683873556944, 2275953257778, 2551662281604, 1412444856199, 305738313679, 9302370699, 0, 0] := by
  rw [show D2M8K2.u5815 = KTree.node D2M8K2.u5811 (nat_lit 12525286) (nat_lit 2465141117) (nat_lit 0) D2M8K2.u5814 from rfl, totK_node, atot5811, atot5814]
  decide +kernel

theorem arows5825 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5825 = true := by
  rw [show D2M8K2.u5825 = KTree.node D2M8K2.u5821 (nat_lit 12532045) (nat_lit 1384185253) (nat_lit 0) D2M8K2.u5824 from rfl, allE_node, arows5821, irow5825, arows5824]
  all_goals rfl

theorem atot5825 : totK PD2M8K2 D2M8K2.u5825 = [695467159499, 2659643750147, 2944457855996, 918393186742, 50646844051, 0, 0, 0] := by
  rw [show D2M8K2.u5825 = KTree.node D2M8K2.u5821 (nat_lit 12532045) (nat_lit 1384185253) (nat_lit 0) D2M8K2.u5824 from rfl, totK_node, atot5821, atot5824]
  decide +kernel

theorem arows5832 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5832 = true := by
  rw [show D2M8K2.u5832 = KTree.node D2M8K2.u5828 (nat_lit 12542360) (nat_lit 3754315224) (nat_lit 0) D2M8K2.u5831 from rfl, allE_node, arows5828, irow5832, arows5831]
  all_goals rfl

theorem atot5832 : totK PD2M8K2 D2M8K2.u5832 = [663006220174, 2709349973505, 3041077420489, 769510074044, 28228720284, 0, 0, 0] := by
  rw [show D2M8K2.u5832 = KTree.node D2M8K2.u5828 (nat_lit 12542360) (nat_lit 3754315224) (nat_lit 0) D2M8K2.u5831 from rfl, totK_node, atot5828, atot5831]
  decide +kernel

theorem arows5840 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5840 = true := by
  rw [show D2M8K2.u5840 = KTree.node D2M8K2.u5836 (nat_lit 12549966) (nat_lit 3910713059) (nat_lit 0) D2M8K2.u5839 from rfl, allE_node, arows5836, irow5840, arows5839]
  all_goals rfl

theorem atot5840 : totK PD2M8K2 D2M8K2.u5840 = [0, 1089523522306, 3395826751209, 2419568723335, 292518559869, 2369401571, 0, 0] := by
  rw [show D2M8K2.u5840 = KTree.node D2M8K2.u5836 (nat_lit 12549966) (nat_lit 3910713059) (nat_lit 0) D2M8K2.u5839 from rfl, totK_node, atot5836, atot5839]
  decide +kernel

theorem arows5847 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5847 = true := by
  rw [show D2M8K2.u5847 = KTree.node D2M8K2.u5843 (nat_lit 12561712) (nat_lit 2047129420) (nat_lit 0) D2M8K2.u5846 from rfl, allE_node, arows5843, irow5847, arows5846]
  all_goals rfl

theorem atot5847 : totK PD2M8K2 D2M8K2.u5847 = [229587690250, 1346568036823, 2968112789430, 2175418693063, 397932788434, 16427657237, 0, 0] := by
  rw [show D2M8K2.u5847 = KTree.node D2M8K2.u5843 (nat_lit 12561712) (nat_lit 2047129420) (nat_lit 0) D2M8K2.u5846 from rfl, totK_node, atot5843, atot5846]
  decide +kernel

theorem arows5856 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5856 = true := by
  rw [show D2M8K2.u5856 = KTree.node D2M8K2.u5852 (nat_lit 12576714) (nat_lit 3888046470) (nat_lit 0) D2M8K2.u5855 from rfl, allE_node, arows5852, irow5856, arows5855]
  all_goals rfl

theorem atot5856 : totK PD2M8K2 D2M8K2.u5856 = [693368067088, 2638350372943, 2933641213708, 926122932708, 50845775260, 0, 0, 0] := by
  rw [show D2M8K2.u5856 = KTree.node D2M8K2.u5852 (nat_lit 12576714) (nat_lit 3888046470) (nat_lit 0) D2M8K2.u5855 from rfl, totK_node, atot5852, atot5855]
  decide +kernel

theorem arows5863 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5863 = true := by
  rw [show D2M8K2.u5863 = KTree.node D2M8K2.u5859 (nat_lit 12583654) (nat_lit 3776143439) (nat_lit 0) D2M8K2.u5862 from rfl, allE_node, arows5859, irow5863, arows5862]
  all_goals rfl

theorem atot5863 : totK PD2M8K2 D2M8K2.u5863 = [739385584865, 2837625405177, 2935541374897, 701639216943, 26987238905, 0, 0, 0] := by
  rw [show D2M8K2.u5863 = KTree.node D2M8K2.u5859 (nat_lit 12583654) (nat_lit 3776143439) (nat_lit 0) D2M8K2.u5862 from rfl, totK_node, atot5859, atot5862]
  decide +kernel

theorem arows5871 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5871 = true := by
  rw [show D2M8K2.u5871 = KTree.node D2M8K2.u5867 (nat_lit 12598561) (nat_lit 1553244865) (nat_lit 0) D2M8K2.u5870 from rfl, allE_node, arows5867, irow5871, arows5870]
  all_goals rfl

theorem atot5871 : totK PD2M8K2 D2M8K2.u5871 = [0, 1120743652333, 3307865828011, 2364341593482, 384432806633, 13105450397, 0, 0] := by
  rw [show D2M8K2.u5871 = KTree.node D2M8K2.u5867 (nat_lit 12598561) (nat_lit 1553244865) (nat_lit 0) D2M8K2.u5870 from rfl, totK_node, atot5867, atot5870]
  decide +kernel

theorem arows5878 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5878 = true := by
  rw [show D2M8K2.u5878 = KTree.node D2M8K2.u5874 (nat_lit 12605707) (nat_lit 1584360087) (nat_lit 0) D2M8K2.u5877 from rfl, allE_node, arows5874, irow5878, arows5877]
  all_goals rfl

theorem atot5878 : totK PD2M8K2 D2M8K2.u5878 = [510813857819, 2071017570470, 2865979275205, 1504694548292, 204666028750, 4720618446, 0, 0] := by
  rw [show D2M8K2.u5878 = KTree.node D2M8K2.u5874 (nat_lit 12605707) (nat_lit 1584360087) (nat_lit 0) D2M8K2.u5877 from rfl, totK_node, atot5874, atot5877]
  decide +kernel

theorem arows5890 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5890 = true := by
  rw [show D2M8K2.u5890 = KTree.node D2M8K2.u5886 (nat_lit 12614602) (nat_lit 3605675107) (nat_lit 0) D2M8K2.u5889 from rfl, allE_node, arows5886, irow5890, arows5889]
  all_goals rfl

theorem atot5890 : totK PD2M8K2 D2M8K2.u5890 = [716803855411, 2649045404900, 2891464790811, 915024167348, 50651435456, 0, 0, 0] := by
  rw [show D2M8K2.u5890 = KTree.node D2M8K2.u5886 (nat_lit 12614602) (nat_lit 3605675107) (nat_lit 0) D2M8K2.u5889 from rfl, totK_node, atot5886, atot5889]
  decide +kernel

theorem arows5897 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5897 = true := by
  rw [show D2M8K2.u5897 = KTree.node D2M8K2.u5893 (nat_lit 12621557) (nat_lit 2197073260) (nat_lit 0) D2M8K2.u5896 from rfl, allE_node, arows5893, irow5897, arows5896]
  all_goals rfl

theorem atot5897 : totK PD2M8K2 D2M8K2.u5897 = [756270871832, 2880158399998, 2903607016618, 639357597632, 19601020673, 0, 0, 0] := by
  rw [show D2M8K2.u5897 = KTree.node D2M8K2.u5893 (nat_lit 12621557) (nat_lit 2197073260) (nat_lit 0) D2M8K2.u5896 from rfl, totK_node, atot5893, atot5896]
  decide +kernel

theorem arows5905 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5905 = true := by
  rw [show D2M8K2.u5905 = KTree.node D2M8K2.u5901 (nat_lit 12632871) (nat_lit 3632587653) (nat_lit 0) D2M8K2.u5904 from rfl, allE_node, arows5901, irow5905, arows5904]
  all_goals rfl

theorem atot5905 : totK PD2M8K2 D2M8K2.u5905 = [0, 1294047403489, 3584641270935, 2103344445468, 191720705947, 1138244013, 0, 0] := by
  rw [show D2M8K2.u5905 = KTree.node D2M8K2.u5901 (nat_lit 12632871) (nat_lit 3632587653) (nat_lit 0) D2M8K2.u5904 from rfl, totK_node, atot5901, atot5904]
  decide +kernel

theorem arows5912 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5912 = true := by
  rw [show D2M8K2.u5912 = KTree.node D2M8K2.u5908 (nat_lit 12644163) (nat_lit 3608926952) (nat_lit 0) D2M8K2.u5911 from rfl, allE_node, arows5908, irow5912, arows5911]
  all_goals rfl

theorem atot5912 : totK PD2M8K2 D2M8K2.u5912 = [353677020485, 1801535597512, 3052792999913, 1697941249254, 241028444485, 4977114383, 0, 0] := by
  rw [show D2M8K2.u5912 = KTree.node D2M8K2.u5908 (nat_lit 12644163) (nat_lit 3608926952) (nat_lit 0) D2M8K2.u5911 from rfl, totK_node, atot5908, atot5911]
  decide +kernel

theorem arows5921 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5921 = true := by
  rw [show D2M8K2.u5921 = KTree.node D2M8K2.u5917 (nat_lit 12655398) (nat_lit 3761172002) (nat_lit 0) D2M8K2.u5920 from rfl, allE_node, arows5917, irow5921, arows5920]
  all_goals rfl

theorem atot5921 : totK PD2M8K2 D2M8K2.u5921 = [815225431193, 2821976902006, 2804984486958, 801177341295, 39899052951, 0, 0, 0] := by
  rw [show D2M8K2.u5921 = KTree.node D2M8K2.u5917 (nat_lit 12655398) (nat_lit 3761172002) (nat_lit 0) D2M8K2.u5920 from rfl, totK_node, atot5917, atot5920]
  decide +kernel

theorem arows5928 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5928 = true := by
  rw [show D2M8K2.u5928 = KTree.node D2M8K2.u5924 (nat_lit 12662246) (nat_lit 4097372114) (nat_lit 0) D2M8K2.u5927 from rfl, allE_node, arows5924, irow5928, arows5927]
  all_goals rfl

theorem atot5928 : totK PD2M8K2 D2M8K2.u5928 = [826335606808, 2922944497677, 2842349489975, 644146672492, 23871554079, 0, 0, 0] := by
  rw [show D2M8K2.u5928 = KTree.node D2M8K2.u5924 (nat_lit 12662246) (nat_lit 4097372114) (nat_lit 0) D2M8K2.u5927 from rfl, totK_node, atot5924, atot5927]
  decide +kernel

theorem arows5936 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5936 = true := by
  rw [show D2M8K2.u5936 = KTree.node D2M8K2.u5932 (nat_lit 12673487) (nat_lit 2152645251) (nat_lit 0) D2M8K2.u5935 from rfl, allE_node, arows5932, irow5936, arows5935]
  all_goals rfl

theorem atot5936 : totK PD2M8K2 D2M8K2.u5936 = [0, 1258424715148, 3516904731918, 2225600500251, 225515842988, 1310285577, 0, 0] := by
  rw [show D2M8K2.u5936 = KTree.node D2M8K2.u5932 (nat_lit 12673487) (nat_lit 2152645251) (nat_lit 0) D2M8K2.u5935 from rfl, totK_node, atot5932, atot5935]
  decide +kernel

theorem arows5943 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5943 = true := by
  rw [show D2M8K2.u5943 = KTree.node D2M8K2.u5939 (nat_lit 12681648) (nat_lit 3664654344) (nat_lit 0) D2M8K2.u5942 from rfl, allE_node, arows5939, irow5943, arows5942]
  all_goals rfl

theorem atot5943 : totK PD2M8K2 D2M8K2.u5943 = [0, 912911575176, 3167212562406, 2676180843194, 430791089788, 9811245038, 0, 0] := by
  rw [show D2M8K2.u5943 = KTree.node D2M8K2.u5939 (nat_lit 12681648) (nat_lit 3664654344) (nat_lit 0) D2M8K2.u5942 from rfl, totK_node, atot5939, atot5942]
  decide +kernel

theorem arows5953 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5953 = true := by
  rw [show D2M8K2.u5953 = KTree.node D2M8K2.u5949 (nat_lit 12736761) (nat_lit 1902180880) (nat_lit 0) D2M8K2.u5952 from rfl, allE_node, arows5949, irow5953, arows5952]
  all_goals rfl

theorem atot5953 : totK PD2M8K2 D2M8K2.u5953 = [0, 680954177198, 2547889041050, 2964917729199, 1003837267573, 59360566171, 0, 0] := by
  rw [show D2M8K2.u5953 = KTree.node D2M8K2.u5949 (nat_lit 12736761) (nat_lit 1902180880) (nat_lit 0) D2M8K2.u5952 from rfl, totK_node, atot5949, atot5952]
  decide +kernel

theorem arows5960 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5960 = true := by
  rw [show D2M8K2.u5960 = KTree.node D2M8K2.u5956 (nat_lit 12743235) (nat_lit 3641591707) (nat_lit 0) D2M8K2.u5959 from rfl, allE_node, arows5956, irow5960, arows5959]
  all_goals rfl

theorem atot5960 : totK PD2M8K2 D2M8K2.u5960 = [0, 797584873396, 2885084452730, 2849193070189, 630998042519, 17530736909, 0, 0] := by
  rw [show D2M8K2.u5960 = KTree.node D2M8K2.u5956 (nat_lit 12743235) (nat_lit 3641591707) (nat_lit 0) D2M8K2.u5959 from rfl, totK_node, atot5956, atot5959]
  decide +kernel

theorem arows5968 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5968 = true := by
  rw [show D2M8K2.u5968 = KTree.node D2M8K2.u5964 (nat_lit 12749904) (nat_lit 3367748203) (nat_lit 0) D2M8K2.u5967 from rfl, allE_node, arows5964, irow5968, arows5967]
  all_goals rfl

theorem atot5968 : totK PD2M8K2 D2M8K2.u5968 = [0, 639169245621, 2693952718674, 3018614742512, 816961383356, 40174437852, 0, 0] := by
  rw [show D2M8K2.u5968 = KTree.node D2M8K2.u5964 (nat_lit 12749904) (nat_lit 3367748203) (nat_lit 0) D2M8K2.u5967 from rfl, totK_node, atot5964, atot5967]
  decide +kernel

theorem arows5975 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5975 = true := by
  rw [show D2M8K2.u5975 = KTree.node D2M8K2.u5971 (nat_lit 12759530) (nat_lit 4062864674) (nat_lit 0) D2M8K2.u5974 from rfl, allE_node, arows5971, irow5975, arows5974]
  all_goals rfl

theorem atot5975 : totK PD2M8K2 D2M8K2.u5975 = [0, 0, 749958508585, 2751968039198, 2844893850116, 774210108714, 41989737272, 0] := by
  rw [show D2M8K2.u5975 = KTree.node D2M8K2.u5971 (nat_lit 12759530) (nat_lit 4062864674) (nat_lit 0) D2M8K2.u5974 from rfl, totK_node, atot5971, atot5974]
  decide +kernel

theorem arows5984 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5984 = true := by
  rw [show D2M8K2.u5984 = KTree.node D2M8K2.u5980 (nat_lit 12766824) (nat_lit 2611080447) (nat_lit 0) D2M8K2.u5983 from rfl, allE_node, arows5980, irow5984, arows5983]
  all_goals rfl

theorem atot5984 : totK PD2M8K2 D2M8K2.u5984 = [0, 0, 918782747140, 3153720935853, 2673502851098, 401931869614, 6518567072, 0] := by
  rw [show D2M8K2.u5984 = KTree.node D2M8K2.u5980 (nat_lit 12766824) (nat_lit 2611080447) (nat_lit 0) D2M8K2.u5983 from rfl, totK_node, atot5980, atot5983]
  decide +kernel

theorem arows5991 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5991 = true := by
  rw [show D2M8K2.u5991 = KTree.node D2M8K2.u5987 (nat_lit 12774193) (nat_lit 1408261823) (nat_lit 0) D2M8K2.u5990 from rfl, allE_node, arows5987, irow5991, arows5990]
  all_goals rfl

theorem atot5991 : totK PD2M8K2 D2M8K2.u5991 = [0, 683873556944, 2335680074062, 2524256256435, 1339026003841, 278061495679, 9139067247, 0] := by
  rw [show D2M8K2.u5991 = KTree.node D2M8K2.u5987 (nat_lit 12774193) (nat_lit 1408261823) (nat_lit 0) D2M8K2.u5990 from rfl, totK_node, atot5987, atot5990]
  decide +kernel

theorem arows5999 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5999 = true := by
  rw [show D2M8K2.u5999 = KTree.node D2M8K2.u5995 (nat_lit 12780960) (nat_lit 3506628283) (nat_lit 0) D2M8K2.u5998 from rfl, allE_node, arows5995, irow5999, arows5998]
  all_goals rfl

theorem atot5999 : totK PD2M8K2 D2M8K2.u5999 = [0, 695467159499, 2627057353731, 2947941778081, 923874112529, 50537053416, 0, 0] := by
  rw [show D2M8K2.u5999 = KTree.node D2M8K2.u5995 (nat_lit 12780960) (nat_lit 3506628283) (nat_lit 0) D2M8K2.u5998 from rfl, totK_node, atot5995, atot5998]
  decide +kernel

theorem arows6006 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6006 = true := by
  rw [show D2M8K2.u6006 = KTree.node D2M8K2.u6002 (nat_lit 12791266) (nat_lit 4004572508) (nat_lit 0) D2M8K2.u6005 from rfl, allE_node, arows6002, irow6006, arows6005]
  all_goals rfl

theorem atot6006 : totK PD2M8K2 D2M8K2.u6006 = [0, 663006220174, 2722718009144, 3035990964970, 740473040873, 24151216298, 0, 0] := by
  rw [show D2M8K2.u6006 = KTree.node D2M8K2.u6002 (nat_lit 12791266) (nat_lit 4004572508) (nat_lit 0) D2M8K2.u6005 from rfl, totK_node, atot6002, atot6005]
  decide +kernel

theorem arows6017 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6017 = true := by
  rw [show D2M8K2.u6017 = KTree.node D2M8K2.u6013 (nat_lit 12801560) (nat_lit 3875187374) (nat_lit 0) D2M8K2.u6016 from rfl, allE_node, arows6013, irow6017, arows6016]
  all_goals rfl

theorem atot6017 : totK PD2M8K2 D2M8K2.u6017 = [0, 0, 1209613994519, 3443006617153, 2204731351313, 282039478372, 5320761635, 0] := by
  rw [show D2M8K2.u6017 = KTree.node D2M8K2.u6013 (nat_lit 12801560) (nat_lit 3875187374) (nat_lit 0) D2M8K2.u6016 from rfl, totK_node, atot6013, atot6016]
  decide +kernel

theorem arows6024 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6024 = true := by
  rw [show D2M8K2.u6024 = KTree.node D2M8K2.u6020 (nat_lit 12812399) (nat_lit 2770046035) (nat_lit 0) D2M8K2.u6023 from rfl, allE_node, arows6020, irow6024, arows6023]
  all_goals rfl

theorem atot6024 : totK PD2M8K2 D2M8K2.u6024 = [0, 429562897600, 1912444360520, 3022657473848, 1660831528523, 168626305706, 1225787871, 0] := by
  rw [show D2M8K2.u6024 = KTree.node D2M8K2.u6020 (nat_lit 12812399) (nat_lit 2770046035) (nat_lit 0) D2M8K2.u6023 from rfl, totK_node, atot6020, atot6023]
  decide +kernel

theorem arows6032 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6032 = true := by
  rw [show D2M8K2.u6032 = KTree.node D2M8K2.u6028 (nat_lit 12827100) (nat_lit 3169885337) (nat_lit 0) D2M8K2.u6031 from rfl, allE_node, arows6028, irow6032, arows6031]
  all_goals rfl

theorem atot6032 : totK PD2M8K2 D2M8K2.u6032 = [0, 826942995957, 2868612413989, 2788558672763, 700776479509, 25382968211, 0, 0] := by
  rw [show D2M8K2.u6032 = KTree.node D2M8K2.u6028 (nat_lit 12827100) (nat_lit 3169885337) (nat_lit 0) D2M8K2.u6031 from rfl, totK_node, atot6028, atot6031]
  decide +kernel

theorem arows6039 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6039 = true := by
  rw [show D2M8K2.u6039 = KTree.node D2M8K2.u6035 (nat_lit 12834195) (nat_lit 3684479650) (nat_lit 0) D2M8K2.u6038 from rfl, allE_node, arows6035, irow6039, arows6038]
  all_goals rfl

theorem atot6039 : totK PD2M8K2 D2M8K2.u6039 = [0, 405835448646, 2247542563554, 3312479590928, 1201292816275, 67388929446, 0, 0] := by
  rw [show D2M8K2.u6039 = KTree.node D2M8K2.u6035 (nat_lit 12834195) (nat_lit 3684479650) (nat_lit 0) D2M8K2.u6038 from rfl, totK_node, atot6035, atot6038]
  decide +kernel

theorem arows6048 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6048 = true := by
  rw [show D2M8K2.u6048 = KTree.node D2M8K2.u6044 (nat_lit 12849559) (nat_lit 2215749743) (nat_lit 0) D2M8K2.u6047 from rfl, allE_node, arows6044, irow6048, arows6047]
  all_goals rfl

theorem atot6048 : totK PD2M8K2 D2M8K2.u6048 = [0, 0, 960522091239, 3210239287667, 2566222852275, 368449497235, 6624648996, 0] := by
  rw [show D2M8K2.u6048 = KTree.node D2M8K2.u6044 (nat_lit 12849559) (nat_lit 2215749743) (nat_lit 0) D2M8K2.u6047 from rfl, totK_node, atot6044, atot6047]
  decide +kernel

theorem arows6055 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6055 = true := by
  rw [show D2M8K2.u6055 = KTree.node D2M8K2.u6051 (nat_lit 12859259) (nat_lit 1926219256) (nat_lit 0) D2M8K2.u6054 from rfl, allE_node, arows6051, irow6055, arows6054]
  all_goals rfl

theorem atot6055 : totK PD2M8K2 D2M8K2.u6055 = [0, 752141467331, 2729036791764, 2817675187833, 849349578977, 50489227236, 0, 0] := by
  rw [show D2M8K2.u6055 = KTree.node D2M8K2.u6051 (nat_lit 12859259) (nat_lit 1926219256) (nat_lit 0) D2M8K2.u6054 from rfl, totK_node, atot6051, atot6054]
  decide +kernel

theorem arows6063 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6063 = true := by
  rw [show D2M8K2.u6063 = KTree.node D2M8K2.u6059 (nat_lit 12865636) (nat_lit 3881538657) (nat_lit 0) D2M8K2.u6062 from rfl, allE_node, arows6059, irow6063, arows6062]
  all_goals rfl

theorem atot6063 : totK PD2M8K2 D2M8K2.u6063 = [0, 798975846603, 2855832176007, 2831710634227, 678887568086, 22347978492, 0, 0] := by
  rw [show D2M8K2.u6063 = KTree.node D2M8K2.u6059 (nat_lit 12865636) (nat_lit 3881538657) (nat_lit 0) D2M8K2.u6062 from rfl, totK_node, atot6059, atot6062]
  decide +kernel

theorem arows6070 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6070 = true := by
  rw [show D2M8K2.u6070 = KTree.node D2M8K2.u6066 (nat_lit 12872512) (nat_lit 3764622440) (nat_lit 0) D2M8K2.u6069 from rfl, allE_node, arows6066, irow6070, arows6069]
  all_goals rfl

theorem atot6070 : totK PD2M8K2 D2M8K2.u6070 = [0, 436307283398, 2297592793759, 3280250360839, 1072469200602, 56842321013, 0, 0] := by
  rw [show D2M8K2.u6070 = KTree.node D2M8K2.u6066 (nat_lit 12872512) (nat_lit 3764622440) (nat_lit 0) D2M8K2.u6069 from rfl, totK_node, atot6066, atot6069]
  decide +kernel

theorem arows6080 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6080 = true := by
  rw [show D2M8K2.u6080 = KTree.node D2M8K2.u6076 (nat_lit 12888388) (nat_lit 2942825675) (nat_lit 0) D2M8K2.u6079 from rfl, allE_node, arows6076, irow6080, arows6079]
  all_goals rfl

theorem atot6080 : totK PD2M8K2 D2M8K2.u6080 = [0, 0, 1368624769122, 3706015159326, 1946290574211, 126677760812, 0, 0] := by
  rw [show D2M8K2.u6080 = KTree.node D2M8K2.u6076 (nat_lit 12888388) (nat_lit 2942825675) (nat_lit 0) D2M8K2.u6079 from rfl, totK_node, atot6076, atot6079]
  decide +kernel

theorem arows6087 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6087 = true := by
  rw [show D2M8K2.u6087 = KTree.node D2M8K2.u6083 (nat_lit 12901708) (nat_lit 3859069106) (nat_lit 0) D2M8K2.u6086 from rfl, allE_node, arows6083, irow6087, arows6086]
  all_goals rfl

theorem atot6087 : totK PD2M8K2 D2M8K2.u6087 = [0, 756190395948, 2616356643573, 2709236102179, 1013311591524, 132646306340, 1429815836, 0] := by
  rw [show D2M8K2.u6087 = KTree.node D2M8K2.u6083 (nat_lit 12901708) (nat_lit 3859069106) (nat_lit 0) D2M8K2.u6086 from rfl, totK_node, atot6083, atot6086]
  decide +kernel

theorem arows6095 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6095 = true := by
  rw [show D2M8K2.u6095 = KTree.node D2M8K2.u6091 (nat_lit 12907646) (nat_lit 3698171321) (nat_lit 0) D2M8K2.u6094 from rfl, allE_node, arows6091, irow6095, arows6094]
  all_goals rfl

theorem atot6095 : totK PD2M8K2 D2M8K2.u6095 = [0, 802316333251, 2849777514489, 2855315324512, 711685319423, 25053276113, 0, 0] := by
  rw [show D2M8K2.u6095 = KTree.node D2M8K2.u6091 (nat_lit 12907646) (nat_lit 3698171321) (nat_lit 0) D2M8K2.u6094 from rfl, totK_node, atot6091, atot6094]
  decide +kernel

theorem arows6102 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6102 = true := by
  rw [show D2M8K2.u6102 = KTree.node D2M8K2.u6098 (nat_lit 12917760) (nat_lit 2477152849) (nat_lit 0) D2M8K2.u6101 from rfl, allE_node, arows6098, irow6102, arows6101]
  all_goals rfl

theorem atot6102 : totK PD2M8K2 D2M8K2.u6102 = [0, 440762120087, 2371829163659, 3290010469674, 1088761574911, 56902173374, 0, 0] := by
  rw [show D2M8K2.u6102 = KTree.node D2M8K2.u6098 (nat_lit 12917760) (nat_lit 2477152849) (nat_lit 0) D2M8K2.u6101 from rfl, totK_node, atot6098, atot6101]
  decide +kernel

theorem arows6111 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6111 = true := by
  rw [show D2M8K2.u6111 = KTree.node D2M8K2.u6107 (nat_lit 12929167) (nat_lit 1875006417) (nat_lit 0) D2M8K2.u6110 from rfl, allE_node, arows6107, irow6111, arows6110]
  all_goals rfl

theorem atot6111 : totK PD2M8K2 D2M8K2.u6111 = [0, 0, 1016404690178, 3313352454748, 2562213717418, 307235258449, 2656098521, 0] := by
  rw [show D2M8K2.u6111 = KTree.node D2M8K2.u6107 (nat_lit 12929167) (nat_lit 1875006417) (nat_lit 0) D2M8K2.u6110 from rfl, totK_node, atot6107, atot6110]
  decide +kernel

theorem arows6118 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6118 = true := by
  rw [show D2M8K2.u6118 = KTree.node D2M8K2.u6114 (nat_lit 12940100) (nat_lit 3277113964) (nat_lit 0) D2M8K2.u6117 from rfl, allE_node, arows6114, irow6118, arows6117]
  all_goals rfl

theorem atot6118 : totK PD2M8K2 D2M8K2.u6118 = [666037732093, 2046136657624, 1763114355100, 1236156084204, 1196518660550, 275600791882, 9533751846, 0] := by
  rw [show D2M8K2.u6118 = KTree.node D2M8K2.u6114 (nat_lit 12940100) (nat_lit 3277113964) (nat_lit 0) D2M8K2.u6117 from rfl, totK_node, atot6114, atot6117]
  decide +kernel

theorem arows6126 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6126 = true := by
  rw [show D2M8K2.u6126 = KTree.node D2M8K2.u6122 (nat_lit 12950812) (nat_lit 2888417884) (nat_lit 0) D2M8K2.u6125 from rfl, allE_node, arows6122, irow6126, arows6125]
  all_goals rfl

theorem atot6126 : totK PD2M8K2 D2M8K2.u6126 = [835147699407, 2896556984893, 2730504764944, 628681864263, 26300412495, 0, 0, 0] := by
  rw [show D2M8K2.u6126 = KTree.node D2M8K2.u6122 (nat_lit 12950812) (nat_lit 2888417884) (nat_lit 0) D2M8K2.u6125 from rfl, totK_node, atot6122, atot6125]
  decide +kernel

theorem arows6133 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6133 = true := by
  rw [show D2M8K2.u6133 = KTree.node D2M8K2.u6129 (nat_lit 12957984) (nat_lit 3708958841) (nat_lit 0) D2M8K2.u6132 from rfl, allE_node, arows6129, irow6133, arows6132]
  all_goals rfl

theorem atot6133 : totK PD2M8K2 D2M8K2.u6133 = [504464290524, 2442823613597, 3181565773441, 959361717935, 45032108697, 0, 0, 0] := by
  rw [show D2M8K2.u6133 = KTree.node D2M8K2.u6129 (nat_lit 12957984) (nat_lit 3708958841) (nat_lit 0) D2M8K2.u6132 from rfl, totK_node, atot6129, atot6132]
  decide +kernel

theorem arows6148 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6148 = true := by
  rw [show D2M8K2.u6148 = KTree.node D2M8K2.u6144 (nat_lit 12968256) (nat_lit 3390458902) (nat_lit 0) D2M8K2.u6147 from rfl, allE_node, arows6144, irow6148, arows6147]
  all_goals rfl

theorem atot6148 : totK PD2M8K2 D2M8K2.u6148 = [0, 1218556629826, 3527533221580, 2101139683704, 212589379357, 1369150432, 0, 0] := by
  rw [show D2M8K2.u6148 = KTree.node D2M8K2.u6144 (nat_lit 12968256) (nat_lit 3390458902) (nat_lit 0) D2M8K2.u6147 from rfl, totK_node, atot6144, atot6147]
  decide +kernel

theorem arows6155 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6155 = true := by
  rw [show D2M8K2.u6155 = KTree.node D2M8K2.u6151 (nat_lit 12985164) (nat_lit 2660977686) (nat_lit 0) D2M8K2.u6154 from rfl, allE_node, arows6151, irow6155, arows6154]
  all_goals rfl

theorem atot6155 : totK PD2M8K2 D2M8K2.u6155 = [535074504078, 2278160205285, 3130732276888, 1262128982450, 73611041568, 0, 0, 0] := by
  rw [show D2M8K2.u6155 = KTree.node D2M8K2.u6151 (nat_lit 12985164) (nat_lit 2660977686) (nat_lit 0) D2M8K2.u6154 from rfl, totK_node, atot6151, atot6154]
  decide +kernel

theorem arows6163 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6163 = true := by
  rw [show D2M8K2.u6163 = KTree.node D2M8K2.u6159 (nat_lit 12991509) (nat_lit 1727172080) (nat_lit 0) D2M8K2.u6162 from rfl, allE_node, arows6159, irow6163, arows6162]
  all_goals rfl

theorem atot6163 : totK PD2M8K2 D2M8K2.u6163 = [859668879974, 2960274766781, 2818946397309, 617307476134, 23735181581, 0, 0, 0] := by
  rw [show D2M8K2.u6163 = KTree.node D2M8K2.u6159 (nat_lit 12991509) (nat_lit 1727172080) (nat_lit 0) D2M8K2.u6162 from rfl, totK_node, atot6159, atot6162]
  decide +kernel

theorem arows6170 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6170 = true := by
  rw [show D2M8K2.u6170 = KTree.node D2M8K2.u6166 (nat_lit 12998740) (nat_lit 3734805112) (nat_lit 0) D2M8K2.u6169 from rfl, allE_node, arows6166, irow6170, arows6169]
  all_goals rfl

theorem atot6170 : totK PD2M8K2 D2M8K2.u6170 = [634140869922, 2678068150572, 3039764620050, 854081129277, 48917881377, 0, 0, 0] := by
  rw [show D2M8K2.u6170 = KTree.node D2M8K2.u6166 (nat_lit 12998740) (nat_lit 3734805112) (nat_lit 0) D2M8K2.u6169 from rfl, totK_node, atot6166, atot6169]
  decide +kernel

theorem arows6179 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6179 = true := by
  rw [show D2M8K2.u6179 = KTree.node D2M8K2.u6175 (nat_lit 13008400) (nat_lit 3398309562) (nat_lit 0) D2M8K2.u6178 from rfl, allE_node, arows6175, irow6179, arows6178]
  all_goals rfl

theorem atot6179 : totK PD2M8K2 D2M8K2.u6179 = [0, 727644041057, 2757101058036, 2912995542424, 799803370486, 42081742489, 0, 0] := by
  rw [show D2M8K2.u6179 = KTree.node D2M8K2.u6175 (nat_lit 13008400) (nat_lit 3398309562) (nat_lit 0) D2M8K2.u6178 from rfl, totK_node, atot6175, atot6178]
  decide +kernel

theorem arows6186 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6186 = true := by
  rw [show D2M8K2.u6186 = KTree.node D2M8K2.u6182 (nat_lit 13015905) (nat_lit 1826690268) (nat_lit 0) D2M8K2.u6185 from rfl, allE_node, arows6182, irow6186, arows6185]
  all_goals rfl

theorem atot6186 : totK PD2M8K2 D2M8K2.u6186 = [0, 937413040619, 3159374339956, 2697240309934, 444889594501, 6634014755, 0, 0] := by
  rw [show D2M8K2.u6186 = KTree.node D2M8K2.u6182 (nat_lit 13015905) (nat_lit 1826690268) (nat_lit 0) D2M8K2.u6185 from rfl, totK_node, atot6182, atot6185]
  decide +kernel

theorem arows6194 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6194 = true := by
  rw [show D2M8K2.u6194 = KTree.node D2M8K2.u6190 (nat_lit 13023325) (nat_lit 1025544588) (nat_lit 0) D2M8K2.u6193 from rfl, allE_node, arows6190, irow6194, arows6193]
  all_goals rfl

theorem atot6194 : totK PD2M8K2 D2M8K2.u6194 = [719942848121, 2370754181735, 2524290985219, 1304192623050, 293132856893, 9302370699, 0, 0] := by
  rw [show D2M8K2.u6194 = KTree.node D2M8K2.u6190 (nat_lit 13023325) (nat_lit 1025544588) (nat_lit 0) D2M8K2.u6193 from rfl, totK_node, atot6190, atot6193]
  decide +kernel

theorem arows6201 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6201 = true := by
  rw [show D2M8K2.u6201 = KTree.node D2M8K2.u6197 (nat_lit 13029653) (nat_lit 2290691649) (nat_lit 0) D2M8K2.u6200 from rfl, allE_node, arows6197, irow6201, arows6200]
  all_goals rfl

theorem atot6201 : totK PD2M8K2 D2M8K2.u6201 = [705581847258, 2662373483073, 2938788148961, 908971871793, 50397935182, 0, 0, 0] := by
  rw [show D2M8K2.u6201 = KTree.node D2M8K2.u6197 (nat_lit 13029653) (nat_lit 2290691649) (nat_lit 0) D2M8K2.u6200 from rfl, totK_node, atot6197, atot6200]
  decide +kernel

theorem arows6211 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6211 = true := by
  rw [show D2M8K2.u6211 = KTree.node D2M8K2.u6207 (nat_lit 13039901) (nat_lit 2261509912) (nat_lit 0) D2M8K2.u6210 from rfl, allE_node, arows6207, irow6211, arows6210]
  all_goals rfl

theorem atot6211 : totK PD2M8K2 D2M8K2.u6211 = [707482735916, 2804040704134, 2981186462277, 704298726724, 26842150570, 0, 0, 0] := by
  rw [show D2M8K2.u6211 = KTree.node D2M8K2.u6207 (nat_lit 13039901) (nat_lit 2261509912) (nat_lit 0) D2M8K2.u6210 from rfl, totK_node, atot6207, atot6210]
  decide +kernel

theorem arows6218 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6218 = true := by
  rw [show D2M8K2.u6218 = KTree.node D2M8K2.u6214 (nat_lit 13047096) (nat_lit 3265016501) (nat_lit 0) D2M8K2.u6217 from rfl, allE_node, arows6214, irow6218, arows6217]
  all_goals rfl

theorem atot6218 : totK PD2M8K2 D2M8K2.u6218 = [0, 1193448112534, 3554566929840, 2224196504028, 206119548542, 1206465782, 0, 0] := by
  rw [show D2M8K2.u6218 = KTree.node D2M8K2.u6214 (nat_lit 13047096) (nat_lit 3265016501) (nat_lit 0) D2M8K2.u6217 from rfl, totK_node, atot6214, atot6217]
  decide +kernel

theorem arows6226 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6226 = true := by
  rw [show D2M8K2.u6226 = KTree.node D2M8K2.u6222 (nat_lit 13058497) (nat_lit 1573021799) (nat_lit 0) D2M8K2.u6225 from rfl, allE_node, arows6222, irow6226, arows6225]
  all_goals rfl

theorem atot6226 : totK PD2M8K2 D2M8K2.u6226 = [76372199855, 951948343311, 2967368853594, 2564864245739, 489650537489, 17590593026, 0, 0] := by
  rw [show D2M8K2.u6226 = KTree.node D2M8K2.u6222 (nat_lit 13058497) (nat_lit 1573021799) (nat_lit 0) D2M8K2.u6225 from rfl, totK_node, atot6222, atot6225]
  decide +kernel

theorem arows6233 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6233 = true := by
  rw [show D2M8K2.u6233 = KTree.node D2M8K2.u6229 (nat_lit 13109193) (nat_lit 1788316196) (nat_lit 0) D2M8K2.u6232 from rfl, allE_node, arows6229, irow6233, arows6232]
  all_goals rfl

theorem atot6233 : totK PD2M8K2 D2M8K2.u6233 = [745012336601, 2814526462430, 2863856602338, 747603074339, 34373176832, 0, 0, 0] := by
  rw [show D2M8K2.u6233 = KTree.node D2M8K2.u6229 (nat_lit 13109193) (nat_lit 1788316196) (nat_lit 0) D2M8K2.u6232 from rfl, totK_node, atot6229, atot6232]
  decide +kernel

theorem arows6242 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6242 = true := by
  rw [show D2M8K2.u6242 = KTree.node D2M8K2.u6238 (nat_lit 13115232) (nat_lit 3661867763) (nat_lit 0) D2M8K2.u6241 from rfl, allE_node, arows6238, irow6242, arows6241]
  all_goals rfl

theorem atot6242 : totK PD2M8K2 D2M8K2.u6242 = [855467100470, 2894801364297, 2734043734603, 656531866555, 30713402040, 0, 0, 0] := by
  rw [show D2M8K2.u6242 = KTree.node D2M8K2.u6238 (nat_lit 13115232) (nat_lit 3661867763) (nat_lit 0) D2M8K2.u6241 from rfl, totK_node, atot6238, atot6241]
  decide +kernel

theorem arows6249 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6249 = true := by
  rw [show D2M8K2.u6249 = KTree.node D2M8K2.u6245 (nat_lit 13126162) (nat_lit 4006951394) (nat_lit 0) D2M8K2.u6248 from rfl, allE_node, arows6245, irow6249, arows6248]
  all_goals rfl

theorem atot6249 : totK PD2M8K2 D2M8K2.u6249 = [332401058255, 1916166458155, 3218965513133, 1522618995022, 145258950567, 1138244013, 0, 0] := by
  rw [show D2M8K2.u6249 = KTree.node D2M8K2.u6245 (nat_lit 13126162) (nat_lit 4006951394) (nat_lit 0) D2M8K2.u6248 from rfl, totK_node, atot6245, atot6248]
  decide +kernel

theorem arows6257 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6257 = true := by
  rw [show D2M8K2.u6257 = KTree.node D2M8K2.u6253 (nat_lit 13136603) (nat_lit 2027172459) (nat_lit 0) D2M8K2.u6256 from rfl, allE_node, arows6253, irow6257, arows6256]
  all_goals rfl

theorem atot6257 : totK PD2M8K2 D2M8K2.u6257 = [0, 1401335303914, 3681445951055, 1923592444291, 155288552189, 1095107716, 0, 0] := by
  rw [show D2M8K2.u6257 = KTree.node D2M8K2.u6253 (nat_lit 13136603) (nat_lit 2027172459) (nat_lit 0) D2M8K2.u6256 from rfl, totK_node, atot6253, atot6256]
  decide +kernel

theorem arows6264 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6264 = true := by
  rw [show D2M8K2.u6264 = KTree.node D2M8K2.u6260 (nat_lit 13148988) (nat_lit 3224907551) (nat_lit 0) D2M8K2.u6263 from rfl, allE_node, arows6260, irow6264, arows6263]
  all_goals rfl

theorem atot6264 : totK PD2M8K2 D2M8K2.u6264 = [826693180625, 2705967920793, 2547641490301, 974949422997, 157838419852, 3882006667, 0, 0] := by
  rw [show D2M8K2.u6264 = KTree.node D2M8K2.u6260 (nat_lit 13148988) (nat_lit 3224907551) (nat_lit 0) D2M8K2.u6263 from rfl, totK_node, atot6260, atot6263]
  decide +kernel

theorem arows6275 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6275 = true := by
  rw [show D2M8K2.u6275 = KTree.node D2M8K2.u6271 (nat_lit 13155374) (nat_lit 2149399010) (nat_lit 0) D2M8K2.u6274 from rfl, allE_node, arows6271, irow6275, arows6274]
  all_goals rfl

theorem atot6275 : totK PD2M8K2 D2M8K2.u6275 = [753679371020, 2729173146822, 2920404399694, 808444996998, 30265497698, 0, 0, 0] := by
  rw [show D2M8K2.u6275 = KTree.node D2M8K2.u6271 (nat_lit 13155374) (nat_lit 2149399010) (nat_lit 0) D2M8K2.u6274 from rfl, totK_node, atot6271, atot6274]
  decide +kernel

theorem arows6282 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6282 = true := by
  rw [show D2M8K2.u6282 = KTree.node D2M8K2.u6278 (nat_lit 13166246) (nat_lit 4113132171) (nat_lit 0) D2M8K2.u6281 from rfl, allE_node, arows6278, irow6282, arows6281]
  all_goals rfl

theorem atot6282 : totK PD2M8K2 D2M8K2.u6282 = [441844054865, 2172662538620, 3173590046753, 1294289987718, 115508722327, 1310285577, 0, 0] := by
  rw [show D2M8K2.u6282 = KTree.node D2M8K2.u6278 (nat_lit 13166246) (nat_lit 4113132171) (nat_lit 0) D2M8K2.u6281 from rfl, totK_node, atot6278, atot6281]
  decide +kernel

theorem arows6290 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6290 = true := by
  rw [show D2M8K2.u6290 = KTree.node D2M8K2.u6286 (nat_lit 13174769) (nat_lit 1738422341) (nat_lit 0) D2M8K2.u6289 from rfl, allE_node, arows6286, irow6290, arows6289]
  all_goals rfl

theorem atot6290 : totK PD2M8K2 D2M8K2.u6290 = [0, 1023668211121, 3283664059036, 2567873529485, 328352414689, 4879840392, 0, 0] := by
  rw [show D2M8K2.u6290 = KTree.node D2M8K2.u6286 (nat_lit 13174769) (nat_lit 1738422341) (nat_lit 0) D2M8K2.u6289 from rfl, totK_node, atot6286, atot6289]
  decide +kernel

theorem arows6297 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6297 = true := by
  rw [show D2M8K2.u6297 = KTree.node D2M8K2.u6293 (nat_lit 13186080) (nat_lit 3708958841) (nat_lit 0) D2M8K2.u6296 from rfl, allE_node, arows6293, irow6297, arows6296]
  all_goals rfl

theorem atot6297 : totK PD2M8K2 D2M8K2.u6297 = [0, 864334003755, 2955174972388, 2700374665862, 608522820772, 26682572712, 0, 0] := by
  rw [show D2M8K2.u6297 = KTree.node D2M8K2.u6293 (nat_lit 13186080) (nat_lit 3708958841) (nat_lit 0) D2M8K2.u6296 from rfl, totK_node, atot6293, atot6296]
  decide +kernel

theorem arows6306 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6306 = true := by
  rw [show D2M8K2.u6306 = KTree.node D2M8K2.u6302 (nat_lit 13196269) (nat_lit 1123891006) (nat_lit 0) D2M8K2.u6305 from rfl, allE_node, arows6302, irow6306, arows6305]
  all_goals rfl

theorem atot6306 : totK PD2M8K2 D2M8K2.u6306 = [0, 882449651811, 3059526708017, 2719866903131, 490884155553, 14418877666, 0, 0] := by
  rw [show D2M8K2.u6306 = KTree.node D2M8K2.u6302 (nat_lit 13196269) (nat_lit 1123891006) (nat_lit 0) D2M8K2.u6305 from rfl, totK_node, atot6302, atot6305]
  decide +kernel

theorem arows6313 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6313 = true := by
  rw [show D2M8K2.u6313 = KTree.node D2M8K2.u6309 (nat_lit 13203891) (nat_lit 1146996838) (nat_lit 0) D2M8K2.u6312 from rfl, allE_node, arows6309, irow6313, arows6312]
  all_goals rfl

theorem atot6313 : totK PD2M8K2 D2M8K2.u6313 = [0, 839626798211, 3052798352405, 2792504760751, 450076651455, 7384082042, 0, 0] := by
  rw [show D2M8K2.u6313 = KTree.node D2M8K2.u6309 (nat_lit 13203891) (nat_lit 1146996838) (nat_lit 0) D2M8K2.u6312 from rfl, totK_node, atot6309, atot6312]
  decide +kernel

theorem arows6321 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6321 = true := by
  rw [show D2M8K2.u6321 = KTree.node D2M8K2.u6317 (nat_lit 13211165) (nat_lit 2291127382) (nat_lit 0) D2M8K2.u6320 from rfl, allE_node, arows6317, irow6321, arows6320]
  all_goals rfl

theorem atot6321 : totK PD2M8K2 D2M8K2.u6321 = [0, 0, 1371695418147, 3632055434716, 1810365110834, 157429654018, 1275377855, 0] := by
  rw [show D2M8K2.u6321 = KTree.node D2M8K2.u6317 (nat_lit 13211165) (nat_lit 2291127382) (nat_lit 0) D2M8K2.u6320 from rfl, totK_node, atot6317, atot6320]
  decide +kernel

theorem arows6328 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6328 = true := by
  rw [show D2M8K2.u6328 = KTree.node D2M8K2.u6324 (nat_lit 13227686) (nat_lit 3982689873) (nat_lit 0) D2M8K2.u6327 from rfl, allE_node, arows6324, irow6328, arows6327]
  all_goals rfl

theorem atot6328 : totK PD2M8K2 D2M8K2.u6328 = [0, 443708700729, 2301920019971, 3308579243940, 1098265345375, 55459016937, 0, 0] := by
  rw [show D2M8K2.u6328 = KTree.node D2M8K2.u6324 (nat_lit 13227686) (nat_lit 3982689873) (nat_lit 0) D2M8K2.u6327 from rfl, totK_node, atot6324, atot6327]
  decide +kernel

theorem arows6338 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6338 = true := by
  rw [show D2M8K2.u6338 = KTree.node D2M8K2.u6334 (nat_lit 13238831) (nat_lit 1740776957) (nat_lit 0) D2M8K2.u6337 from rfl, allE_node, arows6334, irow6338, arows6337]
  all_goals rfl

theorem atot6338 : totK PD2M8K2 D2M8K2.u6338 = [0, 754640192146, 2793210427871, 2915831501767, 758876791254, 29437855860, 0, 0] := by
  rw [show D2M8K2.u6338 = KTree.node D2M8K2.u6334 (nat_lit 13238831) (nat_lit 1740776957) (nat_lit 0) D2M8K2.u6337 from rfl, totK_node, atot6334, atot6337]
  decide +kernel

theorem arows6345 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6345 = true := by
  rw [show D2M8K2.u6345 = KTree.node D2M8K2.u6341 (nat_lit 13246909) (nat_lit 1169493868) (nat_lit 0) D2M8K2.u6344 from rfl, allE_node, arows6341, irow6345, arows6344]
  all_goals rfl

theorem atot6345 : totK PD2M8K2 D2M8K2.u6345 = [0, 827172038782, 3015133022062, 2857428963629, 544645259528, 10097647243, 0, 0] := by
  rw [show D2M8K2.u6345 = KTree.node D2M8K2.u6341 (nat_lit 13246909) (nat_lit 1169493868) (nat_lit 0) D2M8K2.u6344 from rfl, totK_node, atot6341, atot6344]
  decide +kernel

theorem arows6353 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6353 = true := by
  rw [show D2M8K2.u6353 = KTree.node D2M8K2.u6349 (nat_lit 13274865) (nat_lit 1745379152) (nat_lit 0) D2M8K2.u6352 from rfl, allE_node, arows6349, irow6353, arows6352]
  all_goals rfl

theorem atot6353 : totK PD2M8K2 D2M8K2.u6353 = [0, 841075107272, 2949377795816, 2755466723371, 646531043439, 32849972973, 0, 0] := by
  rw [show D2M8K2.u6353 = KTree.node D2M8K2.u6349 (nat_lit 13274865) (nat_lit 1745379152) (nat_lit 0) D2M8K2.u6352 from rfl, totK_node, atot6349, atot6352]
  decide +kernel

theorem arows6360 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6360 = true := by
  rw [show D2M8K2.u6360 = KTree.node D2M8K2.u6356 (nat_lit 13280872) (nat_lit 3761714959) (nat_lit 0) D2M8K2.u6359 from rfl, allE_node, arows6356, irow6360, arows6359]
  all_goals rfl

theorem atot6360 : totK PD2M8K2 D2M8K2.u6360 = [0, 863908712849, 3005827147931, 2787854213343, 555310223857, 18260305523, 0, 0] := by
  rw [show D2M8K2.u6360 = KTree.node D2M8K2.u6356 (nat_lit 13280872) (nat_lit 3761714959) (nat_lit 0) D2M8K2.u6359 from rfl, totK_node, atot6356, atot6359]
  decide +kernel

theorem arows6369 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6369 = true := by
  rw [show D2M8K2.u6369 = KTree.node D2M8K2.u6365 (nat_lit 13290930) (nat_lit 2995251921) (nat_lit 0) D2M8K2.u6368 from rfl, allE_node, arows6365, irow6369, arows6368]
  all_goals rfl

theorem atot6369 : totK PD2M8K2 D2M8K2.u6369 = [0, 422956155823, 2005681234370, 3108613988998, 1393022361062, 129457342164, 1206465782, 0] := by
  rw [show D2M8K2.u6369 = KTree.node D2M8K2.u6365 (nat_lit 13290930) (nat_lit 2995251921) (nat_lit 0) D2M8K2.u6368 from rfl, totK_node, atot6365, atot6368]
  decide +kernel

theorem arows6376 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6376 = true := by
  rw [show D2M8K2.u6376 = KTree.node D2M8K2.u6372 (nat_lit 13300064) (nat_lit 3746301912) (nat_lit 0) D2M8K2.u6375 from rfl, allE_node, arows6372, irow6376, arows6375]
  all_goals rfl

theorem atot6376 : totK PD2M8K2 D2M8K2.u6376 = [0, 0, 1180800967927, 3339945396911, 2193119947121, 364731359132, 13016197374, 0] := by
  rw [show D2M8K2.u6376 = KTree.node D2M8K2.u6372 (nat_lit 13300064) (nat_lit 3746301912) (nat_lit 0) D2M8K2.u6375 from rfl, totK_node, atot6372, atot6375]
  decide +kernel

theorem arows6384 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6384 = true := by
  rw [show D2M8K2.u6384 = KTree.node D2M8K2.u6380 (nat_lit 13310772) (nat_lit 3079332899) (nat_lit 0) D2M8K2.u6383 from rfl, allE_node, arows6380, irow6384, arows6383]
  all_goals rfl

theorem atot6384 : totK PD2M8K2 D2M8K2.u6384 = [0, 497816364279, 2119854849023, 2883245085563, 1342037261293, 179783388144, 4574395652, 0] := by
  rw [show D2M8K2.u6384 = KTree.node D2M8K2.u6380 (nat_lit 13310772) (nat_lit 3079332899) (nat_lit 0) D2M8K2.u6383 from rfl, totK_node, atot6380, atot6383]
  decide +kernel

theorem arows6391 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6391 = true := by
  rw [show D2M8K2.u6391 = KTree.node D2M8K2.u6387 (nat_lit 13361020) (nat_lit 3809035114) (nat_lit 0) D2M8K2.u6390 from rfl, allE_node, arows6387, irow6391, arows6390]
  all_goals rfl

theorem atot6391 : totK PD2M8K2 D2M8K2.u6391 = [0, 774875116933, 2838729651076, 2892449661256, 711629632004, 28063716506, 0, 0] := by
  rw [show D2M8K2.u6391 = KTree.node D2M8K2.u6387 (nat_lit 13361020) (nat_lit 3809035114) (nat_lit 0) D2M8K2.u6390 from rfl, totK_node, atot6387, atot6390]
  decide +kernel

theorem arows6403 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6403 = true := by
  rw [show D2M8K2.u6403 = KTree.node D2M8K2.u6399 (nat_lit 13368406) (nat_lit 3104819299) (nat_lit 0) D2M8K2.u6402 from rfl, allE_node, arows6399, irow6403, arows6402]
  all_goals rfl

theorem atot6403 : totK PD2M8K2 D2M8K2.u6403 = [0, 734555081128, 2859061963028, 2923031323586, 615561648609, 19406804375, 0, 0] := by
  rw [show D2M8K2.u6403 = KTree.node D2M8K2.u6399 (nat_lit 13368406) (nat_lit 3104819299) (nat_lit 0) D2M8K2.u6402 from rfl, totK_node, atot6399, atot6402]
  decide +kernel

theorem arows6410 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6410 = true := by
  rw [show D2M8K2.u6410 = KTree.node D2M8K2.u6406 (nat_lit 13381632) (nat_lit 3757117624) (nat_lit 0) D2M8K2.u6409 from rfl, allE_node, arows6406, irow6410, arows6409]
  all_goals rfl

theorem atot6410 : totK PD2M8K2 D2M8K2.u6410 = [0, 0, 1455585733709, 3666167894474, 1745394835494, 124490788376, 1103454931, 0] := by
  rw [show D2M8K2.u6410 = KTree.node D2M8K2.u6406 (nat_lit 13381632) (nat_lit 3757117624) (nat_lit 0) D2M8K2.u6409 from rfl, totK_node, atot6406, atot6409]
  decide +kernel

theorem arows6418 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6418 = true := by
  rw [show D2M8K2.u6418 = KTree.node D2M8K2.u6414 (nat_lit 13396224) (nat_lit 3422611686) (nat_lit 0) D2M8K2.u6417 from rfl, allE_node, arows6414, irow6418, arows6417]
  all_goals rfl

theorem atot6418 : totK PD2M8K2 D2M8K2.u6418 = [0, 634381195407, 2290279046050, 2736253905813, 1219176717500, 173656841593, 4779662215, 0] := by
  rw [show D2M8K2.u6418 = KTree.node D2M8K2.u6414 (nat_lit 13396224) (nat_lit 3422611686) (nat_lit 0) D2M8K2.u6417 from rfl, totK_node, atot6414, atot6417]
  decide +kernel

theorem arows6425 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6425 = true := by
  rw [show D2M8K2.u6425 = KTree.node D2M8K2.u6421 (nat_lit 13402765) (nat_lit 849227676) (nat_lit 0) D2M8K2.u6424 from rfl, allE_node, arows6421, irow6425, arows6424]
  all_goals rfl

theorem atot6425 : totK PD2M8K2 D2M8K2.u6425 = [0, 765144027704, 2780347022562, 2856200365753, 807659079964, 42346070928, 0, 0] := by
  rw [show D2M8K2.u6425 = KTree.node D2M8K2.u6421 (nat_lit 13402765) (nat_lit 849227676) (nat_lit 0) D2M8K2.u6424 from rfl, totK_node, atot6421, atot6424]
  decide +kernel

theorem arows6434 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6434 = true := by
  rw [show D2M8K2.u6434 = KTree.node D2M8K2.u6430 (nat_lit 13413618) (nat_lit 3433520064) (nat_lit 0) D2M8K2.u6433 from rfl, allE_node, arows6430, irow6434, arows6433]
  all_goals rfl

theorem atot6434 : totK PD2M8K2 D2M8K2.u6434 = [193081648232, 1072049339569, 2620144300467, 2655663548191, 670873546934, 27211392168, 0, 0] := by
  rw [show D2M8K2.u6434 = KTree.node D2M8K2.u6430 (nat_lit 13413618) (nat_lit 3433520064) (nat_lit 0) D2M8K2.u6433 from rfl, totK_node, atot6430, atot6433]
  decide +kernel

theorem arows6441 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6441 = true := by
  rw [show D2M8K2.u6441 = KTree.node D2M8K2.u6437 (nat_lit 13942222) (nat_lit 4007305607) (nat_lit 0) D2M8K2.u6440 from rfl, allE_node, arows6437, irow6441, arows6440]
  all_goals rfl

theorem atot6441 : totK PD2M8K2 D2M8K2.u6441 = [882880993072, 3036553573567, 2740604055685, 517526062717, 14418877666, 0, 0, 0] := by
  rw [show D2M8K2.u6441 = KTree.node D2M8K2.u6437 (nat_lit 13942222) (nat_lit 4007305607) (nat_lit 0) D2M8K2.u6440 from rfl, totK_node, atot6437, atot6440]
  decide +kernel

theorem arows6449 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6449 = true := by
  rw [show D2M8K2.u6449 = KTree.node D2M8K2.u6445 (nat_lit 13949168) (nat_lit 3664052384) (nat_lit 0) D2M8K2.u6448 from rfl, allE_node, arows6445, irow6449, arows6448]
  all_goals rfl

theorem atot6449 : totK PD2M8K2 D2M8K2.u6449 = [821432370098, 2943800290263, 2776377709507, 569872173423, 18231200220, 0, 0, 0] := by
  rw [show D2M8K2.u6449 = KTree.node D2M8K2.u6445 (nat_lit 13949168) (nat_lit 3664052384) (nat_lit 0) D2M8K2.u6448 from rfl, totK_node, atot6445, atot6448]
  decide +kernel

theorem arows6456 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6456 = true := by
  rw [show D2M8K2.u6456 = KTree.node D2M8K2.u6452 (nat_lit 13956681) (nat_lit 1815606545) (nat_lit 0) D2M8K2.u6455 from rfl, allE_node, arows6452, irow6456, arows6455]
  all_goals rfl

theorem atot6456 : totK PD2M8K2 D2M8K2.u6456 = [76459986009, 1388266769919, 3441559229096, 1940888198871, 204241745273, 1369150432, 0, 0] := by
  rw [show D2M8K2.u6456 = KTree.node D2M8K2.u6452 (nat_lit 13956681) (nat_lit 1815606545) (nat_lit 0) D2M8K2.u6455 from rfl, totK_node, atot6452, atot6455]
  decide +kernel

theorem arows6466 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6466 = true := by
  rw [show D2M8K2.u6466 = KTree.node D2M8K2.u6462 (nat_lit 13970274) (nat_lit 3275060898) (nat_lit 0) D2M8K2.u6465 from rfl, allE_node, arows6462, irow6466, arows6465]
  all_goals rfl

theorem atot6466 : totK PD2M8K2 D2M8K2.u6466 = [338449428671, 1925529214847, 3356265199329, 1465999554294, 81691255263, 0, 0, 0] := by
  rw [show D2M8K2.u6466 = KTree.node D2M8K2.u6462 (nat_lit 13970274) (nat_lit 3275060898) (nat_lit 0) D2M8K2.u6465 from rfl, totK_node, atot6462, atot6465]
  decide +kernel

theorem arows6473 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6473 = true := by
  rw [show D2M8K2.u6473 = KTree.node D2M8K2.u6469 (nat_lit 13983563) (nat_lit 2698763696) (nat_lit 0) D2M8K2.u6472 from rfl, allE_node, arows6469, irow6473, arows6472]
  all_goals rfl

theorem atot6473 : totK PD2M8K2 D2M8K2.u6473 = [667187197526, 2628471248421, 2997824342492, 928357436521, 50646263903, 0, 0, 0] := by
  rw [show D2M8K2.u6473 = KTree.node D2M8K2.u6469 (nat_lit 13983563) (nat_lit 2698763696) (nat_lit 0) D2M8K2.u6472 from rfl, totK_node, atot6469, atot6472]
  decide +kernel

theorem arows6481 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6481 = true := by
  rw [show D2M8K2.u6481 = KTree.node D2M8K2.u6477 (nat_lit 13990507) (nat_lit 1650644940) (nat_lit 0) D2M8K2.u6480 from rfl, allE_node, arows6477, irow6481, arows6480]
  all_goals rfl

theorem atot6481 : totK PD2M8K2 D2M8K2.u6481 = [849305159433, 2986014113583, 2805140273442, 581747280131, 18214542822, 0, 0, 0] := by
  rw [show D2M8K2.u6481 = KTree.node D2M8K2.u6477 (nat_lit 13990507) (nat_lit 1650644940) (nat_lit 0) D2M8K2.u6480 from rfl, totK_node, atot6477, atot6480]
  decide +kernel

theorem arows6488 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6488 = true := by
  rw [show D2M8K2.u6488 = KTree.node D2M8K2.u6484 (nat_lit 14001456) (nat_lit 3120035742) (nat_lit 0) D2M8K2.u6487 from rfl, allE_node, arows6484, irow6488, arows6487]
  all_goals rfl

theorem atot6488 : totK PD2M8K2 D2M8K2.u6488 = [132249069452, 1307393316564, 2928608077496, 2249836033740, 615154392858, 36921873854, 0, 0] := by
  rw [show D2M8K2.u6488 = KTree.node D2M8K2.u6484 (nat_lit 14001456) (nat_lit 3120035742) (nat_lit 0) D2M8K2.u6487 from rfl, totK_node, atot6484, atot6487]
  decide +kernel

theorem arows6497 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6497 = true := by
  rw [show D2M8K2.u6497 = KTree.node D2M8K2.u6493 (nat_lit 14008129) (nat_lit 1443549880) (nat_lit 0) D2M8K2.u6496 from rfl, allE_node, arows6493, irow6497, arows6496]
  all_goals rfl

theorem atot6497 : totK PD2M8K2 D2M8K2.u6497 = [0, 886459395327, 3058951501253, 2753469772911, 504442365334, 10378741320, 0, 0] := by
  rw [show D2M8K2.u6497 = KTree.node D2M8K2.u6493 (nat_lit 14008129) (nat_lit 1443549880) (nat_lit 0) D2M8K2.u6496 from rfl, totK_node, atot6493, atot6496]
  decide +kernel

theorem arows6504 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6504 = true := by
  rw [show D2M8K2.u6504 = KTree.node D2M8K2.u6500 (nat_lit 14015647) (nat_lit 2331921920) (nat_lit 0) D2M8K2.u6503 from rfl, allE_node, arows6500, irow6504, arows6503]
  all_goals rfl

theorem atot6504 : totK PD2M8K2 D2M8K2.u6504 = [407232325195, 1546216611439, 2574876736309, 2225450744330, 460457889219, 10717512769, 0, 0] := by
  rw [show D2M8K2.u6504 = KTree.node D2M8K2.u6500 (nat_lit 14015647) (nat_lit 2331921920) (nat_lit 0) D2M8K2.u6503 from rfl, totK_node, atot6500, atot6503]
  decide +kernel

theorem arows6512 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6512 = true := by
  rw [show D2M8K2.u6512 = KTree.node D2M8K2.u6508 (nat_lit 14023133) (nat_lit 2234956051) (nat_lit 0) D2M8K2.u6511 from rfl, allE_node, arows6508, irow6512, arows6511]
  all_goals rfl

theorem atot6512 : totK PD2M8K2 D2M8K2.u6512 = [792003006946, 2826556569871, 2852385271159, 776338611802, 38783037820, 0, 0, 0] := by
  rw [show D2M8K2.u6512 = KTree.node D2M8K2.u6508 (nat_lit 14023133) (nat_lit 2234956051) (nat_lit 0) D2M8K2.u6511 from rfl, totK_node, atot6508, atot6511]
  decide +kernel

theorem arows6519 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6519 = true := by
  rw [show D2M8K2.u6519 = KTree.node D2M8K2.u6515 (nat_lit 14032378) (nat_lit 2676888301) (nat_lit 0) D2M8K2.u6518 from rfl, allE_node, arows6515, irow6519, arows6518]
  all_goals rfl

theorem atot6519 : totK PD2M8K2 D2M8K2.u6519 = [837222740680, 2969683764664, 2851066782184, 582179180330, 18030242193, 0, 0, 0] := by
  rw [show D2M8K2.u6519 = KTree.node D2M8K2.u6515 (nat_lit 14032378) (nat_lit 2676888301) (nat_lit 0) D2M8K2.u6518 from rfl, totK_node, atot6515, atot6518]
  decide +kernel

theorem arows6530 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6530 = true := by
  rw [show D2M8K2.u6530 = KTree.node D2M8K2.u6526 (nat_lit 14040013) (nat_lit 1391987541) (nat_lit 0) D2M8K2.u6529 from rfl, allE_node, arows6526, irow6530, arows6529]
  all_goals rfl

theorem atot6530 : totK PD2M8K2 D2M8K2.u6530 = [0, 1322956250904, 3577952652333, 2039713137803, 187135613735, 1206465782, 0, 0] := by
  rw [show D2M8K2.u6530 = KTree.node D2M8K2.u6526 (nat_lit 14040013) (nat_lit 1391987541) (nat_lit 0) D2M8K2.u6529 from rfl, totK_node, atot6526, atot6529]
  decide +kernel

theorem arows6537 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6537 = true := by
  rw [show D2M8K2.u6537 = KTree.node D2M8K2.u6533 (nat_lit 14052249) (nat_lit 1741974897) (nat_lit 0) D2M8K2.u6536 from rfl, allE_node, arows6533, irow6537, arows6536]
  all_goals rfl

theorem atot6537 : totK PD2M8K2 D2M8K2.u6537 = [0, 888452456489, 3081687593863, 2600139653269, 484096529696, 17590593026, 0, 0] := by
  rw [show D2M8K2.u6537 = KTree.node D2M8K2.u6533 (nat_lit 14052249) (nat_lit 1741974897) (nat_lit 0) D2M8K2.u6536 from rfl, totK_node, atot6533, atot6536]
  decide +kernel

theorem arows6545 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6545 = true := by
  rw [show D2M8K2.u6545 = KTree.node D2M8K2.u6541 (nat_lit 14061332) (nat_lit 3161835503) (nat_lit 0) D2M8K2.u6544 from rfl, allE_node, arows6541, irow6545, arows6544]
  all_goals rfl

theorem atot6545 : totK PD2M8K2 D2M8K2.u6545 = [802680951956, 2820622703828, 2758781211588, 810494348419, 61529655503, 0, 0, 0] := by
  rw [show D2M8K2.u6545 = KTree.node D2M8K2.u6541 (nat_lit 14061332) (nat_lit 3161835503) (nat_lit 0) D2M8K2.u6544 from rfl, totK_node, atot6541, atot6544]
  decide +kernel

theorem arows6552 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6552 = true := by
  rw [show D2M8K2.u6552 = KTree.node D2M8K2.u6548 (nat_lit 14071249) (nat_lit 1540901483) (nat_lit 0) D2M8K2.u6551 from rfl, allE_node, arows6548, irow6552, arows6551]
  all_goals rfl

theorem atot6552 : totK PD2M8K2 D2M8K2.u6552 = [849262933305, 2871668043085, 2741456754200, 730629034482, 29430033303, 0, 0, 0] := by
  rw [show D2M8K2.u6552 = KTree.node D2M8K2.u6548 (nat_lit 14071249) (nat_lit 1540901483) (nat_lit 0) D2M8K2.u6551 from rfl, totK_node, atot6548, atot6551]
  decide +kernel

theorem arows6561 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6561 = true := by
  rw [show D2M8K2.u6561 = KTree.node D2M8K2.u6557 (nat_lit 14081696) (nat_lit 3250758232) (nat_lit 0) D2M8K2.u6560 from rfl, allE_node, arows6557, irow6561, arows6560]
  all_goals rfl

theorem atot6561 : totK PD2M8K2 D2M8K2.u6561 = [0, 1354929349191, 3595342197553, 1997776076682, 187676325668, 1239866073, 0, 0] := by
  rw [show D2M8K2.u6561 = KTree.node D2M8K2.u6557 (nat_lit 14081696) (nat_lit 3250758232) (nat_lit 0) D2M8K2.u6560 from rfl, totK_node, atot6557, atot6560]
  decide +kernel

theorem arows6568 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6568 = true := by
  rw [show D2M8K2.u6568 = KTree.node D2M8K2.u6564 (nat_lit 14093998) (nat_lit 3296949194) (nat_lit 0) D2M8K2.u6567 from rfl, allE_node, arows6564, irow6568, arows6567]
  all_goals rfl

theorem atot6568 : totK PD2M8K2 D2M8K2.u6568 = [190180602404, 1128957849672, 2775894035335, 2457822533177, 487416021426, 17826068843, 0, 0] := by
  rw [show D2M8K2.u6568 = KTree.node D2M8K2.u6564 (nat_lit 14093998) (nat_lit 3296949194) (nat_lit 0) D2M8K2.u6567 from rfl, totK_node, atot6564, atot6567]
  decide +kernel

theorem arows6576 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6576 = true := by
  rw [show D2M8K2.u6576 = KTree.node D2M8K2.u6572 (nat_lit 14104921) (nat_lit 938319146) (nat_lit 0) D2M8K2.u6575 from rfl, allE_node, arows6572, irow6576, arows6575]
  all_goals rfl

theorem atot6576 : totK PD2M8K2 D2M8K2.u6576 = [775755476807, 2793825345504, 2815688102193, 765834909166, 38779636761, 0, 0, 0] := by
  rw [show D2M8K2.u6576 = KTree.node D2M8K2.u6572 (nat_lit 14104921) (nat_lit 938319146) (nat_lit 0) D2M8K2.u6575 from rfl, totK_node, atot6572, atot6575]
  decide +kernel

theorem arows6583 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6583 = true := by
  rw [show D2M8K2.u6583 = KTree.node D2M8K2.u6579 (nat_lit 14111122) (nat_lit 2891697641) (nat_lit 0) D2M8K2.u6582 from rfl, allE_node, arows6579, irow6583, arows6582]
  all_goals rfl

theorem atot6583 : totK PD2M8K2 D2M8K2.u6583 = [774809918603, 2842813682253, 2842109683349, 665244417532, 26300412495, 0, 0, 0] := by
  rw [show D2M8K2.u6583 = KTree.node D2M8K2.u6579 (nat_lit 14111122) (nat_lit 2891697641) (nat_lit 0) D2M8K2.u6582 from rfl, totK_node, atot6579, atot6582]
  decide +kernel

theorem arows6593 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6593 = true := by
  rw [show D2M8K2.u6593 = KTree.node D2M8K2.u6589 (nat_lit 14121419) (nat_lit 2227814674) (nat_lit 0) D2M8K2.u6592 from rfl, allE_node, arows6589, irow6593, arows6592]
  all_goals rfl

theorem atot6593 : totK PD2M8K2 D2M8K2.u6593 = [357800183586, 1959341155857, 3215036079922, 1487505570093, 139170422740, 1138244013, 0, 0] := by
  rw [show D2M8K2.u6593 = KTree.node D2M8K2.u6589 (nat_lit 14121419) (nat_lit 2227814674) (nat_lit 0) D2M8K2.u6592 from rfl, totK_node, atot6589, atot6592]
  decide +kernel

theorem arows6600 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6600 = true := by
  rw [show D2M8K2.u6600 = KTree.node D2M8K2.u6596 (nat_lit 14131803) (nat_lit 1698987738) (nat_lit 0) D2M8K2.u6599 from rfl, allE_node, arows6596, irow6600, arows6599]
  all_goals rfl

theorem atot6600 : totK PD2M8K2 D2M8K2.u6600 = [0, 1502849377849, 3760431520376, 1802239431642, 110126972137, 0, 0, 0] := by
  rw [show D2M8K2.u6600 = KTree.node D2M8K2.u6596 (nat_lit 14131803) (nat_lit 1698987738) (nat_lit 0) D2M8K2.u6599 from rfl, totK_node, atot6596, atot6599]
  decide +kernel

theorem arows6608 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6608 = true := by
  rw [show D2M8K2.u6608 = KTree.node D2M8K2.u6604 (nat_lit 14185060) (nat_lit 3985178986) (nat_lit 0) D2M8K2.u6607 from rfl, allE_node, arows6604, irow6608, arows6607]
  all_goals rfl

theorem atot6608 : totK PD2M8K2 D2M8K2.u6608 = [0, 844617862733, 3162173868505, 2712229607657, 407360424569, 6346264815, 0, 0] := by
  rw [show D2M8K2.u6608 = KTree.node D2M8K2.u6604 (nat_lit 14185060) (nat_lit 3985178986) (nat_lit 0) D2M8K2.u6607 from rfl, totK_node, atot6604, atot6607]
  decide +kernel

theorem arows6615 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6615 = true := by
  rw [show D2M8K2.u6615 = KTree.node D2M8K2.u6611 (nat_lit 14195680) (nat_lit 1843515472) (nat_lit 0) D2M8K2.u6614 from rfl, allE_node, arows6611, irow6615, arows6614]
  all_goals rfl

theorem atot6615 : totK PD2M8K2 D2M8K2.u6615 = [0, 798503782475, 2846695882051, 2786528873928, 619357411596, 27264272300, 0, 0] := by
  rw [show D2M8K2.u6615 = KTree.node D2M8K2.u6611 (nat_lit 14195680) (nat_lit 1843515472) (nat_lit 0) D2M8K2.u6614 from rfl, totK_node, atot6611, atot6614]
  decide +kernel

theorem arows6624 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6624 = true := by
  rw [show D2M8K2.u6624 = KTree.node D2M8K2.u6620 (nat_lit 14203915) (nat_lit 1212393765) (nat_lit 0) D2M8K2.u6623 from rfl, allE_node, arows6620, irow6624, arows6623]
  all_goals rfl

theorem atot6624 : totK PD2M8K2 D2M8K2.u6624 = [0, 325571517576, 1987606480239, 3287040337123, 1310570127450, 116045609448, 1209030869, 0] := by
  rw [show D2M8K2.u6624 = KTree.node D2M8K2.u6620 (nat_lit 14203915) (nat_lit 1212393765) (nat_lit 0) D2M8K2.u6623 from rfl, totK_node, atot6620, atot6623]
  decide +kernel

theorem arows6631 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6631 = true := by
  rw [show D2M8K2.u6631 = KTree.node D2M8K2.u6627 (nat_lit 14218606) (nat_lit 2371069047) (nat_lit 0) D2M8K2.u6630 from rfl, allE_node, arows6627, irow6631, arows6630]
  all_goals rfl

theorem atot6631 : totK PD2M8K2 D2M8K2.u6631 = [0, 301804903204, 2164289995149, 3482035034699, 1125935949974, 50488844667, 0, 0] := by
  rw [show D2M8K2.u6631 = KTree.node D2M8K2.u6627 (nat_lit 14218606) (nat_lit 2371069047) (nat_lit 0) D2M8K2.u6630 from rfl, totK_node, atot6627, atot6630]
  decide +kernel

theorem arows6639 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6639 = true := by
  rw [show D2M8K2.u6639 = KTree.node D2M8K2.u6635 (nat_lit 14232342) (nat_lit 3534823269) (nat_lit 0) D2M8K2.u6638 from rfl, allE_node, arows6635, irow6639, arows6638]
  all_goals rfl

theorem atot6639 : totK PD2M8K2 D2M8K2.u6639 = [0, 716545585684, 2708419842729, 2928569174214, 867932132233, 49372004117, 0, 0] := by
  rw [show D2M8K2.u6639 = KTree.node D2M8K2.u6635 (nat_lit 14232342) (nat_lit 3534823269) (nat_lit 0) D2M8K2.u6638 from rfl, totK_node, atot6635, atot6638]
  decide +kernel

theorem arows6646 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6646 = true := by
  rw [show D2M8K2.u6646 = KTree.node D2M8K2.u6642 (nat_lit 14239438) (nat_lit 3641012883) (nat_lit 0) D2M8K2.u6645 from rfl, allE_node, arows6642, irow6646, arows6645]
  all_goals rfl

theorem atot6646 : totK PD2M8K2 D2M8K2.u6646 = [0, 884680772743, 3104067228044, 2757146266781, 499873458746, 15920989399, 0, 0] := by
  rw [show D2M8K2.u6646 = KTree.node D2M8K2.u6642 (nat_lit 14239438) (nat_lit 3641012883) (nat_lit 0) D2M8K2.u6645 from rfl, totK_node, atot6642, atot6645]
  decide +kernel

theorem arows6659 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6659 = true := by
  rw [show D2M8K2.u6659 = KTree.node D2M8K2.u6655 (nat_lit 14267942) (nat_lit 3618069051) (nat_lit 0) D2M8K2.u6658 from rfl, allE_node, arows6655, irow6659, arows6658]
  all_goals rfl

theorem atot6659 : totK PD2M8K2 D2M8K2.u6659 = [0, 909104127400, 3094874719007, 2715950677646, 495177116840, 11040709493, 0, 0] := by
  rw [show D2M8K2.u6659 = KTree.node D2M8K2.u6655 (nat_lit 14267942) (nat_lit 3618069051) (nat_lit 0) D2M8K2.u6658 from rfl, totK_node, atot6655, atot6658]
  decide +kernel

theorem arows6666 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6666 = true := by
  rw [show D2M8K2.u6666 = KTree.node D2M8K2.u6662 (nat_lit 14274884) (nat_lit 2033624449) (nat_lit 0) D2M8K2.u6665 from rfl, allE_node, arows6662, irow6666, arows6665]
  all_goals rfl

theorem atot6666 : totK PD2M8K2 D2M8K2.u6666 = [0, 807927892673, 2854110957526, 2862465226295, 704444815314, 28063716506, 0, 0] := by
  rw [show D2M8K2.u6666 = KTree.node D2M8K2.u6662 (nat_lit 14274884) (nat_lit 2033624449) (nat_lit 0) D2M8K2.u6665 from rfl, totK_node, atot6662, atot6665]
  decide +kernel

theorem arows6674 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6674 = true := by
  rw [show D2M8K2.u6674 = KTree.node D2M8K2.u6670 (nat_lit 14285460) (nat_lit 3215872083) (nat_lit 0) D2M8K2.u6673 from rfl, allE_node, arows6670, irow6674, arows6673]
  all_goals rfl

theorem atot6674 : totK PD2M8K2 D2M8K2.u6674 = [0, 790623939011, 2969649475803, 2858957922210, 536203534518, 11171927303, 0, 0] := by
  rw [show D2M8K2.u6674 = KTree.node D2M8K2.u6670 (nat_lit 14285460) (nat_lit 3215872083) (nat_lit 0) D2M8K2.u6673 from rfl, totK_node, atot6670, atot6673]
  decide +kernel

theorem arows6681 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6681 = true := by
  rw [show D2M8K2.u6681 = KTree.node D2M8K2.u6677 (nat_lit 14314059) (nat_lit 3730294825) (nat_lit 0) D2M8K2.u6680 from rfl, allE_node, arows6677, irow6681, arows6680]
  all_goals rfl

theorem atot6681 : totK PD2M8K2 D2M8K2.u6681 = [0, 831999324920, 3007802751980, 2858673050633, 584541051362, 16245083475, 0, 0] := by
  rw [show D2M8K2.u6681 = KTree.node D2M8K2.u6677 (nat_lit 14314059) (nat_lit 3730294825) (nat_lit 0) D2M8K2.u6680 from rfl, totK_node, atot6677, atot6680]
  decide +kernel

theorem arows6690 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6690 = true := by
  rw [show D2M8K2.u6690 = KTree.node D2M8K2.u6686 (nat_lit 14323972) (nat_lit 3754342309) (nat_lit 0) D2M8K2.u6689 from rfl, allE_node, arows6686, irow6690, arows6689]
  all_goals rfl

theorem atot6690 : totK PD2M8K2 D2M8K2.u6690 = [0, 831929758797, 2950678702464, 2752034488035, 551808435761, 18299087694, 0, 0] := by
  rw [show D2M8K2.u6690 = KTree.node D2M8K2.u6686 (nat_lit 14323972) (nat_lit 3754342309) (nat_lit 0) D2M8K2.u6689 from rfl, totK_node, atot6686, atot6689]
  decide +kernel

theorem arows6697 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6697 = true := by
  rw [show D2M8K2.u6697 = KTree.node D2M8K2.u6693 (nat_lit 14355403) (nat_lit 1815681041) (nat_lit 0) D2M8K2.u6696 from rfl, allE_node, arows6693, irow6697, arows6696]
  all_goals rfl

theorem atot6697 : totK PD2M8K2 D2M8K2.u6697 = [0, 841607724646, 2942821208357, 2789320117098, 613929103063, 24840097184, 0, 0] := by
  rw [show D2M8K2.u6697 = KTree.node D2M8K2.u6693 (nat_lit 14355403) (nat_lit 1815681041) (nat_lit 0) D2M8K2.u6696 from rfl, totK_node, atot6693, atot6696]
  decide +kernel

theorem arows6705 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6705 = true := by
  rw [show D2M8K2.u6705 = KTree.node D2M8K2.u6701 (nat_lit 14362273) (nat_lit 1549666246) (nat_lit 0) D2M8K2.u6704 from rfl, allE_node, arows6701, irow6705, arows6704]
  all_goals rfl

theorem atot6705 : totK PD2M8K2 D2M8K2.u6705 = [0, 843162022478, 2904293107457, 2762064060971, 604235848628, 25986871446, 0, 0] := by
  rw [show D2M8K2.u6705 = KTree.node D2M8K2.u6701 (nat_lit 14362273) (nat_lit 1549666246) (nat_lit 0) D2M8K2.u6704 from rfl, totK_node, atot6701, atot6704]
  decide +kernel

theorem arows6712 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6712 = true := by
  rw [show D2M8K2.u6712 = KTree.node D2M8K2.u6708 (nat_lit 14372731) (nat_lit 2097673222) (nat_lit 0) D2M8K2.u6711 from rfl, allE_node, arows6708, irow6712, arows6711]
  all_goals rfl

theorem atot6712 : totK PD2M8K2 D2M8K2.u6712 = [0, 0, 1431408329083, 3655548188849, 1771593466841, 160053942818, 1138244013, 0] := by
  rw [show D2M8K2.u6712 = KTree.node D2M8K2.u6708 (nat_lit 14372731) (nat_lit 2097673222) (nat_lit 0) D2M8K2.u6711 from rfl, totK_node, atot6708, atot6711]
  decide +kernel

theorem arows6722 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6722 = true := by
  rw [show D2M8K2.u6722 = KTree.node D2M8K2.u6718 (nat_lit 14384754) (nat_lit 3430439555) (nat_lit 0) D2M8K2.u6721 from rfl, allE_node, arows6718, irow6722, arows6721]
  all_goals rfl

theorem atot6722 : totK PD2M8K2 D2M8K2.u6722 = [306235076213, 721791207661, 1268771548050, 2757463895133, 1755942722247, 251423214348, 4977114383, 0] := by
  rw [show D2M8K2.u6722 = KTree.node D2M8K2.u6718 (nat_lit 14384754) (nat_lit 3430439555) (nat_lit 0) D2M8K2.u6721 from rfl, totK_node, atot6718, atot6721]
  decide +kernel

theorem arows6729 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6729 = true := by
  rw [show D2M8K2.u6729 = KTree.node D2M8K2.u6725 (nat_lit 14440517) (nat_lit 2352245897) (nat_lit 0) D2M8K2.u6728 from rfl, allE_node, arows6725, irow6729, arows6728]
  all_goals rfl

theorem atot6729 : totK PD2M8K2 D2M8K2.u6729 = [835809691657, 3028870003948, 2788867975263, 524741064309, 14418877666, 0, 0, 0] := by
  rw [show D2M8K2.u6729 = KTree.node D2M8K2.u6725 (nat_lit 14440517) (nat_lit 2352245897) (nat_lit 0) D2M8K2.u6728 from rfl, totK_node, atot6725, atot6728]
  decide +kernel

theorem arows6737 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6737 = true := by
  rw [show D2M8K2.u6737 = KTree.node D2M8K2.u6733 (nat_lit 14447820) (nat_lit 3595499130) (nat_lit 0) D2M8K2.u6736 from rfl, allE_node, arows6733, irow6737, arows6736]
  all_goals rfl

theorem atot6737 : totK PD2M8K2 D2M8K2.u6737 = [836559489246, 2924140265494, 2774040709741, 597322725085, 19499939523, 0, 0, 0] := by
  rw [show D2M8K2.u6737 = KTree.node D2M8K2.u6733 (nat_lit 14447820) (nat_lit 3595499130) (nat_lit 0) D2M8K2.u6736 from rfl, totK_node, atot6733, atot6736]
  decide +kernel

theorem arows6744 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6744 = true := by
  rw [show D2M8K2.u6744 = KTree.node D2M8K2.u6740 (nat_lit 14454655) (nat_lit 2384245380) (nat_lit 0) D2M8K2.u6743 from rfl, allE_node, arows6740, irow6744, arows6743]
  all_goals rfl

theorem atot6744 : totK PD2M8K2 D2M8K2.u6744 = [0, 1267442356242, 3536045241687, 2045051932993, 211763842377, 1369150432, 0, 0] := by
  rw [show D2M8K2.u6744 = KTree.node D2M8K2.u6740 (nat_lit 14454655) (nat_lit 2384245380) (nat_lit 0) D2M8K2.u6743 from rfl, totK_node, atot6740, atot6743]
  decide +kernel

theorem arows6753 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6753 = true := by
  rw [show D2M8K2.u6753 = KTree.node D2M8K2.u6749 (nat_lit 14470608) (nat_lit 2771586509) (nat_lit 0) D2M8K2.u6752 from rfl, allE_node, arows6749, irow6753, arows6752]
  all_goals rfl

theorem atot6753 : totK PD2M8K2 D2M8K2.u6753 = [438692147823, 2067532619202, 3237472072242, 1379685738656, 77151914618, 0, 0, 0] := by
  rw [show D2M8K2.u6753 = KTree.node D2M8K2.u6749 (nat_lit 14470608) (nat_lit 2771586509) (nat_lit 0) D2M8K2.u6752 from rfl, totK_node, atot6749, atot6752]
  decide +kernel

theorem arows6760 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6760 = true := by
  rw [show D2M8K2.u6760 = KTree.node D2M8K2.u6756 (nat_lit 14481482) (nat_lit 3991495440) (nat_lit 0) D2M8K2.u6759 from rfl, allE_node, arows6756, irow6760, arows6759]
  all_goals rfl

theorem atot6760 : totK PD2M8K2 D2M8K2.u6760 = [653760292902, 2619953544685, 3022048911089, 930732745498, 50615285690, 0, 0, 0] := by
  rw [show D2M8K2.u6760 = KTree.node D2M8K2.u6756 (nat_lit 14481482) (nat_lit 3991495440) (nat_lit 0) D2M8K2.u6759 from rfl, totK_node, atot6756, atot6759]
  decide +kernel

theorem arows6768 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6768 = true := by
  rw [show D2M8K2.u6768 = KTree.node D2M8K2.u6764 (nat_lit 14488756) (nat_lit 3992702721) (nat_lit 0) D2M8K2.u6767 from rfl, allE_node, arows6764, irow6768, arows6767]
  all_goals rfl

theorem atot6768 : totK PD2M8K2 D2M8K2.u6768 = [911046264957, 3109155558493, 2759315491002, 521959393495, 15923181188, 0, 0, 0] := by
  rw [show D2M8K2.u6768 = KTree.node D2M8K2.u6764 (nat_lit 14488756) (nat_lit 3992702721) (nat_lit 0) D2M8K2.u6767 from rfl, totK_node, atot6764, atot6767]
  decide +kernel

theorem arows6775 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6775 = true := by
  rw [show D2M8K2.u6775 = KTree.node D2M8K2.u6771 (nat_lit 14499408) (nat_lit 3168181223) (nat_lit 0) D2M8K2.u6774 from rfl, allE_node, arows6771, irow6775, arows6774]
  all_goals rfl

theorem atot6775 : totK PD2M8K2 D2M8K2.u6775 = [0, 1081162658499, 3087782267632, 2402261206377, 622771912134, 36921873854, 0, 0] := by
  rw [show D2M8K2.u6775 = KTree.node D2M8K2.u6771 (nat_lit 14499408) (nat_lit 3168181223) (nat_lit 0) D2M8K2.u6774 from rfl, totK_node, atot6771, atot6774]
  decide +kernel

theorem arows6786 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6786 = true := by
  rw [show D2M8K2.u6786 = KTree.node D2M8K2.u6782 (nat_lit 14506059) (nat_lit 3633924771) (nat_lit 0) D2M8K2.u6785 from rfl, allE_node, arows6782, irow6786, arows6785]
  all_goals rfl

theorem atot6786 : totK PD2M8K2 D2M8K2.u6786 = [0, 880874654029, 3097009601845, 2766666450840, 502769944292, 10378741320, 0, 0] := by
  rw [show D2M8K2.u6786 = KTree.node D2M8K2.u6782 (nat_lit 14506059) (nat_lit 3633924771) (nat_lit 0) D2M8K2.u6785 from rfl, totK_node, atot6782, atot6785]
  decide +kernel

theorem arows6793 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6793 = true := by
  rw [show D2M8K2.u6793 = KTree.node D2M8K2.u6789 (nat_lit 14514086) (nat_lit 4113132171) (nat_lit 0) D2M8K2.u6792 from rfl, allE_node, arows6789, irow6793, arows6792]
  all_goals rfl

theorem atot6793 : totK PD2M8K2 D2M8K2.u6793 = [407993187048, 1588464409741, 2615603374990, 2129766116781, 453240409954, 10717512769, 0, 0] := by
  rw [show D2M8K2.u6793 = KTree.node D2M8K2.u6789 (nat_lit 14514086) (nat_lit 4113132171) (nat_lit 0) D2M8K2.u6792 from rfl, totK_node, atot6789, atot6792]
  decide +kernel

theorem arows6801 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6801 = true := by
  rw [show D2M8K2.u6801 = KTree.node D2M8K2.u6797 (nat_lit 14521081) (nat_lit 1363912447) (nat_lit 0) D2M8K2.u6800 from rfl, allE_node, arows6797, irow6801, arows6800]
  all_goals rfl

theorem atot6801 : totK PD2M8K2 D2M8K2.u6801 = [860640141963, 2946805271858, 2758795919754, 709970439853, 37410254603, 0, 0, 0] := by
  rw [show D2M8K2.u6801 = KTree.node D2M8K2.u6797 (nat_lit 14521081) (nat_lit 1363912447) (nat_lit 0) D2M8K2.u6800 from rfl, totK_node, atot6797, atot6800]
  decide +kernel

theorem arows6808 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6808 = true := by
  rw [show D2M8K2.u6808 = KTree.node D2M8K2.u6804 (nat_lit 14530996) (nat_lit 3400185284) (nat_lit 0) D2M8K2.u6807 from rfl, allE_node, arows6804, irow6808, arows6807]
  all_goals rfl

theorem atot6808 : totK PD2M8K2 D2M8K2.u6808 = [771091638455, 2870935695086, 2933185764901, 649196080226, 19298981496, 0, 0, 0] := by
  rw [show D2M8K2.u6808 = KTree.node D2M8K2.u6804 (nat_lit 14530996) (nat_lit 3400185284) (nat_lit 0) D2M8K2.u6807 from rfl, totK_node, atot6804, atot6807]
  decide +kernel

theorem arows6817 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6817 = true := by
  rw [show D2M8K2.u6817 = KTree.node D2M8K2.u6813 (nat_lit 14537913) (nat_lit 1653160814) (nat_lit 0) D2M8K2.u6816 from rfl, allE_node, arows6813, irow6817, arows6816]
  all_goals rfl

theorem atot6817 : totK PD2M8K2 D2M8K2.u6817 = [0, 1271864570664, 3568106608059, 2113291720587, 199078609540, 1206465782, 0, 0] := by
  rw [show D2M8K2.u6817 = KTree.node D2M8K2.u6813 (nat_lit 14537913) (nat_lit 1653160814) (nat_lit 0) D2M8K2.u6816 from rfl, totK_node, atot6813, atot6816]
  decide +kernel

theorem arows6824 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6824 = true := by
  rw [show D2M8K2.u6824 = KTree.node D2M8K2.u6820 (nat_lit 14550175) (nat_lit 1612297973) (nat_lit 0) D2M8K2.u6823 from rfl, allE_node, arows6820, irow6824, arows6823]
  all_goals rfl

theorem atot6824 : totK PD2M8K2 D2M8K2.u6824 = [0, 907247713957, 3079219529234, 2620336979929, 491383062654, 17590593026, 0, 0] := by
  rw [show D2M8K2.u6824 = KTree.node D2M8K2.u6820 (nat_lit 14550175) (nat_lit 1612297973) (nat_lit 0) D2M8K2.u6823 from rfl, totK_node, atot6820, atot6823]
  decide +kernel

theorem arows6832 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6832 = true := by
  rw [show D2M8K2.u6832 = KTree.node D2M8K2.u6828 (nat_lit 14559626) (nat_lit 3243404047) (nat_lit 0) D2M8K2.u6831 from rfl, allE_node, arows6828, irow6832, arows6831]
  all_goals rfl

theorem atot6832 : totK PD2M8K2 D2M8K2.u6832 = [804453684306, 2828510624997, 2781540755299, 783773557034, 47050702456, 0, 0, 0] := by
  rw [show D2M8K2.u6832 = KTree.node D2M8K2.u6828 (nat_lit 14559626) (nat_lit 3243404047) (nat_lit 0) D2M8K2.u6831 from rfl, totK_node, atot6828, atot6831]
  decide +kernel

theorem arows6839 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6839 = true := by
  rw [show D2M8K2.u6839 = KTree.node D2M8K2.u6835 (nat_lit 14569671) (nat_lit 3424066818) (nat_lit 0) D2M8K2.u6838 from rfl, allE_node, arows6835, irow6839, arows6838]
  all_goals rfl

theorem atot6839 : totK PD2M8K2 D2M8K2.u6839 = [853567632206, 2907753744542, 2786496205136, 679174252266, 23873293363, 0, 0, 0] := by
  rw [show D2M8K2.u6839 = KTree.node D2M8K2.u6835 (nat_lit 14569671) (nat_lit 3424066818) (nat_lit 0) D2M8K2.u6838 from rfl, totK_node, atot6835, atot6838]
  decide +kernel

theorem arows6849 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6849 = true := by
  rw [show D2M8K2.u6849 = KTree.node D2M8K2.u6845 (nat_lit 14579383) (nat_lit 2027145116) (nat_lit 0) D2M8K2.u6848 from rfl, allE_node, arows6845, irow6849, arows6848]
  all_goals rfl

theorem atot6849 : totK PD2M8K2 D2M8K2.u6849 = [0, 1264483502223, 3549699956409, 2140493884572, 204853585639, 1239866073, 0, 0] := by
  rw [show D2M8K2.u6849 = KTree.node D2M8K2.u6845 (nat_lit 14579383) (nat_lit 2027145116) (nat_lit 0) D2M8K2.u6848 from rfl, totK_node, atot6845, atot6848]
  decide +kernel

theorem arows6856 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6856 = true := by
  rw [show D2M8K2.u6856 = KTree.node D2M8K2.u6852 (nat_lit 14595163) (nat_lit 1697544779) (nat_lit 0) D2M8K2.u6855 from rfl, allE_node, arows6852, irow6856, arows6855]
  all_goals rfl

theorem atot6856 : totK PD2M8K2 D2M8K2.u6856 = [414024072134, 1773630400454, 2767678229272, 1845967046898, 343509228904, 13105450397, 0, 0] := by
  rw [show D2M8K2.u6856 = KTree.node D2M8K2.u6852 (nat_lit 14595163) (nat_lit 1697544779) (nat_lit 0) D2M8K2.u6855 from rfl, totK_node, atot6852, atot6855]
  decide +kernel

theorem arows6864 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6864 = true := by
  rw [show D2M8K2.u6864 = KTree.node D2M8K2.u6860 (nat_lit 14645261) (nat_lit 2175808801) (nat_lit 0) D2M8K2.u6863 from rfl, allE_node, arows6860, irow6864, arows6863]
  all_goals rfl

theorem atot6864 : totK PD2M8K2 D2M8K2.u6864 = [812475601820, 2822774019956, 2816304656462, 764675194395, 38739841348, 0, 0, 0] := by
  rw [show D2M8K2.u6864 = KTree.node D2M8K2.u6860 (nat_lit 14645261) (nat_lit 2175808801) (nat_lit 0) D2M8K2.u6863 from rfl, totK_node, atot6860, atot6863]
  decide +kernel

theorem arows6871 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6871 = true := by
  rw [show D2M8K2.u6871 = KTree.node D2M8K2.u6867 (nat_lit 14651471) (nat_lit 2155777725) (nat_lit 0) D2M8K2.u6870 from rfl, allE_node, arows6867, irow6871, arows6870]
  all_goals rfl

theorem atot6871 : totK PD2M8K2 D2M8K2.u6871 = [791481769124, 2892793815195, 2868805355384, 646337561281, 23592355398, 0, 0, 0] := by
  rw [show D2M8K2.u6871 = KTree.node D2M8K2.u6867 (nat_lit 14651471) (nat_lit 2155777725) (nat_lit 0) D2M8K2.u6870 from rfl, totK_node, atot6867, atot6870]
  decide +kernel

theorem arows6880 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6880 = true := by
  rw [show D2M8K2.u6880 = KTree.node D2M8K2.u6876 (nat_lit 14661452) (nat_lit 2305161926) (nat_lit 0) D2M8K2.u6879 from rfl, allE_node, arows6876, irow6880, arows6879]
  all_goals rfl

theorem atot6880 : totK PD2M8K2 D2M8K2.u6880 = [93924006320, 1448976698543, 3422178354390, 2005205188632, 189661598861, 1310285577, 0, 0] := by
  rw [show D2M8K2.u6880 = KTree.node D2M8K2.u6876 (nat_lit 14661452) (nat_lit 2305161926) (nat_lit 0) D2M8K2.u6879 from rfl, totK_node, atot6876, atot6879]
  decide +kernel

theorem arows6887 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6887 = true := by
  rw [show D2M8K2.u6887 = KTree.node D2M8K2.u6883 (nat_lit 14669810) (nat_lit 2519127889) (nat_lit 0) D2M8K2.u6886 from rfl, allE_node, arows6883, irow6887, arows6886]
  all_goals rfl

theorem atot6887 : totK PD2M8K2 D2M8K2.u6887 = [0, 911687957942, 3160755402148, 2625789309068, 422685684855, 9811245038, 0, 0] := by
  rw [show D2M8K2.u6887 = KTree.node D2M8K2.u6883 (nat_lit 14669810) (nat_lit 2519127889) (nat_lit 0) D2M8K2.u6886 from rfl, totK_node, atot6883, atot6886]
  decide +kernel

theorem arows6895 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6895 = true := by
  rw [show D2M8K2.u6895 = KTree.node D2M8K2.u6891 (nat_lit 14680395) (nat_lit 2382349830) (nat_lit 0) D2M8K2.u6894 from rfl, allE_node, arows6891, irow6895, arows6894]
  all_goals rfl

theorem atot6895 : totK PD2M8K2 D2M8K2.u6895 = [0, 878958241298, 3003539764846, 2704968354304, 572243269326, 23120318498, 0, 0] := by
  rw [show D2M8K2.u6895 = KTree.node D2M8K2.u6891 (nat_lit 14680395) (nat_lit 2382349830) (nat_lit 0) D2M8K2.u6894 from rfl, totK_node, atot6891, atot6894]
  decide +kernel

theorem arows6902 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6902 = true := by
  rw [show D2M8K2.u6902 = KTree.node D2M8K2.u6898 (nat_lit 14690965) (nat_lit 1033499943) (nat_lit 0) D2M8K2.u6901 from rfl, allE_node, arows6898, irow6902, arows6901]
  all_goals rfl

theorem atot6902 : totK PD2M8K2 D2M8K2.u6902 = [0, 807086392746, 2971137626367, 2856026662726, 528174581741, 10401747658, 0, 0] := by
  rw [show D2M8K2.u6902 = KTree.node D2M8K2.u6898 (nat_lit 14690965) (nat_lit 1033499943) (nat_lit 0) D2M8K2.u6901 from rfl, totK_node, atot6898, atot6901]
  decide +kernel

theorem arows6914 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6914 = true := by
  rw [show D2M8K2.u6914 = KTree.node D2M8K2.u6910 (nat_lit 14699095) (nat_lit 1178680481) (nat_lit 0) D2M8K2.u6913 from rfl, allE_node, arows6910, irow6914, arows6913]
  all_goals rfl

theorem atot6914 : totK PD2M8K2 D2M8K2.u6914 = [0, 734385748217, 2824001573198, 2887114762033, 663485621565, 24382714630, 0, 0] := by
  rw [show D2M8K2.u6914 = KTree.node D2M8K2.u6910 (nat_lit 14699095) (nat_lit 1178680481) (nat_lit 0) D2M8K2.u6913 from rfl, totK_node, atot6910, atot6913]
  decide +kernel

theorem arows6921 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6921 = true := by
  rw [show D2M8K2.u6921 = KTree.node D2M8K2.u6917 (nat_lit 14709467) (nat_lit 2341033152) (nat_lit 0) D2M8K2.u6920 from rfl, allE_node, arows6917, irow6921, arows6920]
  all_goals rfl

theorem atot6921 : totK PD2M8K2 D2M8K2.u6921 = [0, 0, 1253181498125, 3608353043863, 1951713737231, 160609731912, 1369150432, 0] := by
  rw [show D2M8K2.u6921 = KTree.node D2M8K2.u6917 (nat_lit 14709467) (nat_lit 2341033152) (nat_lit 0) D2M8K2.u6920 from rfl, totK_node, atot6917, atot6920]
  decide +kernel

theorem arows6929 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6929 = true := by
  rw [show D2M8K2.u6929 = KTree.node D2M8K2.u6925 (nat_lit 14726860) (nat_lit 3917049186) (nat_lit 0) D2M8K2.u6928 from rfl, allE_node, arows6925, irow6929, arows6928]
  all_goals rfl

theorem atot6929 : totK PD2M8K2 D2M8K2.u6929 = [0, 510578905355, 2217289965565, 3165502535304, 1242574328165, 69324332644, 0, 0] := by
  rw [show D2M8K2.u6929 = KTree.node D2M8K2.u6925 (nat_lit 14726860) (nat_lit 3917049186) (nat_lit 0) D2M8K2.u6928 from rfl, totK_node, atot6925, atot6928]
  decide +kernel

theorem arows6936 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6936 = true := by
  rw [show D2M8K2.u6936 = KTree.node D2M8K2.u6932 (nat_lit 14733070) (nat_lit 3974057838) (nat_lit 0) D2M8K2.u6935 from rfl, allE_node, arows6932, irow6936, arows6935]
  all_goals rfl

theorem atot6936 : totK PD2M8K2 D2M8K2.u6936 = [0, 824574647318, 2944045999849, 2856770385978, 633877798507, 18246739283, 0, 0] := by
  rw [show D2M8K2.u6936 = KTree.node D2M8K2.u6932 (nat_lit 14733070) (nat_lit 3974057838) (nat_lit 0) D2M8K2.u6935 from rfl, totK_node, atot6932, atot6935]
  decide +kernel

theorem arows6945 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6945 = true := by
  rw [show D2M8K2.u6945 = KTree.node D2M8K2.u6941 (nat_lit 14740720) (nat_lit 2098822613) (nat_lit 0) D2M8K2.u6944 from rfl, allE_node, arows6941, irow6945, arows6944]
  all_goals rfl

theorem atot6945 : totK PD2M8K2 D2M8K2.u6945 = [0, 863236077338, 2983101874167, 2757948324982, 614961275992, 23360397894, 0, 0] := by
  rw [show D2M8K2.u6945 = KTree.node D2M8K2.u6941 (nat_lit 14740720) (nat_lit 2098822613) (nat_lit 0) D2M8K2.u6944 from rfl, totK_node, atot6941, atot6944]
  decide +kernel

theorem arows6952 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6952 = true := by
  rw [show D2M8K2.u6952 = KTree.node D2M8K2.u6948 (nat_lit 14768599) (nat_lit 1870788255) (nat_lit 0) D2M8K2.u6951 from rfl, allE_node, arows6948, irow6952, arows6951]
  all_goals rfl

theorem atot6952 : totK PD2M8K2 D2M8K2.u6952 = [0, 806136517554, 2861472294620, 2801934248676, 727444300875, 34133982247, 0, 0] := by
  rw [show D2M8K2.u6952 = KTree.node D2M8K2.u6948 (nat_lit 14768599) (nat_lit 1870788255) (nat_lit 0) D2M8K2.u6951 from rfl, totK_node, atot6948, atot6951]
  decide +kernel

theorem arows6960 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6960 = true := by
  rw [show D2M8K2.u6960 = KTree.node D2M8K2.u6956 (nat_lit 14778206) (nat_lit 3923990087) (nat_lit 0) D2M8K2.u6959 from rfl, allE_node, arows6956, irow6960, arows6959]
  all_goals rfl

theorem atot6960 : totK PD2M8K2 D2M8K2.u6960 = [0, 870954003506, 3020346350520, 2776346127876, 537662970787, 17832790025, 0, 0] := by
  rw [show D2M8K2.u6960 = KTree.node D2M8K2.u6956 (nat_lit 14778206) (nat_lit 3923990087) (nat_lit 0) D2M8K2.u6959 from rfl, totK_node, atot6956, atot6959]
  decide +kernel

theorem arows6967 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6967 = true := by
  rw [show D2M8K2.u6967 = KTree.node D2M8K2.u6963 (nat_lit 14785640) (nat_lit 3310341559) (nat_lit 0) D2M8K2.u6966 from rfl, allE_node, arows6963, irow6967, arows6966]
  all_goals rfl

theorem atot6967 : totK PD2M8K2 D2M8K2.u6967 = [0, 164699952579, 1700295529369, 3459427066202, 1650670446264, 124758210568, 1166720416, 0] := by
  rw [show D2M8K2.u6967 = KTree.node D2M8K2.u6963 (nat_lit 14785640) (nat_lit 3310341559) (nat_lit 0) D2M8K2.u6966 from rfl, totK_node, atot6963, atot6966]
  decide +kernel

theorem arows6977 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6977 = true := by
  rw [show D2M8K2.u6977 = KTree.node D2M8K2.u6973 (nat_lit 14798610) (nat_lit 3084651784) (nat_lit 0) D2M8K2.u6976 from rfl, allE_node, arows6973, irow6977, arows6976]
  all_goals rfl

theorem atot6977 : totK PD2M8K2 D2M8K2.u6977 = [0, 89204917003, 1322919604975, 3374610494230, 2021325316376, 246993620717, 5134755853, 0] := by
  rw [show D2M8K2.u6977 = KTree.node D2M8K2.u6973 (nat_lit 14798610) (nat_lit 3084651784) (nat_lit 0) D2M8K2.u6976 from rfl, totK_node, atot6973, atot6976]
  decide +kernel

theorem arows6984 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6984 = true := by
  rw [show D2M8K2.u6984 = KTree.node D2M8K2.u6980 (nat_lit 14809667) (nat_lit 2939354780) (nat_lit 0) D2M8K2.u6983 from rfl, allE_node, arows6980, irow6984, arows6983]
  all_goals rfl

theorem atot6984 : totK PD2M8K2 D2M8K2.u6984 = [0, 798953652932, 2862380331731, 2801489998352, 720704538986, 34174735767, 0, 0] := by
  rw [show D2M8K2.u6984 = KTree.node D2M8K2.u6980 (nat_lit 14809667) (nat_lit 2939354780) (nat_lit 0) D2M8K2.u6983 from rfl, totK_node, atot6980, atot6983]
  decide +kernel

theorem arows6992 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6992 = true := by
  rw [show D2M8K2.u6992 = KTree.node D2M8K2.u6988 (nat_lit 14822845) (nat_lit 1220959258) (nat_lit 0) D2M8K2.u6991 from rfl, allE_node, arows6988, irow6992, arows6991]
  all_goals rfl

theorem atot6992 : totK PD2M8K2 D2M8K2.u6992 = [0, 768514840026, 2862622135441, 2888409799279, 672117060006, 21831948830, 0, 0] := by
  rw [show D2M8K2.u6992 = KTree.node D2M8K2.u6988 (nat_lit 14822845) (nat_lit 1220959258) (nat_lit 0) D2M8K2.u6991 from rfl, totK_node, atot6988, atot6991]
  decide +kernel

theorem arows6999 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6999 = true := by
  rw [show D2M8K2.u6999 = KTree.node D2M8K2.u6995 (nat_lit 14830212) (nat_lit 1372710191) (nat_lit 0) D2M8K2.u6998 from rfl, allE_node, arows6995, irow6999, arows6998]
  all_goals rfl

theorem atot6999 : totK PD2M8K2 D2M8K2.u6999 = [0, 0, 1249394208325, 3523051477398, 2102975040101, 198615863715, 2335892675, 0] := by
  rw [show D2M8K2.u6999 = KTree.node D2M8K2.u6995 (nat_lit 14830212) (nat_lit 1372710191) (nat_lit 0) D2M8K2.u6998 from rfl, totK_node, atot6995, atot6998]
  decide +kernel

theorem arows7008 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7008 = true := by
  rw [show D2M8K2.u7008 = KTree.node D2M8K2.u7004 (nat_lit 14889086) (nat_lit 3654276182) (nat_lit 0) D2M8K2.u7007 from rfl, allE_node, arows7004, irow7008, arows7007]
  all_goals rfl

theorem atot7008 : totK PD2M8K2 D2M8K2.u7008 = [0, 594081262602, 2314511386013, 2848488233552, 1233667538808, 163189224055, 4028038878, 0] := by
  rw [show D2M8K2.u7008 = KTree.node D2M8K2.u7004 (nat_lit 14889086) (nat_lit 3654276182) (nat_lit 0) D2M8K2.u7007 from rfl, totK_node, atot7004, atot7007]
  decide +kernel

theorem arows7015 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7015 = true := by
  rw [show D2M8K2.u7015 = KTree.node D2M8K2.u7011 (nat_lit 14895511) (nat_lit 2086106863) (nat_lit 0) D2M8K2.u7014 from rfl, allE_node, arows7011, irow7015, arows7014]
  all_goals rfl

theorem atot7015 : totK PD2M8K2 D2M8K2.u7015 = [0, 730679526958, 2674867437392, 2895127148954, 844695874953, 38965028177, 0, 0] := by
  rw [show D2M8K2.u7015 = KTree.node D2M8K2.u7011 (nat_lit 14895511) (nat_lit 2086106863) (nat_lit 0) D2M8K2.u7014 from rfl, totK_node, atot7011, atot7014]
  decide +kernel

theorem arows7023 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7023 = true := by
  rw [show D2M8K2.u7023 = KTree.node D2M8K2.u7019 (nat_lit 14905854) (nat_lit 3853262279) (nat_lit 0) D2M8K2.u7022 from rfl, allE_node, arows7019, irow7023, arows7022]
  all_goals rfl

theorem atot7023 : totK PD2M8K2 D2M8K2.u7023 = [0, 785303906976, 2893953545550, 2878345933165, 637298943459, 17367429453, 0, 0] := by
  rw [show D2M8K2.u7023 = KTree.node D2M8K2.u7019 (nat_lit 14905854) (nat_lit 3853262279) (nat_lit 0) D2M8K2.u7022 from rfl, totK_node, atot7019, atot7022]
  decide +kernel

theorem arows7030 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7030 = true := by
  rw [show D2M8K2.u7030 = KTree.node D2M8K2.u7026 (nat_lit 14912981) (nat_lit 2380560630) (nat_lit 0) D2M8K2.u7029 from rfl, allE_node, arows7026, irow7030, arows7029]
  all_goals rfl

theorem atot7030 : totK PD2M8K2 D2M8K2.u7030 = [0, 0, 1282622816484, 3536978884462, 2058886548016, 194795897919, 1288491354, 0] := by
  rw [show D2M8K2.u7030 = KTree.node D2M8K2.u7026 (nat_lit 14912981) (nat_lit 2380560630) (nat_lit 0) D2M8K2.u7029 from rfl, totK_node, atot7026, atot7029]
  decide +kernel

theorem arows7041 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7041 = true := by
  rw [show D2M8K2.u7041 = KTree.node D2M8K2.u7037 (nat_lit 14921392) (nat_lit 1635561807) (nat_lit 0) D2M8K2.u7040 from rfl, allE_node, arows7037, irow7041, arows7040]
  all_goals rfl

theorem atot7041 : totK PD2M8K2 D2M8K2.u7041 = [0, 0, 840005913749, 3065757262220, 2657987700488, 447475391398, 10867436183, 0] := by
  rw [show D2M8K2.u7041 = KTree.node D2M8K2.u7037 (nat_lit 14921392) (nat_lit 1635561807) (nat_lit 0) D2M8K2.u7040 from rfl, totK_node, atot7037, atot7040]
  decide +kernel

theorem arows7048 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7048 = true := by
  rw [show D2M8K2.u7048 = KTree.node D2M8K2.u7044 (nat_lit 14931595) (nat_lit 1585110918) (nat_lit 0) D2M8K2.u7047 from rfl, allE_node, arows7044, irow7048, arows7047]
  all_goals rfl

theorem atot7048 : totK PD2M8K2 D2M8K2.u7048 = [0, 863604381076, 2693014157579, 2298917277010, 1012222085834, 318325310533, 20509029466, 0] := by
  rw [show D2M8K2.u7048 = KTree.node D2M8K2.u7044 (nat_lit 14931595) (nat_lit 1585110918) (nat_lit 0) D2M8K2.u7047 from rfl, totK_node, atot7044, atot7047]
  decide +kernel

theorem arows7056 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7056 = true := by
  rw [show D2M8K2.u7056 = KTree.node D2M8K2.u7052 (nat_lit 14942094) (nat_lit 4016684338) (nat_lit 0) D2M8K2.u7055 from rfl, allE_node, arows7052, irow7056, arows7055]
  all_goals rfl

theorem atot7056 : totK PD2M8K2 D2M8K2.u7056 = [0, 814154424544, 2857694386461, 2761384999430, 626045774930, 26300412495, 0, 0] := by
  rw [show D2M8K2.u7056 = KTree.node D2M8K2.u7052 (nat_lit 14942094) (nat_lit 4016684338) (nat_lit 0) D2M8K2.u7055 from rfl, totK_node, atot7052, atot7055]
  decide +kernel

theorem arows7063 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7063 = true := by
  rw [show D2M8K2.u7063 = KTree.node D2M8K2.u7059 (nat_lit 14949001) (nat_lit 1512170416) (nat_lit 0) D2M8K2.u7062 from rfl, allE_node, arows7059, irow7063, arows7062]
  all_goals rfl

theorem atot7063 : totK PD2M8K2 D2M8K2.u7063 = [0, 419234341778, 2297276820240, 3317237177784, 1037423322525, 48846355329, 0, 0] := by
  rw [show D2M8K2.u7063 = KTree.node D2M8K2.u7059 (nat_lit 14949001) (nat_lit 1512170416) (nat_lit 0) D2M8K2.u7062 from rfl, totK_node, atot7059, atot7062]
  decide +kernel

theorem arows7072 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7072 = true := by
  rw [show D2M8K2.u7072 = KTree.node D2M8K2.u7068 (nat_lit 14961031) (nat_lit 2377939237) (nat_lit 0) D2M8K2.u7071 from rfl, allE_node, arows7068, irow7072, arows7071]
  all_goals rfl

theorem atot7072 : totK PD2M8K2 D2M8K2.u7072 = [0, 0, 1211163019258, 3527683769685, 2071041404788, 211316415044, 1369150432, 0] := by
  rw [show D2M8K2.u7072 = KTree.node D2M8K2.u7068 (nat_lit 14961031) (nat_lit 2377939237) (nat_lit 0) D2M8K2.u7071 from rfl, totK_node, atot7068, atot7071]
  decide +kernel

theorem arows7079 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7079 = true := by
  rw [show D2M8K2.u7079 = KTree.node D2M8K2.u7075 (nat_lit 15014045) (nat_lit 2261822792) (nat_lit 0) D2M8K2.u7078 from rfl, allE_node, arows7075, irow7079, arows7078]
  all_goals rfl

theorem atot7079 : totK PD2M8K2 D2M8K2.u7079 = [0, 768819602542, 2743501781197, 2880968061971, 798002392046, 32313355136, 0, 0] := by
  rw [show D2M8K2.u7079 = KTree.node D2M8K2.u7075 (nat_lit 15014045) (nat_lit 2261822792) (nat_lit 0) D2M8K2.u7078 from rfl, totK_node, atot7075, atot7078]
  decide +kernel

theorem arows7087 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7087 = true := by
  rw [show D2M8K2.u7087 = KTree.node D2M8K2.u7083 (nat_lit 15021234) (nat_lit 3011520124) (nat_lit 0) D2M8K2.u7086 from rfl, allE_node, arows7083, irow7087, arows7086]
  all_goals rfl

theorem atot7087 : totK PD2M8K2 D2M8K2.u7087 = [0, 759749299953, 2782843989030, 2888235599724, 795555012116, 37733363856, 0, 0] := by
  rw [show D2M8K2.u7087 = KTree.node D2M8K2.u7083 (nat_lit 15021234) (nat_lit 3011520124) (nat_lit 0) D2M8K2.u7086 from rfl, totK_node, atot7083, atot7086]
  decide +kernel

theorem arows7094 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7094 = true := by
  rw [show D2M8K2.u7094 = KTree.node D2M8K2.u7090 (nat_lit 15031614) (nat_lit 3672556653) (nat_lit 0) D2M8K2.u7093 from rfl, allE_node, arows7090, irow7094, arows7093]
  all_goals rfl

theorem atot7094 : totK PD2M8K2 D2M8K2.u7094 = [0, 505890490803, 2486529835713, 3237650776223, 905322560979, 33553796073, 0, 0] := by
  rw [show D2M8K2.u7094 = KTree.node D2M8K2.u7090 (nat_lit 15031614) (nat_lit 3672556653) (nat_lit 0) D2M8K2.u7093 from rfl, totK_node, atot7090, atot7093]
  decide +kernel

theorem arows7104 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7104 = true := by
  rw [show D2M8K2.u7104 = KTree.node D2M8K2.u7100 (nat_lit 15040611) (nat_lit 2729606848) (nat_lit 0) D2M8K2.u7103 from rfl, allE_node, arows7100, irow7104, arows7103]
  all_goals rfl

theorem atot7104 : totK PD2M8K2 D2M8K2.u7104 = [0, 0, 871465630319, 3144945006584, 2643309010216, 448157966274, 14222663156, 0] := by
  rw [show D2M8K2.u7104 = KTree.node D2M8K2.u7100 (nat_lit 15040611) (nat_lit 2729606848) (nat_lit 0) D2M8K2.u7103 from rfl, totK_node, atot7100, atot7103]
  decide +kernel

theorem arows7111 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7111 = true := by
  rw [show D2M8K2.u7111 = KTree.node D2M8K2.u7107 (nat_lit 15051098) (nat_lit 2549160392) (nat_lit 0) D2M8K2.u7110 from rfl, allE_node, arows7107, irow7111, arows7110]
  all_goals rfl

theorem atot7111 : totK PD2M8K2 D2M8K2.u7111 = [0, 420970288622, 1827199169845, 2929986613463, 1700173987793, 211426457022, 4574395652, 0] := by
  rw [show D2M8K2.u7111 = KTree.node D2M8K2.u7107 (nat_lit 15051098) (nat_lit 2549160392) (nat_lit 0) D2M8K2.u7110 from rfl, totK_node, atot7107, atot7110]
  decide +kernel

theorem arows7119 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7119 = true := by
  rw [show D2M8K2.u7119 = KTree.node D2M8K2.u7115 (nat_lit 15066448) (nat_lit 3001474136) (nat_lit 0) D2M8K2.u7118 from rfl, allE_node, arows7115, irow7119, arows7118]
  all_goals rfl

theorem atot7119 : totK PD2M8K2 D2M8K2.u7119 = [0, 823857601559, 3015198837441, 2809879204632, 524578238620, 14619835693, 0, 0] := by
  rw [show D2M8K2.u7119 = KTree.node D2M8K2.u7115 (nat_lit 15066448) (nat_lit 3001474136) (nat_lit 0) D2M8K2.u7118 from rfl, totK_node, atot7115, atot7118]
  decide +kernel

theorem arows7126 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7126 = true := by
  rw [show D2M8K2.u7126 = KTree.node D2M8K2.u7122 (nat_lit 15073486) (nat_lit 3995422534) (nat_lit 0) D2M8K2.u7125 from rfl, allE_node, arows7122, irow7126, arows7125]
  all_goals rfl

theorem atot7126 : totK PD2M8K2 D2M8K2.u7126 = [0, 403614254217, 2244526962469, 3352895396300, 1095391858298, 52773747946, 0, 0] := by
  rw [show D2M8K2.u7126 = KTree.node D2M8K2.u7122 (nat_lit 15073486) (nat_lit 3995422534) (nat_lit 0) D2M8K2.u7125 from rfl, totK_node, atot7122, atot7125]
  decide +kernel

theorem arows7135 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7135 = true := by
  rw [show D2M8K2.u7135 = KTree.node D2M8K2.u7131 (nat_lit 15089400) (nat_lit 2686065782) (nat_lit 0) D2M8K2.u7134 from rfl, allE_node, arows7131, irow7135, arows7134]
  all_goals rfl

theorem atot7135 : totK PD2M8K2 D2M8K2.u7135 = [0, 90861460542, 1438164155858, 3504138648224, 1927398939994, 161443284712, 1239866073, 0] := by
  rw [show D2M8K2.u7135 = KTree.node D2M8K2.u7131 (nat_lit 15089400) (nat_lit 2686065782) (nat_lit 0) D2M8K2.u7134 from rfl, totK_node, atot7131, atot7134]
  decide +kernel

theorem arows7142 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7142 = true := by
  rw [show D2M8K2.u7142 = KTree.node D2M8K2.u7138 (nat_lit 15099957) (nat_lit 1731186217) (nat_lit 0) D2M8K2.u7141 from rfl, allE_node, arows7138, irow7142, arows7141]
  all_goals rfl

theorem atot7142 : totK PD2M8K2 D2M8K2.u7142 = [0, 914600694340, 3022278299686, 2694897805417, 586132615426, 17832019167, 0, 0] := by
  rw [show D2M8K2.u7142 = KTree.node D2M8K2.u7138 (nat_lit 15099957) (nat_lit 1731186217) (nat_lit 0) D2M8K2.u7141 from rfl, totK_node, atot7138, atot7141]
  decide +kernel

theorem arows7150 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7150 = true := by
  rw [show D2M8K2.u7150 = KTree.node D2M8K2.u7146 (nat_lit 15107214) (nat_lit 3953930835) (nat_lit 0) D2M8K2.u7149 from rfl, allE_node, arows7146, irow7150, arows7149]
  all_goals rfl

theorem atot7150 : totK PD2M8K2 D2M8K2.u7150 = [0, 794581950208, 2868694809622, 2823144062535, 636919688807, 26300412495, 0, 0] := by
  rw [show D2M8K2.u7150 = KTree.node D2M8K2.u7146 (nat_lit 15107214) (nat_lit 3953930835) (nat_lit 0) D2M8K2.u7149 from rfl, totK_node, atot7146, atot7149]
  decide +kernel

theorem arows7157 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7157 = true := by
  rw [show D2M8K2.u7157 = KTree.node D2M8K2.u7153 (nat_lit 15117661) (nat_lit 1023534013) (nat_lit 0) D2M8K2.u7156 from rfl, allE_node, arows7153, irow7157, arows7156]
  all_goals rfl

theorem atot7157 : totK PD2M8K2 D2M8K2.u7157 = [0, 177806637211, 1714163854005, 3452231312830, 1614231019485, 138853676653, 1138244013, 0] := by
  rw [show D2M8K2.u7157 = KTree.node D2M8K2.u7153 (nat_lit 15117661) (nat_lit 1023534013) (nat_lit 0) D2M8K2.u7156 from rfl, totK_node, atot7153, atot7156]
  decide +kernel

theorem arows7171 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7171 = true := by
  rw [show D2M8K2.u7171 = KTree.node D2M8K2.u7167 (nat_lit 15128622) (nat_lit 3844506042) (nat_lit 0) D2M8K2.u7170 from rfl, allE_node, arows7167, irow7171, arows7170]
  all_goals rfl

theorem atot7171 : totK PD2M8K2 D2M8K2.u7171 = [0, 55323524080, 1233583692321, 3437693036960, 2095500527026, 245462347453, 4977114383, 0] := by
  rw [show D2M8K2.u7171 = KTree.node D2M8K2.u7167 (nat_lit 15128622) (nat_lit 3844506042) (nat_lit 0) D2M8K2.u7170 from rfl, totK_node, atot7167, atot7170]
  decide +kernel

theorem arows7178 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7178 = true := by
  rw [show D2M8K2.u7178 = KTree.node D2M8K2.u7174 (nat_lit 15141252) (nat_lit 951288606) (nat_lit 0) D2M8K2.u7177 from rfl, allE_node, arows7174, irow7178, arows7177]
  all_goals rfl

theorem atot7178 : totK PD2M8K2 D2M8K2.u7178 = [0, 863159992843, 2979604152116, 2737834803041, 658320756517, 32396575332, 0, 0] := by
  rw [show D2M8K2.u7178 = KTree.node D2M8K2.u7174 (nat_lit 15141252) (nat_lit 951288606) (nat_lit 0) D2M8K2.u7177 from rfl, totK_node, atot7174, atot7177]
  decide +kernel

theorem arows7186 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7186 = true := by
  rw [show D2M8K2.u7186 = KTree.node D2M8K2.u7182 (nat_lit 15148125) (nat_lit 1263493270) (nat_lit 0) D2M8K2.u7185 from rfl, allE_node, arows7182, irow7186, arows7185]
  all_goals rfl

theorem atot7186 : totK PD2M8K2 D2M8K2.u7186 = [0, 838918615600, 2939075254836, 2836477693193, 597351797505, 18499430880, 0, 0] := by
  rw [show D2M8K2.u7186 = KTree.node D2M8K2.u7182 (nat_lit 15148125) (nat_lit 1263493270) (nat_lit 0) D2M8K2.u7185 from rfl, totK_node, atot7182, atot7185]
  decide +kernel

theorem arows7193 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7193 = true := by
  rw [show D2M8K2.u7193 = KTree.node D2M8K2.u7189 (nat_lit 15158618) (nat_lit 3796687905) (nat_lit 0) D2M8K2.u7192 from rfl, allE_node, arows7189, irow7193, arows7192]
  all_goals rfl

theorem atot7193 : totK PD2M8K2 D2M8K2.u7193 = [0, 231594451109, 1665457797608, 3269543903448, 1806017734071, 175551317716, 1310285577, 0] := by
  rw [show D2M8K2.u7193 = KTree.node D2M8K2.u7189 (nat_lit 15158618) (nat_lit 3796687905) (nat_lit 0) D2M8K2.u7192 from rfl, totK_node, atot7189, atot7192]
  decide +kernel

theorem arows7202 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7202 = true := by
  rw [show D2M8K2.u7202 = KTree.node D2M8K2.u7198 (nat_lit 15167340) (nat_lit 2829619261) (nat_lit 0) D2M8K2.u7201 from rfl, allE_node, arows7198, irow7202, arows7201]
  all_goals rfl

theorem atot7202 : totK PD2M8K2 D2M8K2.u7202 = [0, 0, 1211183984715, 3475947695916, 2249650437662, 260442056760, 4879840392, 0] := by
  rw [show D2M8K2.u7202 = KTree.node D2M8K2.u7198 (nat_lit 15167340) (nat_lit 2829619261) (nat_lit 0) D2M8K2.u7201 from rfl, totK_node, atot7198, atot7201]
  decide +kernel

theorem arows7209 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7209 = true := by
  rw [show D2M8K2.u7209 = KTree.node D2M8K2.u7205 (nat_lit 15179736) (nat_lit 3561687974) (nat_lit 0) D2M8K2.u7208 from rfl, allE_node, arows7205, irow7209, arows7208]
  all_goals rfl

theorem atot7209 : totK PD2M8K2 D2M8K2.u7209 = [0, 0, 865345565980, 3104364500257, 2720541958904, 482567953776, 15155644480, 0] := by
  rw [show D2M8K2.u7209 = KTree.node D2M8K2.u7205 (nat_lit 15179736) (nat_lit 3561687974) (nat_lit 0) D2M8K2.u7208 from rfl, totK_node, atot7205, atot7208]
  decide +kernel

theorem arows7217 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7217 = true := by
  rw [show D2M8K2.u7217 = KTree.node D2M8K2.u7213 (nat_lit 15190312) (nat_lit 2325921096) (nat_lit 0) D2M8K2.u7216 from rfl, allE_node, arows7213, irow7217, arows7216]
  all_goals rfl

theorem atot7217 : totK PD2M8K2 D2M8K2.u7217 = [0, 0, 927618858273, 3079651651598, 2590091935403, 419221220737, 14089731401, 0] := by
  rw [show D2M8K2.u7217 = KTree.node D2M8K2.u7213 (nat_lit 15190312) (nat_lit 2325921096) (nat_lit 0) D2M8K2.u7216 from rfl, totK_node, atot7213, atot7216]
  decide +kernel

theorem arows7224 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7224 = true := by
  rw [show D2M8K2.u7224 = KTree.node D2M8K2.u7220 (nat_lit 15197695) (nat_lit 2408648108) (nat_lit 0) D2M8K2.u7223 from rfl, allE_node, arows7220, irow7224, arows7223]
  all_goals rfl

theorem atot7224 : totK PD2M8K2 D2M8K2.u7224 = [0, 0, 453750280337, 2434413918250, 3264266671894, 871390317513, 37159195947, 0] := by
  rw [show D2M8K2.u7224 = KTree.node D2M8K2.u7220 (nat_lit 15197695) (nat_lit 2408648108) (nat_lit 0) D2M8K2.u7223 from rfl, totK_node, atot7220, atot7223]
  decide +kernel

theorem arows7234 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7234 = true := by
  rw [show D2M8K2.u7234 = KTree.node D2M8K2.u7230 (nat_lit 15210811) (nat_lit 2243241104) (nat_lit 0) D2M8K2.u7233 from rfl, allE_node, arows7230, irow7234, arows7233]
  all_goals rfl

theorem atot7234 : totK PD2M8K2 D2M8K2.u7234 = [0, 0, 0, 1554437659054, 3686577703270, 1593988454361, 144700074498, 1369150432] := by
  rw [show D2M8K2.u7234 = KTree.node D2M8K2.u7230 (nat_lit 15210811) (nat_lit 2243241104) (nat_lit 0) D2M8K2.u7233 from rfl, totK_node, atot7230, atot7233]
  decide +kernel

theorem arows7241 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7241 = true := by
  rw [show D2M8K2.u7241 = KTree.node D2M8K2.u7237 (nat_lit 15264949) (nat_lit 1167152361) (nat_lit 0) D2M8K2.u7240 from rfl, allE_node, arows7237, irow7241, arows7240]
  all_goals rfl

theorem atot7241 : totK PD2M8K2 D2M8K2.u7241 = [0, 0, 933377859072, 3124673262329, 2666447859511, 478095267202, 15585527994, 0] := by
  rw [show D2M8K2.u7241 = KTree.node D2M8K2.u7237 (nat_lit 15264949) (nat_lit 1167152361) (nat_lit 0) D2M8K2.u7240 from rfl, totK_node, atot7237, atot7240]
  decide +kernel

theorem arows7249 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7249 = true := by
  rw [show D2M8K2.u7249 = KTree.node D2M8K2.u7245 (nat_lit 15275853) (nat_lit 1496740031) (nat_lit 0) D2M8K2.u7248 from rfl, allE_node, arows7245, irow7249, arows7248]
  all_goals rfl

theorem atot7249 : totK PD2M8K2 D2M8K2.u7249 = [0, 0, 839824687620, 2978797349287, 2790351162282, 522546099101, 17966996581, 0] := by
  rw [show D2M8K2.u7249 = KTree.node D2M8K2.u7245 (nat_lit 15275853) (nat_lit 1496740031) (nat_lit 0) D2M8K2.u7248 from rfl, totK_node, atot7245, atot7248]
  decide +kernel

theorem arows7256 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7256 = true := by
  rw [show D2M8K2.u7256 = KTree.node D2M8K2.u7252 (nat_lit 15304011) (nat_lit 1840378332) (nat_lit 136) D2M8K2.u7255 from rfl, allE_node, arows7252, irow7256, arows7255]
  all_goals rfl

theorem atot7256 : totK PD2M8K2 D2M8K2.u7256 = [0, 0, 916476100105, 3110308557644, 2682316944665, 450952349863, 15053452749, 0] := by
  rw [show D2M8K2.u7256 = KTree.node D2M8K2.u7252 (nat_lit 15304011) (nat_lit 1840378332) (nat_lit 136) D2M8K2.u7255 from rfl, totK_node, atot7252, atot7255]
  decide +kernel

theorem arows7265 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7265 = true := by
  rw [show D2M8K2.u7265 = KTree.node D2M8K2.u7261 (nat_lit 15319406) (nat_lit 3381939697) (nat_lit 0) D2M8K2.u7264 from rfl, allE_node, arows7261, irow7265, arows7264]
  all_goals rfl

theorem atot7265 : totK PD2M8K2 D2M8K2.u7265 = [0, 0, 1260234540478, 3544844307353, 2157463909694, 188087220626, 1096505104, 0] := by
  rw [show D2M8K2.u7265 = KTree.node D2M8K2.u7261 (nat_lit 15319406) (nat_lit 3381939697) (nat_lit 0) D2M8K2.u7264 from rfl, totK_node, atot7261, atot7264]
  decide +kernel

theorem arows7272 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7272 = true := by
  rw [show D2M8K2.u7272 = KTree.node D2M8K2.u7268 (nat_lit 15350153) (nat_lit 1794605220) (nat_lit 0) D2M8K2.u7271 from rfl, allE_node, arows7268, irow7272, arows7271]
  all_goals rfl

theorem atot7272 : totK PD2M8K2 D2M8K2.u7272 = [0, 0, 863009075615, 3176828882162, 2746161597157, 378734778938, 3943030865, 0] := by
  rw [show D2M8K2.u7272 = KTree.node D2M8K2.u7268 (nat_lit 15350153) (nat_lit 1794605220) (nat_lit 0) D2M8K2.u7271 from rfl, totK_node, atot7268, atot7271]
  decide +kernel

theorem arows7280 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7280 = true := by
  rw [show D2M8K2.u7280 = KTree.node D2M8K2.u7276 (nat_lit 15358248) (nat_lit 3471409198) (nat_lit 0) D2M8K2.u7279 from rfl, allE_node, arows7276, irow7280, arows7279]
  all_goals rfl

theorem atot7280 : totK PD2M8K2 D2M8K2.u7280 = [0, 0, 811654378316, 3022722318906, 2797855080023, 473874547160, 15183121520, 0] := by
  rw [show D2M8K2.u7280 = KTree.node D2M8K2.u7276 (nat_lit 15358248) (nat_lit 3471409198) (nat_lit 0) D2M8K2.u7279 from rfl, totK_node, atot7276, atot7279]
  decide +kernel

theorem arows7287 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7287 = true := by
  rw [show D2M8K2.u7287 = KTree.node D2M8K2.u7283 (nat_lit 15390038) (nat_lit 4150964372) (nat_lit 0) D2M8K2.u7286 from rfl, allE_node, arows7283, irow7287, arows7286]
  all_goals rfl

theorem atot7287 : totK PD2M8K2 D2M8K2.u7287 = [0, 0, 1161738163096, 3443281456324, 2352256073861, 265804331224, 4183747439, 0] := by
  rw [show D2M8K2.u7287 = KTree.node D2M8K2.u7283 (nat_lit 15390038) (nat_lit 4150964372) (nat_lit 0) D2M8K2.u7286 from rfl, totK_node, atot7283, atot7286]
  decide +kernel

end QECKChecks.D2M8K2
