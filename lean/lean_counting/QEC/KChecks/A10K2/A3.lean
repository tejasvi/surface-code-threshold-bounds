import QEC.Count.ChunksK3
import QEC.KChecks.A10K2.A2

namespace QECKChecks.A10K2

open QEC QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem arows3596 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3596 = true := by
  rw [show A10K2.u3596 = KTree.node A10K2.t3600 (nat_lit 59146597) (nat_lit 7209061384) (nat_lit 0) A10K2.t3601 from rfl, allE_node, rows3600, irow3596, rows3601]
  all_goals rfl

theorem atot3596 : totK PA10K2 A10K2.u3596 = [0, 0, 0, 1141401734693, 3902535515263, 3417661234734, 725485471173, 38110549964, 0, 0] := by
  rw [show A10K2.u3596 = KTree.node A10K2.t3600 (nat_lit 59146597) (nat_lit 7209061384) (nat_lit 0) A10K2.t3601 from rfl, totK_node, tot3600, tot3601]
  decide +kernel

theorem arows3597 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3597 = true := by
  rw [show A10K2.u3597 = KTree.node A10K2.t3602 (nat_lit 59162721) (nat_lit 9996329722) (nat_lit 0) A10K2.t3603 from rfl, allE_node, rows3602, irow3597, rows3603]
  all_goals rfl

theorem atot3597 : totK PA10K2 A10K2.u3597 = [0, 0, 0, 1304418831292, 4069451769865, 3342403218121, 686851006473, 36877445968, 0, 0] := by
  rw [show A10K2.u3597 = KTree.node A10K2.t3602 (nat_lit 59162721) (nat_lit 9996329722) (nat_lit 0) A10K2.t3603 from rfl, totK_node, tot3602, tot3603]
  decide +kernel

theorem arows3599 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3599 = true := by
  rw [show A10K2.u3599 = KTree.node A10K2.t3604 (nat_lit 59168946) (nat_lit 11065005545) (nat_lit 0) A10K2.t3605 from rfl, allE_node, rows3604, irow3599, rows3605]
  all_goals rfl

theorem atot3599 : totK PA10K2 A10K2.u3599 = [0, 329682097654, 1182155827690, 1399706696585, 1916414867761, 2879159538449, 1385319861529, 192289909650, 5676195732, 0] := by
  rw [show A10K2.u3599 = KTree.node A10K2.t3604 (nat_lit 59168946) (nat_lit 11065005545) (nat_lit 0) A10K2.t3605 from rfl, totK_node, tot3604, tot3605]
  decide +kernel

theorem arows3600 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3600 = true := by
  rw [show A10K2.u3600 = KTree.node A10K2.t3606 (nat_lit 59322266) (nat_lit 14591627111) (nat_lit 0) A10K2.t3607 from rfl, allE_node, rows3606, irow3600, rows3607]
  all_goals rfl

theorem atot3600 : totK PA10K2 A10K2.u3600 = [0, 518434751736, 2554544469325, 3980744002111, 2234123064741, 426054852346, 25734533292, 0, 0, 0] := by
  rw [show A10K2.u3600 = KTree.node A10K2.t3606 (nat_lit 59322266) (nat_lit 14591627111) (nat_lit 0) A10K2.t3607 from rfl, totK_node, tot3606, tot3607]
  decide +kernel

theorem arows3603 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3603 = true := by
  rw [show A10K2.u3603 = KTree.node A10K2.t3608 (nat_lit 59327712) (nat_lit 7525496256) (nat_lit 0) A10K2.t3609 from rfl, allE_node, rows3608, irow3603, rows3609]
  all_goals rfl

theorem atot3603 : totK PA10K2 A10K2.u3603 = [0, 742937934308, 2959821785685, 3727053729765, 1810381212754, 259136547755, 6034215561, 0, 0, 0] := by
  rw [show A10K2.u3603 = KTree.node A10K2.t3608 (nat_lit 59327712) (nat_lit 7525496256) (nat_lit 0) A10K2.t3609 from rfl, totK_node, tot3608, tot3609]
  decide +kernel

theorem arows3604 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3604 = true := by
  rw [show A10K2.u3604 = KTree.node A10K2.t3610 (nat_lit 59333382) (nat_lit 4510351625) (nat_lit 0) A10K2.t3611 from rfl, allE_node, rows3610, irow3604, rows3611]
  all_goals rfl

theorem atot3604 : totK PA10K2 A10K2.u3604 = [0, 577458300780, 2642247422709, 4133696067454, 2151969714859, 301715795511, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u3604 = KTree.node A10K2.t3610 (nat_lit 59333382) (nat_lit 4510351625) (nat_lit 0) A10K2.t3611 from rfl, totK_node, tot3610, tot3611]
  decide +kernel

theorem arows3606 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3606 = true := by
  rw [show A10K2.u3606 = KTree.node A10K2.t3612 (nat_lit 59340450) (nat_lit 14286667535) (nat_lit 0) A10K2.t3613 from rfl, allE_node, rows3612, irow3606, rows3613]
  all_goals rfl

theorem atot3606 : totK PA10K2 A10K2.u3606 = [0, 117664770764, 1580807429979, 4152673134303, 3489925010840, 873860495456, 48360659890, 0, 0, 0] := by
  rw [show A10K2.u3606 = KTree.node A10K2.t3612 (nat_lit 59340450) (nat_lit 14286667535) (nat_lit 0) A10K2.t3613 from rfl, totK_node, tot3612, tot3613]
  decide +kernel

theorem arows3607 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3607 = true := by
  rw [show A10K2.u3607 = KTree.node A10K2.t3614 (nat_lit 59354263) (nat_lit 13993239748) (nat_lit 0) A10K2.t3615 from rfl, allE_node, rows3614, irow3607, rows3615]
  all_goals rfl

theorem atot3607 : totK PA10K2 A10K2.u3607 = [0, 0, 644381207677, 2934542051687, 4066067356251, 1770774592821, 281231595889, 20331139758, 0, 0] := by
  rw [show A10K2.u3607 = KTree.node A10K2.t3614 (nat_lit 59354263) (nat_lit 13993239748) (nat_lit 0) A10K2.t3615 from rfl, totK_node, tot3614, tot3615]
  decide +kernel

theorem arows3612 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3612 = true := by
  rw [show A10K2.u3612 = KTree.node A10K2.t3616 (nat_lit 59359506) (nat_lit 13679744188) (nat_lit 0) A10K2.t3617 from rfl, allE_node, rows3616, irow3612, rows3617]
  all_goals rfl

theorem atot3612 : totK PA10K2 A10K2.u3612 = [0, 0, 634300304452, 2599939221954, 3739137258138, 2074117722800, 355096493773, 10751746851, 0, 0] := by
  rw [show A10K2.u3612 = KTree.node A10K2.t3616 (nat_lit 59359506) (nat_lit 13679744188) (nat_lit 0) A10K2.t3617 from rfl, totK_node, tot3616, tot3617]
  decide +kernel

theorem arows3613 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3613 = true := by
  rw [show A10K2.u3613 = KTree.node A10K2.t3618 (nat_lit 59365559) (nat_lit 5689488052) (nat_lit 0) A10K2.t3619 from rfl, allE_node, rows3618, irow3613, rows3619]
  all_goals rfl

theorem atot3613 : totK PA10K2 A10K2.u3613 = [0, 0, 507182490604, 2663063494259, 4163844444510, 1950642713009, 239732529510, 6121173289, 0, 0] := by
  rw [show A10K2.u3613 = KTree.node A10K2.t3618 (nat_lit 59365559) (nat_lit 5689488052) (nat_lit 0) A10K2.t3619 from rfl, totK_node, tot3618, tot3619]
  decide +kernel

theorem arows3615 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3615 = true := by
  rw [show A10K2.u3615 = KTree.node A10K2.t3620 (nat_lit 59376001) (nat_lit 10422756214) (nat_lit 0) A10K2.t3621 from rfl, allE_node, rows3620, irow3615, rows3621]
  all_goals rfl

theorem atot3615 : totK PA10K2 A10K2.u3615 = [0, 516552094339, 2367046030959, 3629332397855, 2377184107853, 724291850049, 48083517153, 0, 0, 0] := by
  rw [show A10K2.u3615 = KTree.node A10K2.t3620 (nat_lit 59376001) (nat_lit 10422756214) (nat_lit 0) A10K2.t3621 from rfl, totK_node, tot3620, tot3621]
  decide +kernel

theorem arows3616 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3616 = true := by
  rw [show A10K2.u3616 = KTree.node A10K2.t3622 (nat_lit 59385124) (nat_lit 13742643306) (nat_lit 0) A10K2.t3623 from rfl, allE_node, rows3622, irow3616, rows3623]
  all_goals rfl

theorem atot3616 : totK PA10K2 A10K2.u3616 = [0, 640753510724, 2530013046437, 3625195503002, 2169909147780, 450788798926, 30831673886, 0, 0, 0] := by
  rw [show A10K2.u3616 = KTree.node A10K2.t3622 (nat_lit 59385124) (nat_lit 13742643306) (nat_lit 0) A10K2.t3623 from rfl, totK_node, tot3622, tot3623]
  decide +kernel

theorem arows3619 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3619 = true := by
  rw [show A10K2.u3619 = KTree.node A10K2.t3624 (nat_lit 59389880) (nat_lit 7250860596) (nat_lit 0) A10K2.t3625 from rfl, allE_node, rows3624, irow3619, rows3625]
  all_goals rfl

theorem atot3619 : totK PA10K2 A10K2.u3619 = [0, 363062879634, 2027096241341, 3874162687692, 2886607006463, 616063758146, 31768748853, 0, 0, 0] := by
  rw [show A10K2.u3619 = KTree.node A10K2.t3624 (nat_lit 59389880) (nat_lit 7250860596) (nat_lit 0) A10K2.t3625 from rfl, totK_node, tot3624, tot3625]
  decide +kernel

theorem arows3620 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3620 = true := by
  rw [show A10K2.u3620 = KTree.node A10K2.t3626 (nat_lit 59394230) (nat_lit 10071350081) (nat_lit 0) A10K2.t3627 from rfl, allE_node, rows3626, irow3620, rows3627]
  all_goals rfl

theorem atot3620 : totK PA10K2 A10K2.u3620 = [0, 583209941258, 2903344699417, 4165748331032, 1655704381453, 126324832095, 0, 0, 0, 0] := by
  rw [show A10K2.u3620 = KTree.node A10K2.t3626 (nat_lit 59394230) (nat_lit 10071350081) (nat_lit 0) A10K2.t3627 from rfl, totK_node, tot3626, tot3627]
  decide +kernel

theorem arows3622 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3622 = true := by
  rw [show A10K2.u3622 = KTree.node A10K2.t3628 (nat_lit 59409223) (nat_lit 5500784964) (nat_lit 0) A10K2.t3629 from rfl, allE_node, rows3628, irow3622, rows3629]
  all_goals rfl

theorem atot3622 : totK PA10K2 A10K2.u3622 = [0, 0, 1084801481527, 3823507565904, 3591080413211, 832987709613, 38342359577, 0, 0, 0] := by
  rw [show A10K2.u3622 = KTree.node A10K2.t3628 (nat_lit 59409223) (nat_lit 5500784964) (nat_lit 0) A10K2.t3629 from rfl, totK_node, tot3628, tot3629]
  decide +kernel

theorem arows3623 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3623 = true := by
  rw [show A10K2.u3623 = KTree.node A10K2.t3630 (nat_lit 59420345) (nat_lit 2364238602) (nat_lit 0) A10K2.t3631 from rfl, allE_node, rows3630, irow3623, rows3631]
  all_goals rfl

theorem atot3623 : totK PA10K2 A10K2.u3623 = [0, 0, 987663185609, 3615046751775, 3837957295428, 1046062687731, 64078106957, 0, 0, 0] := by
  rw [show A10K2.u3623 = KTree.node A10K2.t3630 (nat_lit 59420345) (nat_lit 2364238602) (nat_lit 0) A10K2.t3631 from rfl, totK_node, tot3630, tot3631]
  decide +kernel

theorem arows3627 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3627 = true := by
  rw [show A10K2.u3627 = KTree.node A10K2.t3632 (nat_lit 59430038) (nat_lit 13320598012) (nat_lit 0) A10K2.t3633 from rfl, allE_node, rows3632, irow3627, rows3633]
  all_goals rfl

theorem atot3627 : totK PA10K2 A10K2.u3627 = [0, 202041260899, 823788501426, 2320986840748, 3744983946015, 1890064517082, 282524277315, 6354482628, 0, 0] := by
  rw [show A10K2.u3627 = KTree.node A10K2.t3632 (nat_lit 59430038) (nat_lit 13320598012) (nat_lit 0) A10K2.t3633 from rfl, totK_node, tot3632, tot3633]
  decide +kernel

theorem arows3628 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3628 = true := by
  rw [show A10K2.u3628 = KTree.node A10K2.t3634 (nat_lit 59452819) (nat_lit 10460993823) (nat_lit 0) A10K2.t3635 from rfl, allE_node, rows3634, irow3628, rows3635]
  all_goals rfl

theorem atot3628 : totK PA10K2 A10K2.u3628 = [0, 609207037005, 2753039335601, 4108732154796, 2158099803969, 405799458312, 25715051306, 0, 0, 0] := by
  rw [show A10K2.u3628 = KTree.node A10K2.t3634 (nat_lit 59452819) (nat_lit 10460993823) (nat_lit 0) A10K2.t3635 from rfl, totK_node, tot3634, tot3635]
  decide +kernel

theorem arows3630 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3630 = true := by
  rw [show A10K2.u3630 = KTree.node A10K2.t3636 (nat_lit 59466625) (nat_lit 10296676959) (nat_lit 0) A10K2.t3637 from rfl, allE_node, rows3636, irow3630, rows3637]
  all_goals rfl

theorem atot3630 : totK PA10K2 A10K2.u3630 = [0, 798450316783, 3159880700163, 4097771453534, 1933161358572, 266873039309, 6032141194, 0, 0, 0] := by
  rw [show A10K2.u3630 = KTree.node A10K2.t3636 (nat_lit 59466625) (nat_lit 10296676959) (nat_lit 0) A10K2.t3637 from rfl, totK_node, tot3636, tot3637]
  decide +kernel

theorem arows3631 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3631 = true := by
  rw [show A10K2.u3631 = KTree.node A10K2.t3638 (nat_lit 59471574) (nat_lit 13661861614) (nat_lit 0) A10K2.t3639 from rfl, allE_node, rows3638, irow3631, rows3639]
  all_goals rfl

theorem atot3631 : totK PA10K2 A10K2.u3631 = [0, 0, 1302853760343, 4255227437192, 3774582980429, 888437584919, 42874818239, 0, 0, 0] := by
  rw [show A10K2.u3631 = KTree.node A10K2.t3638 (nat_lit 59471574) (nat_lit 13661861614) (nat_lit 0) A10K2.t3639 from rfl, totK_node, tot3638, tot3639]
  decide +kernel

theorem arows3634 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3634 = true := by
  rw [show A10K2.u3634 = KTree.node A10K2.t3640 (nat_lit 59485618) (nat_lit 14586405808) (nat_lit 0) A10K2.t3641 from rfl, allE_node, rows3640, irow3634, rows3641]
  all_goals rfl

theorem atot3634 : totK PA10K2 A10K2.u3634 = [0, 0, 583357225147, 2819056743768, 4217269316854, 2134629571958, 295452889618, 7047025452, 0, 0] := by
  rw [show A10K2.u3634 = KTree.node A10K2.t3640 (nat_lit 59485618) (nat_lit 14586405808) (nat_lit 0) A10K2.t3641 from rfl, totK_node, tot3640, tot3641]
  decide +kernel

theorem arows3635 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3635 = true := by
  rw [show A10K2.u3635 = KTree.node A10K2.t3642 (nat_lit 59499963) (nat_lit 7035925206) (nat_lit 0) A10K2.t3643 from rfl, allE_node, rows3642, irow3635, rows3643]
  all_goals rfl

theorem atot3635 : totK PA10K2 A10K2.u3635 = [0, 0, 797739579589, 3328779565947, 4302534388867, 1688428403855, 125324390452, 0, 0, 0] := by
  rw [show A10K2.u3635 = KTree.node A10K2.t3642 (nat_lit 59499963) (nat_lit 7035925206) (nat_lit 0) A10K2.t3643 from rfl, totK_node, tot3642, tot3643]
  decide +kernel

theorem arows3637 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3637 = true := by
  rw [show A10K2.u3637 = KTree.node A10K2.t3644 (nat_lit 59506061) (nat_lit 2657610236) (nat_lit 0) A10K2.t3645 from rfl, allE_node, rows3644, irow3637, rows3645]
  all_goals rfl

theorem atot3637 : totK PA10K2 A10K2.u3637 = [0, 0, 319639362920, 1837947771306, 3913945711578, 3189273974112, 777449948644, 41921244464, 0, 0] := by
  rw [show A10K2.u3637 = KTree.node A10K2.t3644 (nat_lit 59506061) (nat_lit 2657610236) (nat_lit 0) A10K2.t3645 from rfl, totK_node, tot3644, tot3645]
  decide +kernel

theorem arows3638 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3638 = true := by
  rw [show A10K2.u3638 = KTree.node A10K2.t3646 (nat_lit 59584214) (nat_lit 15136587392) (nat_lit 0) A10K2.t3647 from rfl, allE_node, rows3646, irow3638, rows3647]
  all_goals rfl

theorem atot3638 : totK PA10K2 A10K2.u3638 = [0, 0, 538071541683, 2594130032822, 3948233267829, 2178471337799, 428929141814, 25734533292, 0, 0] := by
  rw [show A10K2.u3638 = KTree.node A10K2.t3646 (nat_lit 59584214) (nat_lit 15136587392) (nat_lit 0) A10K2.t3647 from rfl, totK_node, tot3646, tot3647]
  decide +kernel

theorem arows3644 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3644 = true := by
  rw [show A10K2.u3644 = KTree.node A10K2.t3648 (nat_lit 59589851) (nat_lit 9771628988) (nat_lit 0) A10K2.t3649 from rfl, allE_node, rows3648, irow3644, rows3649]
  all_goals rfl

theorem atot3644 : totK PA10K2 A10K2.u3644 = [0, 0, 742273277851, 2974379173262, 3786469547444, 1725925369821, 235333911869, 6034215561, 0, 0] := by
  rw [show A10K2.u3644 = KTree.node A10K2.t3648 (nat_lit 59589851) (nat_lit 9771628988) (nat_lit 0) A10K2.t3649 from rfl, totK_node, tot3648, tot3649]
  decide +kernel

theorem arows3645 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3645 = true := by
  rw [show A10K2.u3645 = KTree.node A10K2.t3650 (nat_lit 59595540) (nat_lit 13252706185) (nat_lit 0) A10K2.t3651 from rfl, allE_node, rows3650, irow3645, rows3651]
  all_goals rfl

theorem atot3645 : totK PA10K2 A10K2.u3645 = [0, 0, 576535847275, 2672322306271, 4174693209961, 2058979480703, 246821382421, 6239673734, 0, 0] := by
  rw [show A10K2.u3645 = KTree.node A10K2.t3650 (nat_lit 59595540) (nat_lit 13252706185) (nat_lit 0) A10K2.t3651 from rfl, totK_node, tot3650, tot3651]
  decide +kernel

theorem arows3647 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3647 = true := by
  rw [show A10K2.u3647 = KTree.node A10K2.t3652 (nat_lit 59602616) (nat_lit 9425261818) (nat_lit 0) A10K2.t3653 from rfl, allE_node, rows3652, irow3647, rows3653]
  all_goals rfl

theorem atot3647 : totK PA10K2 A10K2.u3647 = [0, 0, 117664770764, 1659942380668, 4314257145820, 3378606162240, 714981079744, 36427600291, 0, 0] := by
  rw [show A10K2.u3647 = KTree.node A10K2.t3652 (nat_lit 59602616) (nat_lit 9425261818) (nat_lit 0) A10K2.t3653 from rfl, totK_node, tot3652, tot3653]
  decide +kernel

theorem arows3648 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3648 = true := by
  rw [show A10K2.u3648 = KTree.node A10K2.t3654 (nat_lit 59616502) (nat_lit 16319387176) (nat_lit 0) A10K2.t3655 from rfl, allE_node, rows3654, irow3648, rows3655]
  all_goals rfl

theorem atot3648 : totK PA10K2 A10K2.u3648 = [0, 0, 0, 535466203172, 2649856939012, 3957659186844, 1983303912122, 388026534923, 25565504801, 0] := by
  rw [show A10K2.u3648 = KTree.node A10K2.t3654 (nat_lit 59616502) (nat_lit 16319387176) (nat_lit 0) A10K2.t3655 from rfl, totK_node, tot3654, tot3655]
  decide +kernel

theorem arows3651 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3651 = true := by
  rw [show A10K2.u3651 = KTree.node A10K2.t3656 (nat_lit 59622177) (nat_lit 9304849763) (nat_lit 0) A10K2.t3657 from rfl, allE_node, rows3656, irow3651, rows3657]
  all_goals rfl

theorem atot3651 : totK PA10K2 A10K2.u3651 = [0, 0, 0, 737191083864, 2951662263670, 3699907907989, 1623241848007, 231509521680, 5453062850, 0] := by
  rw [show A10K2.u3651 = KTree.node A10K2.t3656 (nat_lit 59622177) (nat_lit 9304849763) (nat_lit 0) A10K2.t3657 from rfl, totK_node, tot3656, tot3657]
  decide +kernel

theorem arows3652 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3652 = true := by
  rw [show A10K2.u3652 = KTree.node A10K2.t3658 (nat_lit 59628183) (nat_lit 8353787410) (nat_lit 0) A10K2.t3659 from rfl, allE_node, rows3658, irow3652, rows3659]
  all_goals rfl

theorem atot3652 : totK PA10K2 A10K2.u3652 = [0, 0, 0, 630339857083, 2866305100328, 4082346714724, 1775885984082, 220211641996, 5685526223, 0] := by
  rw [show A10K2.u3652 = KTree.node A10K2.t3658 (nat_lit 59628183) (nat_lit 8353787410) (nat_lit 0) A10K2.t3659 from rfl, totK_node, tot3658, tot3659]
  decide +kernel

theorem arows3654 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3654 = true := by
  rw [show A10K2.u3654 = KTree.node A10K2.t3660 (nat_lit 59639964) (nat_lit 11880596856) (nat_lit 0) A10K2.t3661 from rfl, allE_node, rows3660, irow3654, rows3661]
  all_goals rfl

theorem atot3654 : totK PA10K2 A10K2.u3654 = [0, 0, 516552094339, 2430506688388, 3855610533004, 2119638360889, 452780957075, 30176414022, 0, 0] := by
  rw [show A10K2.u3654 = KTree.node A10K2.t3660 (nat_lit 59639964) (nat_lit 11880596856) (nat_lit 0) A10K2.t3661 from rfl, totK_node, tot3660, tot3661]
  decide +kernel

theorem arows3655 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3655 = true := by
  rw [show A10K2.u3655 = KTree.node A10K2.t3662 (nat_lit 59648269) (nat_lit 5926268763) (nat_lit 0) A10K2.t3663 from rfl, allE_node, rows3662, irow3655, rows3663]
  all_goals rfl

theorem atot3655 : totK PA10K2 A10K2.u3655 = [0, 0, 789671577276, 3177661467604, 3976362138711, 1662485320061, 197629842232, 5460492893, 0, 0] := by
  rw [show A10K2.u3655 = KTree.node A10K2.t3662 (nat_lit 59648269) (nat_lit 5926268763) (nat_lit 0) A10K2.t3663 from rfl, totK_node, tot3662, tot3663]
  decide +kernel

theorem arows3659 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3659 = true := by
  rw [show A10K2.u3659 = KTree.node A10K2.t3664 (nat_lit 59653553) (nat_lit 5780247974) (nat_lit 0) A10K2.t3665 from rfl, allE_node, rows3664, irow3659, rows3665]
  all_goals rfl

theorem atot3659 : totK PA10K2 A10K2.u3659 = [0, 0, 505996508307, 2168210587037, 3600055355336, 2582514361591, 578544309202, 31768748853, 0, 0] := by
  rw [show A10K2.u3659 = KTree.node A10K2.t3664 (nat_lit 59653553) (nat_lit 5780247974) (nat_lit 0) A10K2.t3665 from rfl, totK_node, tot3664, tot3665]
  decide +kernel

theorem arows3660 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3660 = true := by
  rw [show A10K2.u3660 = KTree.node A10K2.t3666 (nat_lit 59659412) (nat_lit 12505876131) (nat_lit 0) A10K2.t3667 from rfl, allE_node, rows3666, irow3660, rows3667]
  all_goals rfl

theorem atot3660 : totK PA10K2 A10K2.u3660 = [0, 0, 304062355366, 2218212544500, 4200030556555, 2269440451053, 306575559770, 6354482628, 0, 0] := by
  rw [show A10K2.u3660 = KTree.node A10K2.t3666 (nat_lit 59659412) (nat_lit 12505876131) (nat_lit 0) A10K2.t3667 from rfl, totK_node, tot3666, tot3667]
  decide +kernel

theorem arows3662 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3662 = true := by
  rw [show A10K2.u3662 = KTree.node A10K2.t3668 (nat_lit 59680069) (nat_lit 6714878553) (nat_lit 0) A10K2.t3669 from rfl, allE_node, rows3668, irow3662, rows3669]
  all_goals rfl

theorem atot3662 : totK PA10K2 A10K2.u3662 = [0, 0, 0, 1060075386397, 3788704338001, 3660956663077, 846865349955, 43864921862, 0, 0] := by
  rw [show A10K2.u3662 = KTree.node A10K2.t3668 (nat_lit 59680069) (nat_lit 6714878553) (nat_lit 0) A10K2.t3669 from rfl, totK_node, tot3668, tot3669]
  decide +kernel

theorem arows3663 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3663 = true := by
  rw [show A10K2.u3663 = KTree.node A10K2.t3670 (nat_lit 59688343) (nat_lit 11977732833) (nat_lit 0) A10K2.t3671 from rfl, allE_node, rows3670, irow3663, rows3671]
  all_goals rfl

theorem atot3663 : totK PA10K2 A10K2.u3663 = [0, 0, 0, 901568387610, 3622096867175, 3871410745108, 941099941125, 49581884977, 0, 0] := by
  rw [show A10K2.u3663 = KTree.node A10K2.t3670 (nat_lit 59688343) (nat_lit 11977732833) (nat_lit 0) A10K2.t3671 from rfl, totK_node, tot3670, tot3671]
  decide +kernel

theorem arows3666 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3666 = true := by
  rw [show A10K2.u3666 = KTree.node A10K2.t3672 (nat_lit 59712740) (nat_lit 12660168957) (nat_lit 0) A10K2.t3673 from rfl, allE_node, rows3672, irow3666, rows3673]
  all_goals rfl

theorem atot3666 : totK PA10K2 A10K2.u3666 = [0, 0, 659356540618, 2174995670828, 2730610612863, 2473645561797, 1266047901158, 202894274768, 6239673734, 0] := by
  rw [show A10K2.u3666 = KTree.node A10K2.t3672 (nat_lit 59712740) (nat_lit 12660168957) (nat_lit 0) A10K2.t3673 from rfl, totK_node, tot3672, tot3673]
  decide +kernel

theorem arows3667 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3667 = true := by
  rw [show A10K2.u3667 = KTree.node A10K2.t3674 (nat_lit 59717399) (nat_lit 9339251002) (nat_lit 0) A10K2.t3675 from rfl, allE_node, rows3674, irow3667, rows3675]
  all_goals rfl

theorem atot3667 : totK PA10K2 A10K2.u3667 = [0, 0, 326175957100, 2112652551916, 4129929862348, 2916536586384, 596013410500, 31285368086, 0, 0] := by
  rw [show A10K2.u3667 = KTree.node A10K2.t3674 (nat_lit 59717399) (nat_lit 9339251002) (nat_lit 0) A10K2.t3675 from rfl, totK_node, tot3674, tot3675]
  decide +kernel

theorem arows3669 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3669 = true := by
  rw [show A10K2.u3669 = KTree.node A10K2.t3676 (nat_lit 59731393) (nat_lit 9956298540) (nat_lit 0) A10K2.t3677 from rfl, allE_node, rows3676, irow3669, rows3677]
  all_goals rfl

theorem atot3669 : totK PA10K2 A10K2.u3669 = [0, 0, 605061847711, 2896093828335, 4468885181139, 2163996945508, 210575050091, 0, 0, 0] := by
  rw [show A10K2.u3669 = KTree.node A10K2.t3676 (nat_lit 59731393) (nat_lit 9956298540) (nat_lit 0) A10K2.t3677 from rfl, totK_node, tot3676, tot3677]
  decide +kernel

theorem arows3670 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3670 = true := by
  rw [show A10K2.u3670 = KTree.node A10K2.t3678 (nat_lit 59769097) (nat_lit 9792185400) (nat_lit 0) A10K2.t3679 from rfl, allE_node, rows3678, irow3670, rows3679]
  all_goals rfl

theorem atot3670 : totK PA10K2 A10K2.u3670 = [0, 573258531646, 2085875459077, 2474964889465, 1988494321288, 1921417101638, 671356004017, 42874818239, 0, 0] := by
  rw [show A10K2.u3670 = KTree.node A10K2.t3678 (nat_lit 59769097) (nat_lit 9792185400) (nat_lit 0) A10K2.t3679 from rfl, totK_node, tot3678, tot3679]
  decide +kernel

theorem arows3675 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3675 = true := by
  rw [show A10K2.u3675 = KTree.node A10K2.t3680 (nat_lit 59773872) (nat_lit 14652486819) (nat_lit 0) A10K2.t3681 from rfl, allE_node, rows3680, irow3675, rows3681]
  all_goals rfl

theorem atot3675 : totK PA10K2 A10K2.u3675 = [0, 466327680920, 2156157010310, 3739838492256, 2672038451166, 573508024427, 30831673886, 0, 0, 0] := by
  rw [show A10K2.u3675 = KTree.node A10K2.t3680 (nat_lit 59773872) (nat_lit 14652486819) (nat_lit 0) A10K2.t3681 from rfl, totK_node, tot3680, tot3681]
  decide +kernel

theorem arows3676 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3676 = true := by
  rw [show A10K2.u3676 = KTree.node A10K2.t3682 (nat_lit 59787553) (nat_lit 9700014513) (nat_lit 0) A10K2.t3683 from rfl, allE_node, rows3682, irow3676, rows3683]
  all_goals rfl

theorem atot3676 : totK PA10K2 A10K2.u3676 = [0, 501369278675, 2789626818778, 4324984324027, 1783598962135, 147759654866, 0, 0, 0, 0] := by
  rw [show A10K2.u3676 = KTree.node A10K2.t3682 (nat_lit 59787553) (nat_lit 9700014513) (nat_lit 0) A10K2.t3683 from rfl, totK_node, tot3682, tot3683]
  decide +kernel

theorem arows3678 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3678 = true := by
  rw [show A10K2.u3678 = KTree.node A10K2.t3684 (nat_lit 59797605) (nat_lit 6187776518) (nat_lit 0) A10K2.t3685 from rfl, allE_node, rows3684, irow3678, rows3685]
  all_goals rfl

theorem atot3678 : totK PA10K2 A10K2.u3678 = [0, 266424507814, 1648508419890, 3711286330735, 3115074724413, 753362509430, 38874906472, 0, 0, 0] := by
  rw [show A10K2.u3678 = KTree.node A10K2.t3684 (nat_lit 59797605) (nat_lit 6187776518) (nat_lit 0) A10K2.t3685 from rfl, totK_node, tot3684, tot3685]
  decide +kernel

theorem arows3679 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3679 = true := by
  rw [show A10K2.u3679 = KTree.node A10K2.t3686 (nat_lit 59805953) (nat_lit 10404522250) (nat_lit 0) A10K2.t3687 from rfl, allE_node, rows3686, irow3679, rows3687]
  all_goals rfl

theorem atot3679 : totK PA10K2 A10K2.u3679 = [0, 0, 456732611805, 2349846813325, 3919386843083, 2223374381661, 443811040704, 30650496230, 0, 0] := by
  rw [show A10K2.u3679 = KTree.node A10K2.t3686 (nat_lit 59805953) (nat_lit 10404522250) (nat_lit 0) A10K2.t3687 from rfl, totK_node, tot3686, tot3687]
  decide +kernel

theorem arows3682 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3682 = true := by
  rw [show A10K2.u3682 = KTree.node A10K2.t3688 (nat_lit 59819859) (nat_lit 9157592675) (nat_lit 0) A10K2.t3689 from rfl, allE_node, rows3688, irow3682, rows3689]
  all_goals rfl

theorem atot3682 : totK PA10K2 A10K2.u3682 = [0, 0, 778410583582, 3379839173102, 4072772668332, 1220513319585, 78932638602, 0, 0, 0] := by
  rw [show A10K2.u3682 = KTree.node A10K2.t3688 (nat_lit 59819859) (nat_lit 9157592675) (nat_lit 0) A10K2.t3689 from rfl, totK_node, tot3688, tot3689]
  decide +kernel

theorem arows3683 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3683 = true := by
  rw [show A10K2.u3683 = KTree.node A10K2.t3690 (nat_lit 59826984) (nat_lit 12158729684) (nat_lit 0) A10K2.t3691 from rfl, allE_node, rows3690, irow3683, rows3691]
  all_goals rfl

theorem atot3683 : totK PA10K2 A10K2.u3683 = [0, 582775338075, 2122550201012, 2924950802901, 2529484395315, 1183819767733, 179533038711, 5546304973, 0, 0] := by
  rw [show A10K2.u3683 = KTree.node A10K2.t3690 (nat_lit 59826984) (nat_lit 12158729684) (nat_lit 0) A10K2.t3691 from rfl, totK_node, tot3690, tot3691]
  decide +kernel

theorem arows3685 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3685 = true := by
  rw [show A10K2.u3685 = KTree.node A10K2.t3692 (nat_lit 59848121) (nat_lit 3553096973) (nat_lit 0) A10K2.t3693 from rfl, allE_node, rows3692, irow3685, rows3693]
  all_goals rfl

theorem atot3685 : totK PA10K2 A10K2.u3685 = [0, 232933380217, 1870050574109, 4079340887575, 2894527414595, 589520326551, 31768748853, 0, 0, 0] := by
  rw [show A10K2.u3685 = KTree.node A10K2.t3692 (nat_lit 59848121) (nat_lit 3553096973) (nat_lit 0) A10K2.t3693 from rfl, totK_node, tot3692, tot3693]
  decide +kernel

theorem arows3686 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3686 = true := by
  rw [show A10K2.u3686 = KTree.node A10K2.t3694 (nat_lit 59852564) (nat_lit 13049808624) (nat_lit 0) A10K2.t3695 from rfl, allE_node, rows3694, irow3686, rows3695]
  all_goals rfl

theorem atot3686 : totK PA10K2 A10K2.u3686 = [0, 781826896359, 3208208125068, 3977086416298, 1497744291170, 133146796736, 0, 0, 0, 0] := by
  rw [show A10K2.u3686 = KTree.node A10K2.t3694 (nat_lit 59852564) (nat_lit 13049808624) (nat_lit 0) A10K2.t3695 from rfl, totK_node, tot3694, tot3695]
  decide +kernel

theorem arows3690 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3690 = true := by
  rw [show A10K2.u3690 = KTree.node A10K2.t3696 (nat_lit 59860409) (nat_lit 5443028371) (nat_lit 0) A10K2.t3697 from rfl, allE_node, rows3696, irow3690, rows3697]
  all_goals rfl

theorem atot3690 : totK PA10K2 A10K2.u3690 = [0, 502723522018, 2549203320785, 4221963955759, 2299374256583, 316789827718, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u3690 = KTree.node A10K2.t3696 (nat_lit 59860409) (nat_lit 5443028371) (nat_lit 0) A10K2.t3697 from rfl, totK_node, tot3696, tot3697]
  decide +kernel

theorem arows3691 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3691 = true := by
  rw [show A10K2.u3691 = KTree.node A10K2.t3698 (nat_lit 59876759) (nat_lit 14237883125) (nat_lit 0) A10K2.t3699 from rfl, allE_node, rows3698, irow3691, rows3699]
  all_goals rfl

theorem atot3691 : totK PA10K2 A10K2.u3691 = [0, 0, 990685776188, 3718303146557, 3984710174415, 1157155075046, 75335321539, 0, 0, 0] := by
  rw [show A10K2.u3691 = KTree.node A10K2.t3698 (nat_lit 59876759) (nat_lit 14237883125) (nat_lit 0) A10K2.t3699 from rfl, totK_node, tot3698, tot3699]
  decide +kernel

theorem arows3693 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3693 = true := by
  rw [show A10K2.u3693 = KTree.node A10K2.t3700 (nat_lit 59881406) (nat_lit 13800404345) (nat_lit 0) A10K2.t3701 from rfl, allE_node, rows3700, irow3693, rows3701]
  all_goals rfl

theorem atot3693 : totK PA10K2 A10K2.u3693 = [0, 0, 293962571262, 1949386981823, 3945905084881, 2742910010737, 567727731755, 31082886609, 0, 0] := by
  rw [show A10K2.u3693 = KTree.node A10K2.t3700 (nat_lit 59881406) (nat_lit 13800404345) (nat_lit 0) A10K2.t3701 from rfl, totK_node, tot3700, tot3701]
  decide +kernel

theorem arows3694 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3694 = true := by
  rw [show A10K2.u3694 = KTree.node A10K2.t3702 (nat_lit 59885907) (nat_lit 10326093066) (nat_lit 0) A10K2.t3703 from rfl, allE_node, rows3702, irow3694, rows3703]
  all_goals rfl

theorem atot3694 : totK PA10K2 A10K2.u3694 = [0, 0, 584263778251, 2950734218708, 4228944204646, 1589627243666, 109291298544, 0, 0, 0] := by
  rw [show A10K2.u3694 = KTree.node A10K2.t3702 (nat_lit 59885907) (nat_lit 10326093066) (nat_lit 0) A10K2.t3703 from rfl, totK_node, tot3702, tot3703]
  decide +kernel

theorem arows3697 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3697 = true := by
  rw [show A10K2.u3697 = KTree.node A10K2.t3704 (nat_lit 59895191) (nat_lit 14616934806) (nat_lit 0) A10K2.t3705 from rfl, allE_node, rows3704, irow3697, rows3705]
  all_goals rfl

theorem atot3697 : totK PA10K2 A10K2.u3697 = [0, 385220696395, 1714956594856, 3058361965399, 2951107475156, 1391514005564, 204863376814, 6121173289, 0, 0] := by
  rw [show A10K2.u3697 = KTree.node A10K2.t3704 (nat_lit 59895191) (nat_lit 14616934806) (nat_lit 0) A10K2.t3705 from rfl, totK_node, tot3704, tot3705]
  decide +kernel

theorem arows3698 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3698 = true := by
  rw [show A10K2.u3698 = KTree.node A10K2.t3706 (nat_lit 59904384) (nat_lit 15445956646) (nat_lit 0) A10K2.t3707 from rfl, allE_node, rows3706, irow3698, rows3707]
  all_goals rfl

theorem atot3698 : totK PA10K2 A10K2.u3698 = [0, 311403322303, 2001343157726, 3852672486144, 2531346113296, 504268195577, 30831673886, 0, 0, 0] := by
  rw [show A10K2.u3698 = KTree.node A10K2.t3706 (nat_lit 59904384) (nat_lit 15445956646) (nat_lit 0) A10K2.t3707 from rfl, totK_node, tot3706, tot3707]
  decide +kernel

theorem arows3700 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3700 = true := by
  rw [show A10K2.u3700 = KTree.node A10K2.t3708 (nat_lit 59910700) (nat_lit 13050340309) (nat_lit 0) A10K2.t3709 from rfl, allE_node, rows3708, irow3700, rows3709]
  all_goals rfl

theorem atot3700 : totK PA10K2 A10K2.u3700 = [0, 749997641183, 3034835887758, 3893048785704, 1708898814260, 280427550769, 20340910120, 0, 0, 0] := by
  rw [show A10K2.u3700 = KTree.node A10K2.t3708 (nat_lit 59910700) (nat_lit 13050340309) (nat_lit 0) A10K2.t3709 from rfl, totK_node, tot3708, tot3709]
  decide +kernel

theorem arows3701 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3701 = true := by
  rw [show A10K2.u3701 = KTree.node A10K2.t3710 (nat_lit 59916553) (nat_lit 9757796508) (nat_lit 0) A10K2.t3711 from rfl, allE_node, rows3710, irow3701, rows3711]
  all_goals rfl

theorem atot3701 : totK PA10K2 A10K2.u3701 = [0, 538864630786, 2414163214974, 3804039509899, 2323161382601, 414429899638, 11427838733, 0, 0, 0] := by
  rw [show A10K2.u3701 = KTree.node A10K2.t3710 (nat_lit 59916553) (nat_lit 9757796508) (nat_lit 0) A10K2.t3711 from rfl, totK_node, tot3710, tot3711]
  decide +kernel

theorem arows3708 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3708 = true := by
  rw [show A10K2.u3708 = KTree.node A10K2.t3712 (nat_lit 59921669) (nat_lit 6950600564) (nat_lit 0) A10K2.t3713 from rfl, allE_node, rows3712, irow3708, rows3713]
  all_goals rfl

theorem atot3708 : totK PA10K2 A10K2.u3708 = [0, 295989007569, 2255982852479, 4275409594649, 2332491106838, 309305900333, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u3708 = KTree.node A10K2.t3712 (nat_lit 59921669) (nat_lit 6950600564) (nat_lit 0) A10K2.t3713 from rfl, totK_node, tot3712, tot3713]
  decide +kernel

theorem arows3709 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3709 = true := by
  rw [show A10K2.u3709 = KTree.node A10K2.t3714 (nat_lit 59936193) (nat_lit 10094729673) (nat_lit 0) A10K2.t3715 from rfl, allE_node, rows3714, irow3709, rows3715]
  all_goals rfl

theorem atot3709 : totK PA10K2 A10K2.u3709 = [0, 0, 951536103081, 3496819766502, 3812505549513, 1053019161956, 64899520130, 0, 0, 0] := by
  rw [show A10K2.u3709 = KTree.node A10K2.t3714 (nat_lit 59936193) (nat_lit 10094729673) (nat_lit 0) A10K2.t3715 from rfl, totK_node, tot3714, tot3715]
  decide +kernel

theorem arows3711 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3711 = true := by
  rw [show A10K2.u3711 = KTree.node A10K2.t3716 (nat_lit 59949641) (nat_lit 8629483964) (nat_lit 0) A10K2.t3717 from rfl, allE_node, rows3716, irow3711, rows3717]
  all_goals rfl

theorem atot3711 : totK PA10K2 A10K2.u3711 = [0, 0, 1012626381726, 3634007234172, 3803991060185, 1017148575300, 63495312472, 0, 0, 0] := by
  rw [show A10K2.u3711 = KTree.node A10K2.t3716 (nat_lit 59949641) (nat_lit 8629483964) (nat_lit 0) A10K2.t3717 from rfl, totK_node, tot3716, tot3717]
  decide +kernel

theorem arows3712 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3712 = true := by
  rw [show A10K2.u3712 = KTree.node A10K2.t3718 (nat_lit 59955413) (nat_lit 6365199804) (nat_lit 0) A10K2.t3719 from rfl, allE_node, rows3718, irow3712, rows3719]
  all_goals rfl

theorem atot3712 : totK PA10K2 A10K2.u3712 = [0, 0, 342891817455, 2421192074471, 4217095172027, 2002280527984, 291459347602, 6354482628, 0, 0] := by
  rw [show A10K2.u3712 = KTree.node A10K2.t3718 (nat_lit 59955413) (nat_lit 6365199804) (nat_lit 0) A10K2.t3719 from rfl, totK_node, tot3718, tot3719]
  decide +kernel

theorem arows3715 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3715 = true := by
  rw [show A10K2.u3715 = KTree.node A10K2.t3720 (nat_lit 60035168) (nat_lit 13870624922) (nat_lit 0) A10K2.t3721 from rfl, allE_node, rows3720, irow3715, rows3721]
  all_goals rfl

theorem atot3715 : totK PA10K2 A10K2.u3715 = [0, 0, 457783257613, 2277345804153, 3887476104644, 2398687255822, 455969393503, 30818366867, 0, 0] := by
  rw [show A10K2.u3715 = KTree.node A10K2.t3720 (nat_lit 60035168) (nat_lit 13870624922) (nat_lit 0) A10K2.t3721 from rfl, totK_node, tot3720, tot3721]
  decide +kernel

theorem arows3716 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3716 = true := by
  rw [show A10K2.u3716 = KTree.node A10K2.t3722 (nat_lit 60049054) (nat_lit 12146181424) (nat_lit 0) A10K2.t3723 from rfl, allE_node, rows3722, irow3716, rows3723]
  all_goals rfl

theorem atot3716 : totK PA10K2 A10K2.u3716 = [0, 0, 777926418751, 3231245105452, 4021942135518, 1407066297715, 100997783827, 0, 0, 0] := by
  rw [show A10K2.u3716 = KTree.node A10K2.t3722 (nat_lit 60049054) (nat_lit 12146181424) (nat_lit 0) A10K2.t3723 from rfl, totK_node, tot3722, tot3723]
  decide +kernel

theorem arows3718 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3718 = true := by
  rw [show A10K2.u3718 = KTree.node A10K2.t3724 (nat_lit 60055906) (nat_lit 7994404350) (nat_lit 0) A10K2.t3725 from rfl, allE_node, rows3724, irow3718, rows3725]
  all_goals rfl

theorem atot3718 : totK PA10K2 A10K2.u3718 = [0, 0, 578193655896, 2603463038710, 3965050783035, 2069602949376, 299460808653, 6354482628, 0, 0] := by
  rw [show A10K2.u3718 = KTree.node A10K2.t3724 (nat_lit 60055906) (nat_lit 7994404350) (nat_lit 0) A10K2.t3725 from rfl, totK_node, tot3724, tot3725]
  decide +kernel

theorem arows3719 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3719 = true := by
  rw [show A10K2.u3719 = KTree.node A10K2.t3726 (nat_lit 60108231) (nat_lit 13834645836) (nat_lit 0) A10K2.t3727 from rfl, allE_node, rows3726, irow3719, rows3727]
  all_goals rfl

theorem atot3719 : totK PA10K2 A10K2.u3719 = [0, 0, 503333154511, 2508253936157, 3999987705746, 2199528116595, 416919651691, 25734533292, 0, 0] := by
  rw [show A10K2.u3719 = KTree.node A10K2.t3726 (nat_lit 60108231) (nat_lit 13834645836) (nat_lit 0) A10K2.t3727 from rfl, totK_node, tot3726, tot3727]
  decide +kernel

theorem arows3723 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3723 = true := by
  rw [show A10K2.u3723 = KTree.node A10K2.t3728 (nat_lit 60113664) (nat_lit 14565965058) (nat_lit 0) A10K2.t3729 from rfl, allE_node, rows3728, irow3723, rows3729]
  all_goals rfl

theorem atot3723 : totK PA10K2 A10K2.u3723 = [0, 0, 779803666384, 2885919172867, 3730996544632, 1891019732949, 254743065708, 5718040558, 0, 0] := by
  rw [show A10K2.u3723 = KTree.node A10K2.t3728 (nat_lit 60113664) (nat_lit 14565965058) (nat_lit 0) A10K2.t3729 from rfl, totK_node, tot3728, tot3729]
  decide +kernel

theorem arows3724 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3724 = true := by
  rw [show A10K2.u3724 = KTree.node A10K2.t3730 (nat_lit 60119301) (nat_lit 7040787894) (nat_lit 0) A10K2.t3731 from rfl, allE_node, rows3730, irow3724, rows3731]
  all_goals rfl

theorem atot3724 : totK PA10K2 A10K2.u3724 = [0, 0, 390762680392, 2450145838911, 4268805147181, 2198015311281, 300601247933, 6354482628, 0, 0] := by
  rw [show A10K2.u3724 = KTree.node A10K2.t3730 (nat_lit 60119301) (nat_lit 7040787894) (nat_lit 0) A10K2.t3731 from rfl, totK_node, tot3730, tot3731]
  decide +kernel

theorem arows3726 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3726 = true := by
  rw [show A10K2.u3726 = KTree.node A10K2.t3732 (nat_lit 60128689) (nat_lit 8257112776) (nat_lit 0) A10K2.t3733 from rfl, allE_node, rows3732, irow3726, rows3733]
  all_goals rfl

theorem atot3726 : totK PA10K2 A10K2.u3726 = [0, 0, 677639267173, 2791821152247, 3932317479805, 2127626777537, 316512928086, 6962742351, 0, 0] := by
  rw [show A10K2.u3726 = KTree.node A10K2.t3732 (nat_lit 60128689) (nat_lit 8257112776) (nat_lit 0) A10K2.t3733 from rfl, totK_node, tot3732, tot3733]
  decide +kernel

theorem arows3727 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3727 = true := by
  rw [show A10K2.u3727 = KTree.node A10K2.t3734 (nat_lit 60166948) (nat_lit 13650589155) (nat_lit 0) A10K2.t3735 from rfl, allE_node, rows3734, irow3727, rows3735]
  all_goals rfl

theorem atot3727 : totK PA10K2 A10K2.u3727 = [0, 0, 424305048878, 2104135867788, 3790202027272, 2295314434849, 454661206129, 30074883546, 0, 0] := by
  rw [show A10K2.u3727 = KTree.node A10K2.t3734 (nat_lit 60166948) (nat_lit 13650589155) (nat_lit 0) A10K2.t3735 from rfl, totK_node, tot3734, tot3735]
  decide +kernel

theorem arows3730 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3730 = true := by
  rw [show A10K2.u3730 = KTree.node A10K2.t3736 (nat_lit 60173718) (nat_lit 13946581908) (nat_lit 0) A10K2.t3737 from rfl, allE_node, rows3736, irow3730, rows3737]
  all_goals rfl

theorem atot3730 : totK PA10K2 A10K2.u3730 = [0, 0, 454642566388, 2546111040232, 4087356416817, 2089473584340, 350584490309, 24969229125, 0, 0] := by
  rw [show A10K2.u3730 = KTree.node A10K2.t3736 (nat_lit 60173718) (nat_lit 13946581908) (nat_lit 0) A10K2.t3737 from rfl, totK_node, tot3736, tot3737]
  decide +kernel

theorem arows3731 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3731 = true := by
  rw [show A10K2.u3731 = KTree.node A10K2.t3738 (nat_lit 60179282) (nat_lit 12658409085) (nat_lit 0) A10K2.t3739 from rfl, allE_node, rows3738, irow3731, rows3739]
  all_goals rfl

theorem atot3731 : totK PA10K2 A10K2.u3731 = [0, 0, 846697737338, 3066855787919, 3642081689200, 1627692338701, 222207808802, 6034215561, 0, 0] := by
  rw [show A10K2.u3731 = KTree.node A10K2.t3738 (nat_lit 60179282) (nat_lit 12658409085) (nat_lit 0) A10K2.t3739 from rfl, totK_node, tot3738, tot3739]
  decide +kernel

theorem arows3733 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3733 = true := by
  rw [show A10K2.u3733 = KTree.node A10K2.t3740 (nat_lit 60184796) (nat_lit 11107961971) (nat_lit 0) A10K2.t3741 from rfl, allE_node, rows3740, irow3733, rows3741]
  all_goals rfl

theorem atot3733 : totK PA10K2 A10K2.u3733 = [0, 0, 0, 1492241673131, 4223587854879, 2883534338219, 556701478162, 31193230065, 0, 0] := by
  rw [show A10K2.u3733 = KTree.node A10K2.t3740 (nat_lit 60184796) (nat_lit 11107961971) (nat_lit 0) A10K2.t3741 from rfl, totK_node, tot3740, tot3741]
  decide +kernel

theorem arows3734 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3734 = true := by
  rw [show A10K2.u3734 = KTree.node A10K2.t3742 (nat_lit 60204717) (nat_lit 5944114305) (nat_lit 0) A10K2.t3743 from rfl, allE_node, rows3742, irow3734, rows3743]
  all_goals rfl

theorem atot3734 : totK PA10K2 A10K2.u3734 = [0, 0, 0, 1154006028756, 3916912726379, 3479384906577, 770874640967, 38045387652, 0, 0] := by
  rw [show A10K2.u3734 = KTree.node A10K2.t3742 (nat_lit 60204717) (nat_lit 5944114305) (nat_lit 0) A10K2.t3743 from rfl, totK_node, tot3742, tot3743]
  decide +kernel

theorem arows3739 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3739 = true := by
  rw [show A10K2.u3739 = KTree.node A10K2.t3744 (nat_lit 60213248) (nat_lit 15064410632) (nat_lit 0) A10K2.t3745 from rfl, allE_node, rows3744, irow3739, rows3745]
  all_goals rfl

theorem atot3739 : totK PA10K2 A10K2.u3739 = [0, 0, 0, 727444888492, 3194533134399, 3841295365801, 1220953201850, 102081032701, 0, 0] := by
  rw [show A10K2.u3739 = KTree.node A10K2.t3744 (nat_lit 60213248) (nat_lit 15064410632) (nat_lit 0) A10K2.t3745 from rfl, totK_node, tot3744, tot3745]
  decide +kernel

theorem arows3740 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3740 = true := by
  rw [show A10K2.u3740 = KTree.node A10K2.t3746 (nat_lit 60817957) (nat_lit 6956416829) (nat_lit 0) A10K2.t3747 from rfl, allE_node, rows3746, irow3740, rows3747]
  all_goals rfl

theorem atot3740 : totK PA10K2 A10K2.u3740 = [0, 0, 840727299041, 2752291454811, 2874683069401, 1768673351604, 1018022102591, 213642913445, 6354482628, 0] := by
  rw [show A10K2.u3740 = KTree.node A10K2.t3746 (nat_lit 60817957) (nat_lit 6956416829) (nat_lit 0) A10K2.t3747 from rfl, totK_node, tot3746, tot3747]
  decide +kernel

theorem arows3742 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3742 = true := by
  rw [show A10K2.u3742 = KTree.node A10K2.t3748 (nat_lit 60823617) (nat_lit 10302278770) (nat_lit 0) A10K2.t3749 from rfl, allE_node, rows3748, irow3742, rows3749]
  all_goals rfl

theorem atot3742 : totK PA10K2 A10K2.u3742 = [0, 0, 290498283436, 1885867638384, 3963868481559, 2871941893616, 579269138377, 30831673886, 0, 0] := by
  rw [show A10K2.u3742 = KTree.node A10K2.t3748 (nat_lit 60823617) (nat_lit 10302278770) (nat_lit 0) A10K2.t3749 from rfl, totK_node, tot3748, tot3749]
  decide +kernel

theorem arows3743 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3743 = true := by
  rw [show A10K2.u3743 = KTree.node A10K2.t3750 (nat_lit 60836396) (nat_lit 13070434595) (nat_lit 0) A10K2.t3751 from rfl, allE_node, rows3750, irow3743, rows3751]
  all_goals rfl

theorem atot3743 : totK PA10K2 A10K2.u3743 = [0, 0, 453828566602, 2709198554703, 4347378964500, 1737120250743, 115449264117, 0, 0, 0] := by
  rw [show A10K2.u3743 = KTree.node A10K2.t3750 (nat_lit 60836396) (nat_lit 13070434595) (nat_lit 0) A10K2.t3751 from rfl, totK_node, tot3750, tot3751]
  decide +kernel

theorem arows3746 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3746 = true := by
  rw [show A10K2.u3746 = KTree.node A10K2.t3752 (nat_lit 60845463) (nat_lit 14616934806) (nat_lit 0) A10K2.t3753 from rfl, allE_node, rows3752, irow3746, rows3753]
  all_goals rfl

theorem atot3746 : totK PA10K2 A10K2.u3746 = [0, 0, 593403324104, 2583006108498, 3959664677830, 2449930755833, 423304603510, 13207830636, 0, 0] := by
  rw [show A10K2.u3746 = KTree.node A10K2.t3752 (nat_lit 60845463) (nat_lit 14616934806) (nat_lit 0) A10K2.t3753 from rfl, totK_node, tot3752, tot3753]
  decide +kernel

theorem arows3747 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3747 = true := by
  rw [show A10K2.u3747 = KTree.node A10K2.t3754 (nat_lit 60851080) (nat_lit 14261625976) (nat_lit 0) A10K2.t3755 from rfl, allE_node, rows3754, irow3747, rows3755]
  all_goals rfl

theorem atot3747 : totK PA10K2 A10K2.u3747 = [0, 0, 0, 1099005620170, 3931255108861, 3921257507080, 920208661404, 43910551696, 0, 0] := by
  rw [show A10K2.u3747 = KTree.node A10K2.t3754 (nat_lit 60851080) (nat_lit 14261625976) (nat_lit 0) A10K2.t3755 from rfl, totK_node, tot3754, tot3755]
  decide +kernel

theorem arows3749 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3749 = true := by
  rw [show A10K2.u3749 = KTree.node A10K2.t3756 (nat_lit 60868769) (nat_lit 8246437863) (nat_lit 0) A10K2.t3757 from rfl, allE_node, rows3756, irow3749, rows3757]
  all_goals rfl

theorem atot3749 : totK PA10K2 A10K2.u3749 = [0, 0, 0, 660490378325, 3186339716740, 4117778414198, 1219088174873, 90161000571, 0, 0] := by
  rw [show A10K2.u3749 = KTree.node A10K2.t3756 (nat_lit 60868769) (nat_lit 8246437863) (nat_lit 0) A10K2.t3757 from rfl, totK_node, tot3756, tot3757]
  decide +kernel

theorem arows3750 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3750 = true := by
  rw [show A10K2.u3750 = KTree.node A10K2.t3758 (nat_lit 60878043) (nat_lit 7109919633) (nat_lit 0) A10K2.t3759 from rfl, allE_node, rows3758, irow3750, rows3759]
  all_goals rfl

theorem atot3750 : totK PA10K2 A10K2.u3750 = [0, 0, 536209087732, 2216219105938, 3486216929426, 2505055884808, 880635875173, 141559855606, 5546304973, 0] := by
  rw [show A10K2.u3750 = KTree.node A10K2.t3758 (nat_lit 60878043) (nat_lit 7109919633) (nat_lit 0) A10K2.t3759 from rfl, totK_node, tot3758, tot3759]
  decide +kernel

theorem arows3754 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3754 = true := by
  rw [show A10K2.u3754 = KTree.node A10K2.t3760 (nat_lit 60953047) (nat_lit 10029406740) (nat_lit 0) A10K2.t3761 from rfl, allE_node, rows3760, irow3754, rows3761]
  all_goals rfl

theorem atot3754 : totK PA10K2 A10K2.u3754 = [0, 0, 273543959815, 1982569174562, 4082522974842, 2749311767761, 497757685702, 30831673886, 0, 0] := by
  rw [show A10K2.u3754 = KTree.node A10K2.t3760 (nat_lit 60953047) (nat_lit 10029406740) (nat_lit 0) A10K2.t3761 from rfl, totK_node, tot3760, tot3761]
  decide +kernel

theorem arows3755 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3755 = true := by
  rw [show A10K2.u3755 = KTree.node A10K2.t3762 (nat_lit 60959517) (nat_lit 6289835514) (nat_lit 0) A10K2.t3763 from rfl, allE_node, rows3762, irow3755, rows3763]
  all_goals rfl

theorem atot3755 : totK PA10K2 A10K2.u3755 = [0, 0, 516667892269, 2519761081216, 4037783709934, 2180713419600, 278177661602, 5393623172, 0, 0] := by
  rw [show A10K2.u3755 = KTree.node A10K2.t3762 (nat_lit 60959517) (nat_lit 6289835514) (nat_lit 0) A10K2.t3763 from rfl, totK_node, tot3762, tot3763]
  decide +kernel

theorem arows3757 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3757 = true := by
  rw [show A10K2.u3757 = KTree.node A10K2.t3764 (nat_lit 60966619) (nat_lit 9729004333) (nat_lit 0) A10K2.t3765 from rfl, allE_node, rows3764, irow3757, rows3765]
  all_goals rfl

theorem atot3757 : totK PA10K2 A10K2.u3757 = [0, 0, 815829842394, 3237360779410, 3795760634215, 1389850110796, 183045312739, 6034215561, 0, 0] := by
  rw [show A10K2.u3757 = KTree.node A10K2.t3764 (nat_lit 60966619) (nat_lit 9729004333) (nat_lit 0) A10K2.t3765 from rfl, totK_node, tot3764, tot3765]
  decide +kernel

theorem arows3758 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3758 = true := by
  rw [show A10K2.u3758 = KTree.node A10K2.t3766 (nat_lit 60981511) (nat_lit 10295367160) (nat_lit 0) A10K2.t3767 from rfl, allE_node, rows3766, irow3758, rows3767]
  all_goals rfl

theorem atot3758 : totK PA10K2 A10K2.u3758 = [0, 0, 0, 1158051711945, 3911627027859, 3532695692483, 734951579894, 38342359577, 0, 0] := by
  rw [show A10K2.u3758 = KTree.node A10K2.t3766 (nat_lit 60981511) (nat_lit 10295367160) (nat_lit 0) A10K2.t3767 from rfl, totK_node, tot3766, tot3767]
  decide +kernel

theorem arows3761 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3761 = true := by
  rw [show A10K2.u3761 = KTree.node A10K2.t3768 (nat_lit 60991756) (nat_lit 12074599327) (nat_lit 0) A10K2.t3769 from rfl, allE_node, rows3768, irow3761, rows3769]
  all_goals rfl

theorem atot3761 : totK PA10K2 A10K2.u3761 = [0, 0, 0, 1103221084847, 3953393707925, 3763215191051, 756489624535, 36615231393, 0, 0] := by
  rw [show A10K2.u3761 = KTree.node A10K2.t3768 (nat_lit 60991756) (nat_lit 12074599327) (nat_lit 0) A10K2.t3769 from rfl, totK_node, tot3768, tot3769]
  decide +kernel

theorem arows3762 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3762 = true := by
  rw [show A10K2.u3762 = KTree.node A10K2.t3770 (nat_lit 61001985) (nat_lit 10329861105) (nat_lit 0) A10K2.t3771 from rfl, allE_node, rows3770, irow3762, rows3771]
  all_goals rfl

theorem atot3762 : totK PA10K2 A10K2.u3762 = [0, 0, 118410781347, 686996895894, 2603749593895, 3942214820114, 1695244825361, 221145934464, 6354482628, 0] := by
  rw [show A10K2.u3762 = KTree.node A10K2.t3770 (nat_lit 61001985) (nat_lit 10329861105) (nat_lit 0) A10K2.t3771 from rfl, totK_node, tot3770, tot3771]
  decide +kernel

theorem arows3764 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3764 = true := by
  rw [show A10K2.u3764 = KTree.node A10K2.t3772 (nat_lit 61418304) (nat_lit 9858292692) (nat_lit 0) A10K2.t3773 from rfl, allE_node, rows3772, irow3764, rows3773]
  all_goals rfl

theorem atot3764 : totK PA10K2 A10K2.u3764 = [0, 0, 741794313646, 3197841502601, 4159156307357, 1607324273493, 129666445646, 0, 0, 0] := by
  rw [show A10K2.u3764 = KTree.node A10K2.t3772 (nat_lit 61418304) (nat_lit 9858292692) (nat_lit 0) A10K2.t3773 from rfl, totK_node, tot3772, tot3773]
  decide +kernel

theorem arows3765 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3765 = true := by
  rw [show A10K2.u3765 = KTree.node A10K2.t3774 (nat_lit 61423044) (nat_lit 1185866097) (nat_lit 0) A10K2.t3775 from rfl, allE_node, rows3774, irow3765, rows3775]
  all_goals rfl

theorem atot3765 : totK PA10K2 A10K2.u3765 = [0, 0, 457229152946, 2166513021357, 3719935602170, 2571922830598, 562749713457, 31768748853, 0, 0] := by
  rw [show A10K2.u3765 = KTree.node A10K2.t3774 (nat_lit 61423044) (nat_lit 1185866097) (nat_lit 0) A10K2.t3775 from rfl, totK_node, tot3774, tot3775]
  decide +kernel

theorem arows3771 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3771 = true := by
  rw [show A10K2.u3771 = KTree.node A10K2.t3776 (nat_lit 61429142) (nat_lit 15221483549) (nat_lit 0) A10K2.t3777 from rfl, allE_node, rows3776, irow3771, rows3777]
  all_goals rfl

theorem atot3771 : totK PA10K2 A10K2.u3771 = [0, 0, 642565773208, 2752339808055, 3983989779682, 1933180872105, 243650626530, 6354482628, 0, 0] := by
  rw [show A10K2.u3771 = KTree.node A10K2.t3776 (nat_lit 61429142) (nat_lit 15221483549) (nat_lit 0) A10K2.t3777 from rfl, totK_node, tot3776, tot3777]
  decide +kernel

theorem arows3772 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3772 = true := by
  rw [show A10K2.u3772 = KTree.node A10K2.t3778 (nat_lit 61436295) (nat_lit 14471687564) (nat_lit 0) A10K2.t3779 from rfl, allE_node, rows3778, irow3772, rows3779]
  all_goals rfl

theorem atot3772 : totK PA10K2 A10K2.u3772 = [0, 0, 338266079698, 2298693775368, 4452378180078, 2821933397035, 407005323147, 6962742351, 0, 0] := by
  rw [show A10K2.u3772 = KTree.node A10K2.t3778 (nat_lit 61436295) (nat_lit 14471687564) (nat_lit 0) A10K2.t3779 from rfl, totK_node, tot3778, tot3779]
  decide +kernel

theorem arows3774 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3774 = true := by
  rw [show A10K2.u3774 = KTree.node A10K2.t3780 (nat_lit 61450391) (nat_lit 12087012632) (nat_lit 0) A10K2.t3781 from rfl, allE_node, rows3780, irow3774, rows3781]
  all_goals rfl

theorem atot3774 : totK PA10K2 A10K2.u3774 = [0, 0, 0, 857014542868, 3448766650257, 4085862047028, 1308717320195, 91911686939, 0, 0] := by
  rw [show A10K2.u3774 = KTree.node A10K2.t3780 (nat_lit 61450391) (nat_lit 12087012632) (nat_lit 0) A10K2.t3781 from rfl, totK_node, tot3780, tot3781]
  decide +kernel

theorem arows3775 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3775 = true := by
  rw [show A10K2.u3775 = KTree.node A10K2.t3782 (nat_lit 61455118) (nat_lit 581521316) (nat_lit 0) A10K2.t3783 from rfl, allE_node, rows3782, irow3775, rows3783]
  all_goals rfl

theorem atot3775 : totK PA10K2 A10K2.u3775 = [0, 0, 0, 456920526858, 2180045101458, 3743822153508, 2435602977073, 542157487626, 31082886609, 0] := by
  rw [show A10K2.u3775 = KTree.node A10K2.t3782 (nat_lit 61455118) (nat_lit 581521316) (nat_lit 0) A10K2.t3783 from rfl, totK_node, tot3782, tot3783]
  decide +kernel

theorem arows3778 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3778 = true := by
  rw [show A10K2.u3778 = KTree.node A10K2.t3784 (nat_lit 61461676) (nat_lit 12530468901) (nat_lit 0) A10K2.t3785 from rfl, allE_node, rows3784, irow3778, rows3785]
  all_goals rfl

theorem atot3778 : totK PA10K2 A10K2.u3778 = [0, 0, 0, 501205492732, 2630308375911, 4183822927743, 1910724778934, 227698315526, 6121173289, 0] := by
  rw [show A10K2.u3778 = KTree.node A10K2.t3784 (nat_lit 61461676) (nat_lit 12530468901) (nat_lit 0) A10K2.t3785 from rfl, totK_node, tot3784, tot3785]
  decide +kernel

theorem arows3779 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3779 = true := by
  rw [show A10K2.u3779 = KTree.node A10K2.t3786 (nat_lit 61468573) (nat_lit 2679161789) (nat_lit 0) A10K2.t3787 from rfl, allE_node, rows3786, irow3779, rows3787]
  all_goals rfl

theorem atot3779 : totK PA10K2 A10K2.u3779 = [0, 0, 516552094339, 2318496623087, 3579464793907, 2536822760049, 748888526708, 56732679026, 0, 0] := by
  rw [show A10K2.u3779 = KTree.node A10K2.t3786 (nat_lit 61468573) (nat_lit 2679161789) (nat_lit 0) A10K2.t3787 from rfl, totK_node, tot3786, tot3787]
  decide +kernel

theorem arows3781 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3781 = true := by
  rw [show A10K2.u3781 = KTree.node A10K2.t3788 (nat_lit 61482134) (nat_lit 14612539823) (nat_lit 0) A10K2.t3789 from rfl, allE_node, rows3788, irow3781, rows3789]
  all_goals rfl

theorem atot3781 : totK PA10K2 A10K2.u3781 = [0, 0, 584594178835, 2514544055665, 3838263822644, 2107528163228, 329531262266, 10760911071, 0, 0] := by
  rw [show A10K2.u3781 = KTree.node A10K2.t3788 (nat_lit 61482134) (nat_lit 14612539823) (nat_lit 0) A10K2.t3789 from rfl, totK_node, tot3788, tot3789]
  decide +kernel

theorem arows3782 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3782 = true := by
  rw [show A10K2.u3782 = KTree.node A10K2.t3790 (nat_lit 61486817) (nat_lit 3454178581) (nat_lit 0) A10K2.t3791 from rfl, allE_node, rows3790, irow3782, rows3791]
  all_goals rfl

theorem atot3782 : totK PA10K2 A10K2.u3782 = [0, 0, 300439572007, 1886714789992, 4013847340633, 2999210359756, 613700170625, 31768748853, 0, 0] := by
  rw [show A10K2.u3782 = KTree.node A10K2.t3790 (nat_lit 61486817) (nat_lit 3454178581) (nat_lit 0) A10K2.t3791 from rfl, totK_node, tot3790, tot3791]
  decide +kernel

theorem arows3786 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3786 = true := by
  rw [show A10K2.u3786 = KTree.node A10K2.t3792 (nat_lit 61491204) (nat_lit 12748852462) (nat_lit 0) A10K2.t3793 from rfl, allE_node, rows3792, irow3786, rows3793]
  all_goals rfl

theorem atot3786 : totK PA10K2 A10K2.u3786 = [0, 0, 714696690107, 3143548667141, 3965112355223, 1398986653195, 106433144500, 0, 0, 0] := by
  rw [show A10K2.u3786 = KTree.node A10K2.t3792 (nat_lit 61491204) (nat_lit 12748852462) (nat_lit 0) A10K2.t3793 from rfl, totK_node, tot3792, tot3793]
  decide +kernel

theorem arows3787 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3787 = true := by
  rw [show A10K2.u3787 = KTree.node A10K2.t3794 (nat_lit 61506090) (nat_lit 6246038997) (nat_lit 0) A10K2.t3795 from rfl, allE_node, rows3794, irow3787, rows3795]
  all_goals rfl

theorem atot3787 : totK PA10K2 A10K2.u3787 = [0, 0, 0, 1227255989195, 4100299185915, 3440770853658, 616539353532, 18095079033, 0, 0] := by
  rw [show A10K2.u3787 = KTree.node A10K2.t3794 (nat_lit 61506090) (nat_lit 6246038997) (nat_lit 0) A10K2.t3795 from rfl, totK_node, tot3794, tot3795]
  decide +kernel

theorem arows3789 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3789 = true := by
  rw [show A10K2.u3789 = KTree.node A10K2.t3796 (nat_lit 61517274) (nat_lit 14491231619) (nat_lit 0) A10K2.t3797 from rfl, allE_node, rows3796, irow3789, rows3797]
  all_goals rfl

theorem atot3789 : totK PA10K2 A10K2.u3789 = [0, 0, 0, 987663185609, 3662578213851, 3885093640000, 988107041161, 50077070082, 0, 0] := by
  rw [show A10K2.u3789 = KTree.node A10K2.t3796 (nat_lit 61517274) (nat_lit 14491231619) (nat_lit 0) A10K2.t3797 from rfl, totK_node, tot3796, tot3797]
  decide +kernel

theorem arows3790 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3790 = true := by
  rw [show A10K2.u3790 = KTree.node A10K2.t3798 (nat_lit 61526372) (nat_lit 13775768551) (nat_lit 0) A10K2.t3799 from rfl, allE_node, rows3798, irow3790, rows3799]
  all_goals rfl

theorem atot3790 : totK PA10K2 A10K2.u3790 = [0, 0, 202041260899, 712363574172, 2332375689575, 3887279716300, 1853494503244, 255457917856, 6354482628, 0] := by
  rw [show A10K2.u3790 = KTree.node A10K2.t3798 (nat_lit 61526372) (nat_lit 13775768551) (nat_lit 0) A10K2.t3799 from rfl, totK_node, tot3798, tot3799]
  decide +kernel

theorem arows3793 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3793 = true := by
  rw [show A10K2.u3793 = KTree.node A10K2.t3800 (nat_lit 61549811) (nat_lit 10126295530) (nat_lit 0) A10K2.t3801 from rfl, allE_node, rows3800, irow3793, rows3801]
  all_goals rfl

theorem atot3793 : totK PA10K2 A10K2.u3793 = [0, 0, 609207037005, 2868267383398, 4081399818280, 2072905924687, 373924057056, 20328650499, 0, 0] := by
  rw [show A10K2.u3793 = KTree.node A10K2.t3800 (nat_lit 61549811) (nat_lit 10126295530) (nat_lit 0) A10K2.t3801 from rfl, totK_node, tot3800, tot3801]
  decide +kernel

theorem arows3794 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3794 = true := by
  rw [show A10K2.u3794 = KTree.node A10K2.t3802 (nat_lit 61563461) (nat_lit 4958019997) (nat_lit 0) A10K2.t3803 from rfl, allE_node, rows3802, irow3794, rows3803]
  all_goals rfl

theorem atot3794 : totK PA10K2 A10K2.u3794 = [0, 0, 798450316783, 3122514278033, 4094438431277, 1968876267101, 280805407813, 11193583013, 0, 0] := by
  rw [show A10K2.u3794 = KTree.node A10K2.t3802 (nat_lit 61563461) (nat_lit 4958019997) (nat_lit 0) A10K2.t3803 from rfl, totK_node, tot3802, tot3803]
  decide +kernel

theorem arows3796 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3796 = true := by
  rw [show A10K2.u3796 = KTree.node A10K2.t3804 (nat_lit 61568691) (nat_lit 10246331566) (nat_lit 0) A10K2.t3805 from rfl, allE_node, rows3804, irow3796, rows3805]
  all_goals rfl

theorem atot3796 : totK PA10K2 A10K2.u3796 = [0, 0, 0, 1311442963872, 4269548150189, 3756584425548, 882444739735, 42874818239, 0, 0] := by
  rw [show A10K2.u3796 = KTree.node A10K2.t3804 (nat_lit 61568691) (nat_lit 10246331566) (nat_lit 0) A10K2.t3805 from rfl, totK_node, tot3804, tot3805]
  decide +kernel

theorem arows3797 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3797 = true := by
  rw [show A10K2.u3797 = KTree.node A10K2.t3806 (nat_lit 61582769) (nat_lit 8545629371) (nat_lit 0) A10K2.t3807 from rfl, allE_node, rows3806, irow3797, rows3807]
  all_goals rfl

theorem atot3797 : totK PA10K2 A10K2.u3797 = [0, 0, 0, 604120045713, 2897438449893, 4209554935519, 1950868737014, 277781853484, 7047025452, 0] := by
  rw [show A10K2.u3797 = KTree.node A10K2.t3806 (nat_lit 61582769) (nat_lit 8545629371) (nat_lit 0) A10K2.t3807 from rfl, totK_node, tot3806, tot3807]
  decide +kernel

theorem arows3802 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3802 = true := by
  rw [show A10K2.u3802 = KTree.node A10K2.t3808 (nat_lit 61598732) (nat_lit 5043801051) (nat_lit 8) A10K2.t3809 from rfl, allE_node, rows3808, irow3802, rows3809]
  all_goals rfl

theorem atot3802 : totK PA10K2 A10K2.u3802 = [0, 0, 302616931391, 1716839986343, 3618429941180, 3334212984805, 1136065714555, 83817335307, 0, 0] := by
  rw [show A10K2.u3802 = KTree.node A10K2.t3808 (nat_lit 61598732) (nat_lit 5043801051) (nat_lit 8) A10K2.t3809 from rfl, totK_node, tot3808, tot3809]
  decide +kernel

theorem arows3803 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3803 = true := by
  rw [show A10K2.u3803 = KTree.node A10K2.t3810 (nat_lit 61869638) (nat_lit 15109149156) (nat_lit 0) A10K2.t3811 from rfl, allE_node, rows3810, irow3803, rows3811]
  all_goals rfl

theorem atot3803 : totK PA10K2 A10K2.u3803 = [0, 0, 458388819914, 2423576909307, 4071677752046, 2209216715912, 359579605661, 25371180993, 0, 0] := by
  rw [show A10K2.u3803 = KTree.node A10K2.t3810 (nat_lit 61869638) (nat_lit 15109149156) (nat_lit 0) A10K2.t3811 from rfl, totK_node, tot3810, tot3811]
  decide +kernel

theorem arows3805 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3805 = true := by
  rw [show A10K2.u3805 = KTree.node A10K2.t3812 (nat_lit 61883539) (nat_lit 10954712508) (nat_lit 0) A10K2.t3813 from rfl, allE_node, rows3812, irow3805, rows3813]
  all_goals rfl

theorem atot3805 : totK PA10K2 A10K2.u3805 = [0, 0, 778583728134, 3057175204442, 3804646704251, 1693876109780, 221978937871, 5460492893, 0, 0] := by
  rw [show A10K2.u3805 = KTree.node A10K2.t3812 (nat_lit 61883539) (nat_lit 10954712508) (nat_lit 0) A10K2.t3813 from rfl, totK_node, tot3812, tot3813]
  decide +kernel

theorem arows3806 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3806 = true := by
  rw [show A10K2.u3806 = KTree.node A10K2.t3814 (nat_lit 61889320) (nat_lit 11255223256) (nat_lit 0) A10K2.t3815 from rfl, allE_node, rows3814, irow3806, rows3815]
  all_goals rfl

theorem atot3806 : totK PA10K2 A10K2.u3806 = [0, 0, 266424507814, 2059898468207, 4255238852892, 2618091976293, 360168927505, 6354482628, 0, 0] := by
  rw [show A10K2.u3806 = KTree.node A10K2.t3814 (nat_lit 61889320) (nat_lit 11255223256) (nat_lit 0) A10K2.t3815 from rfl, totK_node, tot3814, tot3815]
  decide +kernel

theorem arows3809 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3809 = true := by
  rw [show A10K2.u3809 = KTree.node A10K2.t3816 (nat_lit 61901597) (nat_lit 5993252933) (nat_lit 0) A10K2.t3817 from rfl, allE_node, rows3816, irow3809, rows3817]
  all_goals rfl

theorem atot3809 : totK PA10K2 A10K2.u3809 = [0, 0, 0, 1041686025554, 3806066453208, 3747072167581, 816704902567, 56933001426, 0, 0] := by
  rw [show A10K2.u3809 = KTree.node A10K2.t3816 (nat_lit 61901597) (nat_lit 5993252933) (nat_lit 0) A10K2.t3817 from rfl, totK_node, tot3816, tot3817]
  decide +kernel

theorem arows3810 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3810 = true := by
  rw [show A10K2.u3810 = KTree.node A10K2.t3818 (nat_lit 61919507) (nat_lit 5261955307) (nat_lit 0) A10K2.t3819 from rfl, allE_node, rows3818, irow3810, rows3819]
  all_goals rfl

theorem atot3810 : totK PA10K2 A10K2.u3810 = [0, 0, 0, 620320904108, 2888913948571, 4040984815294, 1616168519297, 198207399149, 5546304973, 0] := by
  rw [show A10K2.u3810 = KTree.node A10K2.t3818 (nat_lit 61919507) (nat_lit 5261955307) (nat_lit 0) A10K2.t3819 from rfl, totK_node, tot3818, tot3819]
  decide +kernel

theorem arows3812 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3812 = true := by
  rw [show A10K2.u3812 = KTree.node A10K2.t3820 (nat_lit 61941973) (nat_lit 6347289791) (nat_lit 0) A10K2.t3821 from rfl, allE_node, rows3820, irow3812, rows3821]
  all_goals rfl

theorem atot3812 : totK PA10K2 A10K2.u3812 = [0, 0, 814371176014, 3141407867331, 3966830622463, 1719479075366, 155614052559, 0, 0, 0] := by
  rw [show A10K2.u3812 = KTree.node A10K2.t3820 (nat_lit 61941973) (nat_lit 6347289791) (nat_lit 0) A10K2.t3821 from rfl, totK_node, tot3820, tot3821]
  decide +kernel

theorem arows3813 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3813 = true := by
  rw [show A10K2.u3813 = KTree.node A10K2.t3822 (nat_lit 61946934) (nat_lit 15475085972) (nat_lit 0) A10K2.t3823 from rfl, allE_node, rows3822, irow3813, rows3823]
  all_goals rfl

theorem atot3813 : totK PA10K2 A10K2.u3813 = [0, 0, 482403941286, 2166289510896, 3645401722146, 2600551129792, 576576661921, 31768748853, 0, 0] := by
  rw [show A10K2.u3813 = KTree.node A10K2.t3822 (nat_lit 61946934) (nat_lit 15475085972) (nat_lit 0) A10K2.t3823 from rfl, totK_node, tot3822, tot3823]
  decide +kernel

theorem arows3817 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3817 = true := by
  rw [show A10K2.u3817 = KTree.node A10K2.t3824 (nat_lit 61952296) (nat_lit 12227163393) (nat_lit 0) A10K2.t3825 from rfl, allE_node, rows3824, irow3817, rows3825]
  all_goals rfl

theorem atot3817 : totK PA10K2 A10K2.u3817 = [0, 0, 410627361782, 2376584579283, 4186432429033, 2233906862007, 302022523840, 6354482628, 0, 0] := by
  rw [show A10K2.u3817 = KTree.node A10K2.t3824 (nat_lit 61952296) (nat_lit 12227163393) (nat_lit 0) A10K2.t3825 from rfl, totK_node, tot3824, tot3825]
  decide +kernel

theorem arows3818 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3818 = true := by
  rw [show A10K2.u3818 = KTree.node A10K2.t3826 (nat_lit 61961500) (nat_lit 11782292529) (nat_lit 0) A10K2.t3827 from rfl, allE_node, rows3826, irow3818, rows3827]
  all_goals rfl

theorem atot3818 : totK PA10K2 A10K2.u3818 = [0, 0, 390160844362, 2372374870216, 4326502926942, 2661113151923, 455633229406, 12926121504, 0, 0] := by
  rw [show A10K2.u3818 = KTree.node A10K2.t3826 (nat_lit 61961500) (nat_lit 11782292529) (nat_lit 0) A10K2.t3827 from rfl, totK_node, tot3826, tot3827]
  decide +kernel

theorem arows3820 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3820 = true := by
  rw [show A10K2.u3820 = KTree.node A10K2.t3828 (nat_lit 61975789) (nat_lit 5462238129) (nat_lit 0) A10K2.t3829 from rfl, allE_node, rows3828, irow3820, rows3829]
  all_goals rfl

theorem atot3820 : totK PA10K2 A10K2.u3820 = [0, 0, 0, 542411564712, 2778205151402, 4046589339345, 1806011868890, 321115640737, 25130442608, 0] := by
  rw [show A10K2.u3820 = KTree.node A10K2.t3828 (nat_lit 61975789) (nat_lit 5462238129) (nat_lit 0) A10K2.t3829 from rfl, totK_node, tot3828, tot3829]
  decide +kernel

theorem arows3821 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3821 = true := by
  rw [show A10K2.u3821 = KTree.node A10K2.t3830 (nat_lit 61981922) (nat_lit 14238202023) (nat_lit 0) A10K2.t3831 from rfl, allE_node, rows3830, irow3821, rows3831]
  all_goals rfl

theorem atot3821 : totK PA10K2 A10K2.u3821 = [0, 0, 0, 777042948740, 3150177811386, 3831300421559, 1508541422931, 195359092037, 5517381808, 0] := by
  rw [show A10K2.u3821 = KTree.node A10K2.t3830 (nat_lit 61981922) (nat_lit 14238202023) (nat_lit 0) A10K2.t3831 from rfl, totK_node, tot3830, tot3831]
  decide +kernel

theorem arows3824 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3824 = true := by
  rw [show A10K2.u3824 = KTree.node A10K2.t3832 (nat_lit 61987614) (nat_lit 4979111479) (nat_lit 0) A10K2.t3833 from rfl, allE_node, rows3832, irow3824, rows3833]
  all_goals rfl

theorem atot3824 : totK PA10K2 A10K2.u3824 = [0, 0, 42649034548, 570543934099, 2620563308042, 4223708439529, 1972188826879, 246152103141, 6121173289, 0] := by
  rw [show A10K2.u3824 = KTree.node A10K2.t3832 (nat_lit 61987614) (nat_lit 4979111479) (nat_lit 0) A10K2.t3833 from rfl, totK_node, tot3832, tot3833]
  decide +kernel

theorem arows3825 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3825 = true := by
  rw [show A10K2.u3825 = KTree.node A10K2.t3834 (nat_lit 61999784) (nat_lit 8662782893) (nat_lit 0) A10K2.t3835 from rfl, allE_node, rows3834, irow3825, rows3835]
  all_goals rfl

theorem atot3825 : totK PA10K2 A10K2.u3825 = [0, 0, 639623211765, 2739591779398, 3665467578883, 1759849622184, 315138672054, 25371180993, 0, 0] := by
  rw [show A10K2.u3825 = KTree.node A10K2.t3834 (nat_lit 61999784) (nat_lit 8662782893) (nat_lit 0) A10K2.t3835 from rfl, totK_node, tot3834, tot3835]
  decide +kernel

theorem arows3827 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3827 = true := by
  rw [show A10K2.u3827 = KTree.node A10K2.t3836 (nat_lit 62006935) (nat_lit 13156212986) (nat_lit 0) A10K2.t3837 from rfl, allE_node, rows3836, irow3827, rows3837]
  all_goals rfl

theorem atot3827 : totK PA10K2 A10K2.u3827 = [0, 0, 745920107432, 2997043322418, 3876128378676, 1700227927398, 209884934324, 5460492893, 0, 0] := by
  rw [show A10K2.u3827 = KTree.node A10K2.t3836 (nat_lit 62006935) (nat_lit 13156212986) (nat_lit 0) A10K2.t3837 from rfl, totK_node, tot3836, tot3837]
  decide +kernel

theorem arows3828 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3828 = true := by
  rw [show A10K2.u3828 = KTree.node A10K2.t3838 (nat_lit 62011678) (nat_lit 9755146076) (nat_lit 0) A10K2.t3839 from rfl, allE_node, rows3838, irow3828, rows3839]
  all_goals rfl

theorem atot3828 : totK PA10K2 A10K2.u3828 = [0, 0, 266026540485, 1793969053896, 3893297049538, 2903215368705, 568408327072, 31768748853, 0, 0] := by
  rw [show A10K2.u3828 = KTree.node A10K2.t3838 (nat_lit 62011678) (nat_lit 9755146076) (nat_lit 0) A10K2.t3839 from rfl, totK_node, tot3838, tot3839]
  decide +kernel

theorem arows3836 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3836 = true := by
  rw [show A10K2.u3836 = KTree.node A10K2.t3840 (nat_lit 62016056) (nat_lit 13026764199) (nat_lit 0) A10K2.t3841 from rfl, allE_node, rows3840, irow3836, rows3841]
  all_goals rfl

theorem atot3836 : totK PA10K2 A10K2.u3836 = [0, 0, 582523478866, 2883143759531, 4187629883546, 1703926878291, 140464755192, 0, 0, 0] := by
  rw [show A10K2.u3836 = KTree.node A10K2.t3840 (nat_lit 62016056) (nat_lit 13026764199) (nat_lit 0) A10K2.t3841 from rfl, totK_node, tot3840, tot3841]
  decide +kernel

theorem arows3837 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3837 = true := by
  rw [show A10K2.u3837 = KTree.node A10K2.t3842 (nat_lit 62031943) (nat_lit 10219177915) (nat_lit 0) A10K2.t3843 from rfl, allE_node, rows3842, irow3837, rows3843]
  all_goals rfl

theorem atot3837 : totK PA10K2 A10K2.u3837 = [0, 0, 0, 1097610011461, 3848332183168, 3584017278302, 750392782629, 38342359577, 0, 0] := by
  rw [show A10K2.u3837 = KTree.node A10K2.t3842 (nat_lit 62031943) (nat_lit 10219177915) (nat_lit 0) A10K2.t3843 from rfl, totK_node, tot3842, tot3843]
  decide +kernel

theorem arows3839 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3839 = true := by
  rw [show A10K2.u3839 = KTree.node A10K2.t3844 (nat_lit 62041566) (nat_lit 13403863362) (nat_lit 0) A10K2.t3845 from rfl, allE_node, rows3844, irow3839, rows3845]
  all_goals rfl

theorem atot3839 : totK PA10K2 A10K2.u3839 = [0, 0, 0, 986622330448, 3625160062180, 3822107120968, 973885018965, 63640705285, 0, 0] := by
  rw [show A10K2.u3839 = KTree.node A10K2.t3844 (nat_lit 62041566) (nat_lit 13403863362) (nat_lit 0) A10K2.t3845 from rfl, totK_node, tot3844, tot3845]
  decide +kernel

theorem arows3840 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3840 = true := by
  rw [show A10K2.u3840 = KTree.node A10K2.t3846 (nat_lit 62050600) (nat_lit 12309375425) (nat_lit 0) A10K2.t3847 from rfl, allE_node, rows3846, irow3840, rows3847]
  all_goals rfl

theorem atot3840 : totK PA10K2 A10K2.u3840 = [0, 0, 0, 424844537572, 2478912618692, 4145138261559, 1970057203714, 291306829918, 6354482628, 0] := by
  rw [show A10K2.u3840 = KTree.node A10K2.t3846 (nat_lit 62050600) (nat_lit 12309375425) (nat_lit 0) A10K2.t3847 from rfl, totK_node, tot3846, tot3847]
  decide +kernel

theorem arows3843 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3843 = true := by
  rw [show A10K2.u3843 = KTree.node A10K2.t3848 (nat_lit 62131045) (nat_lit 7244901681) (nat_lit 0) A10K2.t3849 from rfl, allE_node, rows3848, irow3843, rows3849]
  all_goals rfl

theorem atot3843 : totK PA10K2 A10K2.u3843 = [0, 0, 0, 642413742979, 3049713458612, 4249190478126, 1458963821666, 127147938916, 0, 0] := by
  rw [show A10K2.u3843 = KTree.node A10K2.t3848 (nat_lit 62131045) (nat_lit 7244901681) (nat_lit 0) A10K2.t3849 from rfl, totK_node, tot3848, tot3849]
  decide +kernel

theorem arows3844 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3844 = true := by
  rw [show A10K2.u3844 = KTree.node A10K2.t3850 (nat_lit 62146218) (nat_lit 12737349524) (nat_lit 0) A10K2.t3851 from rfl, allE_node, rows3850, irow3844, rows3851]
  all_goals rfl

theorem atot3844 : totK PA10K2 A10K2.u3844 = [0, 0, 0, 773650122319, 3256741047271, 3893875635382, 1337694435039, 161879066040, 5447185874, 0] := by
  rw [show A10K2.u3844 = KTree.node A10K2.t3850 (nat_lit 62146218) (nat_lit 12737349524) (nat_lit 0) A10K2.t3851 from rfl, totK_node, tot3850, tot3851]
  decide +kernel

theorem arows3846 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3846 = true := by
  rw [show A10K2.u3846 = KTree.node A10K2.t3852 (nat_lit 62153150) (nat_lit 16287430150) (nat_lit 0) A10K2.t3853 from rfl, allE_node, rows3852, irow3846, rows3853]
  all_goals rfl

theorem atot3846 : totK PA10K2 A10K2.u3846 = [0, 0, 0, 742337670262, 2988806592872, 3849199674955, 1689742212521, 229571284244, 6354482628, 0] := by
  rw [show A10K2.u3846 = KTree.node A10K2.t3852 (nat_lit 62153150) (nat_lit 16287430150) (nat_lit 0) A10K2.t3853 from rfl, totK_node, tot3852, tot3853]
  decide +kernel

theorem arows3847 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3847 = true := by
  rw [show A10K2.u3847 = KTree.node A10K2.t3854 (nat_lit 62207267) (nat_lit 10336289781) (nat_lit 0) A10K2.t3855 from rfl, allE_node, rows3854, irow3847, rows3855]
  all_goals rfl

theorem atot3847 : totK PA10K2 A10K2.u3847 = [0, 0, 0, 336967145562, 2147983498345, 4068930270071, 2446443179238, 470659330519, 31017511657, 0] := by
  rw [show A10K2.u3847 = KTree.node A10K2.t3854 (nat_lit 62207267) (nat_lit 10336289781) (nat_lit 0) A10K2.t3855 from rfl, totK_node, tot3854, tot3855]
  decide +kernel

theorem arows3851 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3851 = true := by
  rw [show A10K2.u3851 = KTree.node A10K2.t3856 (nat_lit 62211987) (nat_lit 10656896559) (nat_lit 0) A10K2.t3857 from rfl, allE_node, rows3856, irow3851, rows3857]
  all_goals rfl

theorem atot3851 : totK PA10K2 A10K2.u3851 = [0, 0, 0, 775529322910, 3308949312116, 4034271459761, 1266481606518, 76382261199, 0, 0] := by
  rw [show A10K2.u3851 = KTree.node A10K2.t3856 (nat_lit 62211987) (nat_lit 10656896559) (nat_lit 0) A10K2.t3857 from rfl, totK_node, tot3856, tot3857]
  decide +kernel

theorem arows3852 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3852 = true := by
  rw [show A10K2.u3852 = KTree.node A10K2.t3858 (nat_lit 62219953) (nat_lit 3396951000) (nat_lit 0) A10K2.t3859 from rfl, allE_node, rows3858, irow3852, rows3859]
  all_goals rfl

theorem atot3852 : totK PA10K2 A10K2.u3852 = [0, 0, 0, 783869932705, 3063779839289, 3901285592346, 1701007417930, 241086744865, 6354482628, 0] := by
  rw [show A10K2.u3852 = KTree.node A10K2.t3858 (nat_lit 62219953) (nat_lit 3396951000) (nat_lit 0) A10K2.t3859 from rfl, totK_node, tot3858, tot3859]
  decide +kernel

theorem arows3854 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3854 = true := by
  rw [show A10K2.u3854 = KTree.node A10K2.t3860 (nat_lit 62263365) (nat_lit 6037852959) (nat_lit 0) A10K2.t3861 from rfl, allE_node, rows3860, irow3854, rows3861]
  all_goals rfl

theorem atot3854 : totK PA10K2 A10K2.u3854 = [0, 0, 0, 625358084433, 2748815399490, 4027326008840, 1659225749410, 203820232313, 5460492893, 0] := by
  rw [show A10K2.u3854 = KTree.node A10K2.t3860 (nat_lit 62263365) (nat_lit 6037852959) (nat_lit 0) A10K2.t3861 from rfl, totK_node, tot3860, tot3861]
  decide +kernel

theorem arows3855 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3855 = true := by
  rw [show A10K2.u3855 = KTree.node A10K2.t3862 (nat_lit 62270641) (nat_lit 1527015484) (nat_lit 0) A10K2.t3863 from rfl, allE_node, rows3862, irow3855, rows3863]
  all_goals rfl

theorem atot3855 : totK PA10K2 A10K2.u3855 = [0, 0, 0, 531260772300, 2658480976798, 3922340611895, 1848195710252, 341080538297, 24969229125, 0] := by
  rw [show A10K2.u3855 = KTree.node A10K2.t3862 (nat_lit 62270641) (nat_lit 1527015484) (nat_lit 0) A10K2.t3863 from rfl, totK_node, tot3862, tot3863]
  decide +kernel

theorem arows3858 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3858 = true := by
  rw [show A10K2.u3858 = KTree.node A10K2.t3864 (nat_lit 62276528) (nat_lit 13762874895) (nat_lit 0) A10K2.t3865 from rfl, allE_node, rows3864, irow3858, rows3865]
  all_goals rfl

theorem atot3858 : totK PA10K2 A10K2.u3858 = [0, 0, 0, 840803844797, 3139694485396, 3683466574625, 1495234408845, 209429781068, 6034215561, 0] := by
  rw [show A10K2.u3858 = KTree.node A10K2.t3864 (nat_lit 62276528) (nat_lit 13762874895) (nat_lit 0) A10K2.t3865 from rfl, totK_node, tot3864, tot3865]
  decide +kernel

theorem arows3859 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3859 = true := by
  rw [show A10K2.u3859 = KTree.node A10K2.t3866 (nat_lit 62282018) (nat_lit 12980963644) (nat_lit 0) A10K2.t3867 from rfl, allE_node, rows3866, irow3859, rows3867]
  all_goals rfl

theorem atot3859 : totK PA10K2 A10K2.u3859 = [0, 0, 0, 0, 1540238442298, 4397415026983, 2767206842905, 460808609248, 11740475125, 0] := by
  rw [show A10K2.u3859 = KTree.node A10K2.t3866 (nat_lit 62282018) (nat_lit 12980963644) (nat_lit 0) A10K2.t3867 from rfl, totK_node, tot3866, tot3867]
  decide +kernel

theorem arows3861 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3861 = true := by
  rw [show A10K2.u3861 = KTree.node A10K2.t3868 (nat_lit 62302286) (nat_lit 2716174388) (nat_lit 2) A10K2.t3869 from rfl, allE_node, rows3868, irow3861, rows3869]
  all_goals rfl

theorem atot3861 : totK PA10K2 A10K2.u3861 = [0, 0, 0, 0, 1143663737547, 3969861561724, 3306636792936, 725530962483, 38045387652, 0] := by
  rw [show A10K2.u3861 = KTree.node A10K2.t3868 (nat_lit 62302286) (nat_lit 2716174388) (nat_lit 2) A10K2.t3869 from rfl, totK_node, tot3868, tot3869]
  decide +kernel

theorem arows3862 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3862 = true := by
  rw [show A10K2.u3862 = KTree.node A10K2.t3870 (nat_lit 62310968) (nat_lit 11518142261) (nat_lit 0) A10K2.t3871 from rfl, allE_node, rows3870, irow3862, rows3871]
  all_goals rfl

theorem atot3862 : totK PA10K2 A10K2.u3862 = [0, 0, 0, 0, 567348919079, 2870920507266, 3997902362156, 1500723376250, 118449278787, 0] := by
  rw [show A10K2.u3862 = KTree.node A10K2.t3870 (nat_lit 62310968) (nat_lit 11518142261) (nat_lit 0) A10K2.t3871 from rfl, totK_node, tot3870, tot3871]
  decide +kernel

theorem arows3867 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3867 = true := by
  rw [show A10K2.u3867 = KTree.node A10K2.t3872 (nat_lit 62916877) (nat_lit 5932359113) (nat_lit 0) A10K2.t3873 from rfl, allE_node, rows3872, irow3867, rows3873]
  all_goals rfl

theorem atot3867 : totK PA10K2 A10K2.u3867 = [0, 844719840339, 3200086546597, 3595172315064, 1166546530971, 81611642989, 229076674476, 429542201963, 142269073820, 6354482628] := by
  rw [show A10K2.u3867 = KTree.node A10K2.t3872 (nat_lit 62916877) (nat_lit 5932359113) (nat_lit 0) A10K2.t3873 from rfl, totK_node, tot3872, tot3873]
  decide +kernel

theorem arows3868 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3868 = true := by
  rw [show A10K2.u3868 = KTree.node A10K2.t3874 (nat_lit 62921735) (nat_lit 14080703769) (nat_lit 0) A10K2.t3875 from rfl, allE_node, rows3874, irow3868, rows3875]
  all_goals rfl

theorem atot3868 : totK PA10K2 A10K2.u3868 = [0, 394016424166, 2029100911239, 3828463529031, 2697097802528, 580868795725, 30831673886, 0, 0, 0] := by
  rw [show A10K2.u3868 = KTree.node A10K2.t3874 (nat_lit 62921735) (nat_lit 14080703769) (nat_lit 0) A10K2.t3875 from rfl, totK_node, tot3874, tot3875]
  decide +kernel

theorem arows3870 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3870 = true := by
  rw [show A10K2.u3870 = KTree.node A10K2.t3876 (nat_lit 62937604) (nat_lit 12660096259) (nat_lit 0) A10K2.t3877 from rfl, allE_node, rows3876, irow3870, rows3877]
  all_goals rfl

theorem atot3870 : totK PA10K2 A10K2.u3870 = [0, 653112340205, 2925254135984, 4069893019778, 1808927779790, 222922296556, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u3870 = KTree.node A10K2.t3876 (nat_lit 62937604) (nat_lit 12660096259) (nat_lit 0) A10K2.t3877 from rfl, totK_node, tot3876, tot3877]
  decide +kernel

theorem arows3871 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3871 = true := by
  rw [show A10K2.u3871 = KTree.node A10K2.t3878 (nat_lit 62943585) (nat_lit 9039014625) (nat_lit 0) A10K2.t3879 from rfl, allE_node, rows3878, irow3871, rows3879]
  all_goals rfl

theorem atot3871 : totK PA10K2 A10K2.u3871 = [0, 314008318368, 2103309445997, 4263397350941, 2933454740100, 532036350666, 13803657628, 0, 0, 0] := by
  rw [show A10K2.u3871 = KTree.node A10K2.t3878 (nat_lit 62943585) (nat_lit 9039014625) (nat_lit 0) A10K2.t3879 from rfl, totK_node, tot3878, tot3879]
  decide +kernel

theorem arows3874 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3874 = true := by
  rw [show A10K2.u3874 = KTree.node A10K2.t3880 (nat_lit 62948275) (nat_lit 6588031001) (nat_lit 0) A10K2.t3881 from rfl, allE_node, rows3880, irow3874, rows3881]
  all_goals rfl

theorem atot3874 : totK PA10K2 A10K2.u3874 = [0, 0, 843005255625, 3461799880784, 4069508885856, 1283864990948, 87129073139, 0, 0, 0] := by
  rw [show A10K2.u3874 = KTree.node A10K2.t3880 (nat_lit 62948275) (nat_lit 6588031001) (nat_lit 0) A10K2.t3881 from rfl, totK_node, tot3880, tot3881]
  decide +kernel

theorem arows3875 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3875 = true := by
  rw [show A10K2.u3875 = KTree.node A10K2.t3882 (nat_lit 62954246) (nat_lit 8239411080) (nat_lit 0) A10K2.t3883 from rfl, allE_node, rows3882, irow3875, rows3883]
  all_goals rfl

theorem atot3875 : totK PA10K2 A10K2.u3875 = [0, 0, 392076695813, 2027955717947, 3850745583693, 2634452509101, 563654900971, 30650496230, 0, 0] := by
  rw [show A10K2.u3875 = KTree.node A10K2.t3882 (nat_lit 62954246) (nat_lit 8239411080) (nat_lit 0) A10K2.t3883 from rfl, totK_node, tot3882, tot3883]
  decide +kernel

theorem arows3877 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3877 = true := by
  rw [show A10K2.u3877 = KTree.node A10K2.t3884 (nat_lit 62973076) (nat_lit 8524645898) (nat_lit 0) A10K2.t3885 from rfl, allE_node, rows3884, irow3877, rows3885]
  all_goals rfl

theorem atot3877 : totK PA10K2 A10K2.u3877 = [0, 0, 965304220865, 3743137508072, 4075099429208, 1123960621428, 57886759290, 0, 0, 0] := by
  rw [show A10K2.u3877 = KTree.node A10K2.t3884 (nat_lit 62973076) (nat_lit 8524645898) (nat_lit 0) A10K2.t3885 from rfl, totK_node, tot3884, tot3885]
  decide +kernel

theorem arows3878 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3878 = true := by
  rw [show A10K2.u3878 = KTree.node A10K2.t3886 (nat_lit 63114276) (nat_lit 10617444664) (nat_lit 0) A10K2.t3887 from rfl, allE_node, rows3886, irow3878, rows3887]
  all_goals rfl

theorem atot3878 : totK PA10K2 A10K2.u3878 = [0, 783941292525, 3168437833525, 4031226324101, 1673824848205, 235007545101, 26048048901, 0, 0, 0] := by
  rw [show A10K2.u3878 = KTree.node A10K2.t3886 (nat_lit 63114276) (nat_lit 10617444664) (nat_lit 0) A10K2.t3887 from rfl, totK_node, tot3886, tot3887]
  decide +kernel

theorem arows3882 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3882 = true := by
  rw [show A10K2.u3882 = KTree.node A10K2.t3888 (nat_lit 63120668) (nat_lit 11020654927) (nat_lit 0) A10K2.t3889 from rfl, allE_node, rows3888, irow3882, rows3889]
  all_goals rfl

theorem atot3882 : totK PA10K2 A10K2.u3882 = [0, 594570731468, 2637033704005, 4009191374169, 2299481765273, 436596744470, 25351274858, 0, 0, 0] := by
  rw [show A10K2.u3882 = KTree.node A10K2.t3888 (nat_lit 63120668) (nat_lit 11020654927) (nat_lit 0) A10K2.t3889 from rfl, totK_node, tot3888, tot3889]
  decide +kernel

theorem arows3883 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3883 = true := by
  rw [show A10K2.u3883 = KTree.node A10K2.t3890 (nat_lit 63135781) (nat_lit 6082593057) (nat_lit 0) A10K2.t3891 from rfl, allE_node, rows3890, irow3883, rows3891]
  all_goals rfl

theorem atot3883 : totK PA10K2 A10K2.u3883 = [0, 539000210498, 2534136185533, 4059998000668, 2423644755424, 437918418166, 13561316338, 0, 0, 0] := by
  rw [show A10K2.u3883 = KTree.node A10K2.t3890 (nat_lit 63135781) (nat_lit 6082593057) (nat_lit 0) A10K2.t3891 from rfl, totK_node, tot3890, tot3891]
  decide +kernel

theorem arows3885 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3885 = true := by
  rw [show A10K2.u3885 = KTree.node A10K2.t3892 (nat_lit 63140282) (nat_lit 12874240221) (nat_lit 0) A10K2.t3893 from rfl, allE_node, rows3892, irow3885, rows3893]
  all_goals rfl

theorem atot3885 : totK PA10K2 A10K2.u3885 = [0, 327737319032, 2050513669004, 4168817184773, 2943810024483, 539308667962, 13816090359, 0, 0, 0] := by
  rw [show A10K2.u3885 = KTree.node A10K2.t3892 (nat_lit 63140282) (nat_lit 12874240221) (nat_lit 0) A10K2.t3893 from rfl, totK_node, tot3892, tot3893]
  decide +kernel

theorem arows3886 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3886 = true := by
  rw [show A10K2.u3886 = KTree.node A10K2.t3894 (nat_lit 63144836) (nat_lit 8656229173) (nat_lit 0) A10K2.t3895 from rfl, allE_node, rows3894, irow3886, rows3895]
  all_goals rfl

theorem atot3886 : totK PA10K2 A10K2.u3886 = [0, 0, 829632506178, 3429963251174, 4129478549403, 1451576672668, 99161160271, 0, 0, 0] := by
  rw [show A10K2.u3886 = KTree.node A10K2.t3894 (nat_lit 63144836) (nat_lit 8656229173) (nat_lit 0) A10K2.t3895 from rfl, totK_node, tot3894, tot3895]
  decide +kernel

theorem arows3889 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3889 = true := by
  rw [show A10K2.u3889 = KTree.node A10K2.t3896 (nat_lit 63151552) (nat_lit 14949107468) (nat_lit 0) A10K2.t3897 from rfl, allE_node, rows3896, irow3889, rows3897]
  all_goals rfl

theorem atot3889 : totK PA10K2 A10K2.u3889 = [0, 0, 593535314503, 2736685048495, 4118091090453, 2175179608938, 325384223891, 6904928264, 0, 0] := by
  rw [show A10K2.u3889 = KTree.node A10K2.t3896 (nat_lit 63151552) (nat_lit 14949107468) (nat_lit 0) A10K2.t3897 from rfl, totK_node, tot3896, tot3897]
  decide +kernel

theorem arows3890 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3890 = true := by
  rw [show A10K2.u3890 = KTree.node A10K2.t3898 (nat_lit 63159708) (nat_lit 7732883750) (nat_lit 0) A10K2.t3899 from rfl, allE_node, rows3898, irow3890, rows3899]
  all_goals rfl

theorem atot3890 : totK PA10K2 A10K2.u3890 = [0, 0, 538702996020, 2642116693149, 4208145033474, 2318658700371, 297740868944, 7047025452, 0, 0] := by
  rw [show A10K2.u3890 = KTree.node A10K2.t3898 (nat_lit 63159708) (nat_lit 7732883750) (nat_lit 0) A10K2.t3899 from rfl, totK_node, tot3898, tot3899]
  decide +kernel

theorem arows3892 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3892 = true := by
  rw [show A10K2.u3892 = KTree.node A10K2.t3900 (nat_lit 63172869) (nat_lit 5826087035) (nat_lit 0) A10K2.t3901 from rfl, allE_node, rows3900, irow3892, rows3901]
  all_goals rfl

theorem atot3892 : totK PA10K2 A10K2.u3892 = [0, 0, 327234200007, 2084452423212, 4159028854057, 2821677695331, 468708732068, 12224107035, 0, 0] := by
  rw [show A10K2.u3892 = KTree.node A10K2.t3900 (nat_lit 63172869) (nat_lit 5826087035) (nat_lit 0) A10K2.t3901 from rfl, totK_node, tot3900, tot3901]
  decide +kernel

theorem arows3893 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3893 = true := by
  rw [show A10K2.u3893 = KTree.node A10K2.t3902 (nat_lit 63177335) (nat_lit 10207976009) (nat_lit 0) A10K2.t3903 from rfl, allE_node, rows3902, irow3893, rows3903]
  all_goals rfl

theorem atot3893 : totK PA10K2 A10K2.u3893 = [0, 0, 844719840339, 3022394319603, 3499839602149, 1805043712582, 543767549864, 48886019071, 0, 0] := by
  rw [show A10K2.u3893 = KTree.node A10K2.t3902 (nat_lit 63177335) (nat_lit 10207976009) (nat_lit 0) A10K2.t3903 from rfl, totK_node, tot3902, tot3903]
  decide +kernel

theorem arows3899 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3899 = true := by
  rw [show A10K2.u3899 = KTree.node A10K2.t3904 (nat_lit 63183072) (nat_lit 8763854771) (nat_lit 0) A10K2.t3905 from rfl, allE_node, rows3904, irow3899, rows3905]
  all_goals rfl

theorem atot3899 : totK PA10K2 A10K2.u3899 = [0, 0, 291919316456, 1881050300171, 3949260276835, 2851388672324, 585145896603, 30831673886, 0, 0] := by
  rw [show A10K2.u3899 = KTree.node A10K2.t3904 (nat_lit 63183072) (nat_lit 8763854771) (nat_lit 0) A10K2.t3905 from rfl, totK_node, tot3904, tot3905]
  decide +kernel

theorem arows3900 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3900 = true := by
  rw [show A10K2.u3900 = KTree.node A10K2.t3906 (nat_lit 63197641) (nat_lit 6774201097) (nat_lit 0) A10K2.t3907 from rfl, allE_node, rows3906, irow3900, rows3907]
  all_goals rfl

theorem atot3900 : totK PA10K2 A10K2.u3900 = [0, 0, 564367217884, 2693553264406, 4107752906846, 1914918398198, 240181399924, 5705019915, 0, 0] := by
  rw [show A10K2.u3900 = KTree.node A10K2.t3906 (nat_lit 63197641) (nat_lit 6774201097) (nat_lit 0) A10K2.t3907 from rfl, totK_node, tot3906, tot3907]
  decide +kernel

theorem arows3902 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3902 = true := by
  rw [show A10K2.u3902 = KTree.node A10K2.t3908 (nat_lit 63205257) (nat_lit 8298999920) (nat_lit 0) A10K2.t3909 from rfl, allE_node, rows3908, irow3902, rows3909]
  all_goals rfl

theorem atot3902 : totK PA10K2 A10K2.u3902 = [0, 0, 504850548399, 2595512961523, 4263459169121, 2448899840200, 354467577798, 6853348008, 0, 0] := by
  rw [show A10K2.u3902 = KTree.node A10K2.t3908 (nat_lit 63205257) (nat_lit 8298999920) (nat_lit 0) A10K2.t3909 from rfl, totK_node, tot3908, tot3909]
  decide +kernel

theorem arows3903 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3903 = true := by
  rw [show A10K2.u3903 = KTree.node A10K2.t3910 (nat_lit 63210280) (nat_lit 12266556858) (nat_lit 0) A10K2.t3911 from rfl, allE_node, rows3910, irow3903, rows3911]
  all_goals rfl

theorem atot3903 : totK PA10K2 A10K2.u3903 = [0, 0, 0, 1004541504187, 3707606464462, 3824316604588, 1084429487167, 66195545706, 0, 0] := by
  rw [show A10K2.u3903 = KTree.node A10K2.t3910 (nat_lit 63210280) (nat_lit 12266556858) (nat_lit 0) A10K2.t3911 from rfl, totK_node, tot3910, tot3911]
  decide +kernel

theorem arows3906 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3906 = true := by
  rw [show A10K2.u3906 = KTree.node A10K2.t3912 (nat_lit 63216758) (nat_lit 15781458070) (nat_lit 0) A10K2.t3913 from rfl, allE_node, rows3912, irow3906, rows3913]
  all_goals rfl

theorem atot3906 : totK PA10K2 A10K2.u3906 = [0, 0, 0, 553529002408, 2713544689170, 3985464687058, 1931189599586, 298210146331, 7903172220, 0] := by
  rw [show A10K2.u3906 = KTree.node A10K2.t3912 (nat_lit 63216758) (nat_lit 15781458070) (nat_lit 0) A10K2.t3913 from rfl, totK_node, tot3912, tot3913]
  decide +kernel

theorem arows3907 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3907 = true := by
  rw [show A10K2.u3907 = KTree.node A10K2.t3914 (nat_lit 63237297) (nat_lit 6742900167) (nat_lit 0) A10K2.t3915 from rfl, allE_node, rows3914, irow3907, rows3915]
  all_goals rfl

theorem atot3907 : totK PA10K2 A10K2.u3907 = [0, 0, 303693864090, 1794622400809, 3814856732317, 3207075226766, 775543227769, 48454395282, 0, 0] := by
  rw [show A10K2.u3907 = KTree.node A10K2.t3914 (nat_lit 63237297) (nat_lit 6742900167) (nat_lit 0) A10K2.t3915 from rfl, totK_node, tot3914, tot3915]
  decide +kernel

theorem arows3909 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3909 = true := by
  rw [show A10K2.u3909 = KTree.node A10K2.t3916 (nat_lit 63377393) (nat_lit 8038460607) (nat_lit 0) A10K2.t3917 from rfl, allE_node, rows3916, irow3909, rows3917]
  all_goals rfl

theorem atot3909 : totK PA10K2 A10K2.u3909 = [0, 0, 480247428435, 2567670161962, 4176106198779, 2293252104207, 386315456916, 13360781053, 0, 0] := by
  rw [show A10K2.u3909 = KTree.node A10K2.t3916 (nat_lit 63377393) (nat_lit 8038460607) (nat_lit 0) A10K2.t3917 from rfl, totK_node, tot3916, tot3917]
  decide +kernel

theorem arows3910 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3910 = true := by
  rw [show A10K2.u3910 = KTree.node A10K2.t3918 (nat_lit 63385080) (nat_lit 12886193038) (nat_lit 0) A10K2.t3919 from rfl, allE_node, rows3918, irow3910, rows3919]
  all_goals rfl

theorem atot3910 : totK PA10K2 A10K2.u3910 = [0, 0, 594293228886, 2737563523144, 4231644946300, 2296834216221, 331063836788, 7151180950, 0, 0] := by
  rw [show A10K2.u3910 = KTree.node A10K2.t3918 (nat_lit 63385080) (nat_lit 12886193038) (nat_lit 0) A10K2.t3919 from rfl, totK_node, tot3918, tot3919]
  decide +kernel

theorem arows3914 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3914 = true := by
  rw [show A10K2.u3914 = KTree.node A10K2.t3920 (nat_lit 63399570) (nat_lit 15830774048) (nat_lit 0) A10K2.t3921 from rfl, allE_node, rows3920, irow3914, rows3921]
  all_goals rfl

theorem atot3914 : totK PA10K2 A10K2.u3914 = [0, 0, 866737529530, 3413012854872, 4099592410202, 1494696674669, 120753675133, 0, 0, 0] := by
  rw [show A10K2.u3914 = KTree.node A10K2.t3920 (nat_lit 63399570) (nat_lit 15830774048) (nat_lit 0) A10K2.t3921 from rfl, totK_node, tot3920, tot3921]
  decide +kernel

theorem arows3915 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3915 = true := by
  rw [show A10K2.u3915 = KTree.node A10K2.t3922 (nat_lit 63405160) (nat_lit 11526962314) (nat_lit 0) A10K2.t3923 from rfl, allE_node, rows3922, irow3915, rows3923]
  all_goals rfl

theorem atot3915 : totK PA10K2 A10K2.u3915 = [0, 320479959089, 932003970308, 1417638741945, 3064497621612, 3284612148144, 959736076278, 62368562949, 0, 0] := by
  rw [show A10K2.u3915 = KTree.node A10K2.t3922 (nat_lit 63405160) (nat_lit 11526962314) (nat_lit 0) A10K2.t3923 from rfl, totK_node, tot3922, tot3923]
  decide +kernel

theorem arows3917 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3917 = true := by
  rw [show A10K2.u3917 = KTree.node A10K2.t3924 (nat_lit 63516108) (nat_lit 1834076528) (nat_lit 0) A10K2.t3925 from rfl, allE_node, rows3924, irow3917, rows3925]
  all_goals rfl

theorem atot3917 : totK PA10K2 A10K2.u3917 = [0, 541416715838, 2563682649328, 3974278998504, 2231120229166, 431873639993, 25734533292, 0, 0, 0] := by
  rw [show A10K2.u3917 = KTree.node A10K2.t3924 (nat_lit 63516108) (nat_lit 1834076528) (nat_lit 0) A10K2.t3925 from rfl, totK_node, tot3924, tot3925]
  decide +kernel

theorem arows3918 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3918 = true := by
  rw [show A10K2.u3918 = KTree.node A10K2.t3926 (nat_lit 63521964) (nat_lit 12833588919) (nat_lit 0) A10K2.t3927 from rfl, allE_node, rows3926, irow3918, rows3927]
  all_goals rfl

theorem atot3918 : totK PA10K2 A10K2.u3918 = [0, 643544332899, 2796979033380, 3928297942166, 1943677058908, 271601120988, 6034215561, 0, 0, 0] := by
  rw [show A10K2.u3918 = KTree.node A10K2.t3926 (nat_lit 63521964) (nat_lit 12833588919) (nat_lit 0) A10K2.t3927 from rfl, totK_node, tot3926, tot3927]
  decide +kernel

theorem arows3921 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3921 = true := by
  rw [show A10K2.u3921 = KTree.node A10K2.t3928 (nat_lit 63529016) (nat_lit 14622956965) (nat_lit 0) A10K2.t3929 from rfl, allE_node, rows3928, irow3921, rows3929]
  all_goals rfl

theorem atot3921 : totK PA10K2 A10K2.u3921 = [0, 573560921706, 2674727731353, 4149446700659, 2072081012395, 270150937868, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u3921 = KTree.node A10K2.t3928 (nat_lit 63529016) (nat_lit 14622956965) (nat_lit 0) A10K2.t3929 from rfl, totK_node, tot3928, tot3929]
  decide +kernel

theorem arows3922 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3922 = true := by
  rw [show A10K2.u3922 = KTree.node A10K2.t3930 (nat_lit 63534264) (nat_lit 10041355490) (nat_lit 0) A10K2.t3931 from rfl, allE_node, rows3930, irow3922, rows3931]
  all_goals rfl

theorem atot3922 : totK PA10K2 A10K2.u3922 = [0, 226651756384, 1736660299158, 4074511199145, 3343560602958, 754717881804, 25625358996, 0, 0, 0] := by
  rw [show A10K2.u3922 = KTree.node A10K2.t3930 (nat_lit 63534264) (nat_lit 10041355490) (nat_lit 0) A10K2.t3931 from rfl, totK_node, tot3930, tot3931]
  decide +kernel

theorem arows3924 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3924 = true := by
  rw [show A10K2.u3924 = KTree.node A10K2.t3932 (nat_lit 63547671) (nat_lit 8942793278) (nat_lit 0) A10K2.t3933 from rfl, allE_node, rows3932, irow3924, rows3933]
  all_goals rfl

theorem atot3924 : totK PA10K2 A10K2.u3924 = [0, 0, 860163598482, 3378459999603, 4023451985300, 1426940755446, 119800991885, 0, 0, 0] := by
  rw [show A10K2.u3924 = KTree.node A10K2.t3932 (nat_lit 63547671) (nat_lit 8942793278) (nat_lit 0) A10K2.t3933 from rfl, totK_node, tot3932, tot3933]
  decide +kernel

theorem arows3925 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3925 = true := by
  rw [show A10K2.u3925 = KTree.node A10K2.t3934 (nat_lit 63552568) (nat_lit 11392077209) (nat_lit 0) A10K2.t3935 from rfl, allE_node, rows3934, irow3925, rows3935]
  all_goals rfl

theorem atot3925 : totK PA10K2 A10K2.u3925 = [0, 0, 378602380011, 2090551683107, 3827073881040, 2580692272029, 553813035352, 31082886609, 0, 0] := by
  rw [show A10K2.u3925 = KTree.node A10K2.t3934 (nat_lit 63552568) (nat_lit 11392077209) (nat_lit 0) A10K2.t3935 from rfl, totK_node, tot3934, tot3935]
  decide +kernel

theorem arows3930 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3930 = true := by
  rw [show A10K2.u3930 = KTree.node A10K2.t3936 (nat_lit 63559831) (nat_lit 10595344951) (nat_lit 0) A10K2.t3937 from rfl, allE_node, rows3936, irow3930, rows3937]
  all_goals rfl

theorem atot3930 : totK PA10K2 A10K2.u3930 = [0, 0, 717494933729, 2919058852852, 3941341814230, 1727408726261, 210587355135, 6121173289, 0, 0] := by
  rw [show A10K2.u3930 = KTree.node A10K2.t3936 (nat_lit 63559831) (nat_lit 10595344951) (nat_lit 0) A10K2.t3937 from rfl, totK_node, tot3936, tot3937]
  decide +kernel

theorem arows3931 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3931 = true := by
  rw [show A10K2.u3931 = KTree.node A10K2.t3938 (nat_lit 63565786) (nat_lit 13282809488) (nat_lit 0) A10K2.t3939 from rfl, allE_node, rows3938, irow3931, rows3939]
  all_goals rfl

theorem atot3931 : totK PA10K2 A10K2.u3931 = [0, 575843650046, 2265811940329, 3399274945209, 2702156220286, 929358898587, 76351749596, 0, 0, 0] := by
  rw [show A10K2.u3931 = KTree.node A10K2.t3938 (nat_lit 63565786) (nat_lit 13282809488) (nat_lit 0) A10K2.t3939 from rfl, totK_node, tot3938, tot3939]
  decide +kernel

theorem arows3933 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3933 = true := by
  rw [show A10K2.u3933 = KTree.node A10K2.t3940 (nat_lit 63583917) (nat_lit 5897492707) (nat_lit 0) A10K2.t3941 from rfl, allE_node, rows3940, irow3933, rows3941]
  all_goals rfl

theorem atot3933 : totK PA10K2 A10K2.u3933 = [0, 295377831852, 1875052486062, 4076547487121, 3035110663313, 630757842383, 31768748853, 0, 0, 0] := by
  rw [show A10K2.u3933 = KTree.node A10K2.t3940 (nat_lit 63583917) (nat_lit 5897492707) (nat_lit 0) A10K2.t3941 from rfl, totK_node, tot3940, tot3941]
  decide +kernel

theorem arows3934 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3934 = true := by
  rw [show A10K2.u3934 = KTree.node A10K2.t3942 (nat_lit 63588524) (nat_lit 13164463702) (nat_lit 0) A10K2.t3943 from rfl, allE_node, rows3942, irow3934, rows3943]
  all_goals rfl

theorem atot3934 : totK PA10K2 A10K2.u3934 = [0, 667350964308, 3149122391566, 4156594299441, 1486643821620, 89709409842, 0, 0, 0, 0] := by
  rw [show A10K2.u3934 = KTree.node A10K2.t3942 (nat_lit 63588524) (nat_lit 13164463702) (nat_lit 0) A10K2.t3943 from rfl, totK_node, tot3942, tot3943]
  decide +kernel

theorem arows3937 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3937 = true := by
  rw [show A10K2.u3937 = KTree.node A10K2.t3944 (nat_lit 63612829) (nat_lit 5046377985) (nat_lit 0) A10K2.t3945 from rfl, allE_node, rows3944, irow3937, rows3945]
  all_goals rfl

theorem atot3937 : totK PA10K2 A10K2.u3937 = [0, 0, 1041638141898, 3851767701092, 3875142902001, 959698678918, 45698759736, 0, 0, 0] := by
  rw [show A10K2.u3937 = KTree.node A10K2.t3944 (nat_lit 63612829) (nat_lit 5046377985) (nat_lit 0) A10K2.t3945 from rfl, totK_node, tot3944, tot3945]
  decide +kernel

theorem arows3938 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3938 = true := by
  rw [show A10K2.u3938 = KTree.node A10K2.t3946 (nat_lit 63621341) (nat_lit 5747407848) (nat_lit 0) A10K2.t3947 from rfl, allE_node, rows3946, irow3938, rows3947]
  all_goals rfl

theorem atot3938 : totK PA10K2 A10K2.u3938 = [0, 0, 663618996947, 3179185043483, 4144100436441, 1331714753016, 95528987695, 0, 0, 0] := by
  rw [show A10K2.u3938 = KTree.node A10K2.t3946 (nat_lit 63621341) (nat_lit 5747407848) (nat_lit 0) A10K2.t3947 from rfl, totK_node, tot3946, tot3947]
  decide +kernel

theorem arows3940 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3940 = true := by
  rw [show A10K2.u3940 = KTree.node A10K2.t3948 (nat_lit 63638935) (nat_lit 14565478140) (nat_lit 0) A10K2.t3949 from rfl, allE_node, rows3948, irow3940, rows3949]
  all_goals rfl

theorem atot3940 : totK PA10K2 A10K2.u3940 = [0, 556621861187, 2402551871681, 3521317265286, 2322127751604, 874241360692, 145541592289, 6354482628, 0, 0] := by
  rw [show A10K2.u3940 = KTree.node A10K2.t3948 (nat_lit 63638935) (nat_lit 14565478140) (nat_lit 0) A10K2.t3949 from rfl, totK_node, tot3948, tot3949]
  decide +kernel

theorem arows3941 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3941 = true := by
  rw [show A10K2.u3941 = KTree.node A10K2.t3950 (nat_lit 63645981) (nat_lit 6399411153) (nat_lit 0) A10K2.t3951 from rfl, allE_node, rows3950, irow3941, rows3951]
  all_goals rfl

theorem atot3941 : totK PA10K2 A10K2.u3941 = [0, 804252991483, 3266008697619, 4158086205363, 1694652235923, 151055876367, 0, 0, 0, 0] := by
  rw [show A10K2.u3941 = KTree.node A10K2.t3950 (nat_lit 63645981) (nat_lit 6399411153) (nat_lit 0) A10K2.t3951 from rfl, totK_node, tot3950, tot3951]
  decide +kernel

theorem arows3945 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3945 = true := by
  rw [show A10K2.u3945 = KTree.node A10K2.t3952 (nat_lit 63651044) (nat_lit 10715652115) (nat_lit 0) A10K2.t3953 from rfl, allE_node, rows3952, irow3945, rows3953]
  all_goals rfl

theorem atot3945 : totK PA10K2 A10K2.u3945 = [0, 534680748697, 2399233993035, 3830711542976, 2504389703866, 557548515157, 31747192500, 0, 0, 0] := by
  rw [show A10K2.u3945 = KTree.node A10K2.t3952 (nat_lit 63651044) (nat_lit 10715652115) (nat_lit 0) A10K2.t3953 from rfl, totK_node, tot3952, tot3953]
  decide +kernel

theorem arows3946 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3946 = true := by
  rw [show A10K2.u3946 = KTree.node A10K2.t3954 (nat_lit 63664177) (nat_lit 9972015927) (nat_lit 0) A10K2.t3955 from rfl, allE_node, rows3954, irow3946, rows3955]
  all_goals rfl

theorem atot3946 : totK PA10K2 A10K2.u3946 = [0, 327742824672, 2081454571417, 4141045905117, 2840265258225, 540880299128, 13816090359, 0, 0, 0] := by
  rw [show A10K2.u3946 = KTree.node A10K2.t3954 (nat_lit 63664177) (nat_lit 9972015927) (nat_lit 0) A10K2.t3955 from rfl, totK_node, tot3954, tot3955]
  decide +kernel

theorem arows3948 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3948 = true := by
  rw [show A10K2.u3948 = KTree.node A10K2.t3956 (nat_lit 63668806) (nat_lit 13407237131) (nat_lit 0) A10K2.t3957 from rfl, allE_node, rows3956, irow3948, rows3957]
  all_goals rfl

theorem atot3948 : totK PA10K2 A10K2.u3948 = [0, 0, 782335794845, 3304019531302, 4196736862165, 1583394033004, 126530100289, 0, 0, 0] := by
  rw [show A10K2.u3948 = KTree.node A10K2.t3956 (nat_lit 63668806) (nat_lit 13407237131) (nat_lit 0) A10K2.t3957 from rfl, totK_node, tot3956, tot3957]
  decide +kernel

theorem arows3949 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3949 = true := by
  rw [show A10K2.u3949 = KTree.node A10K2.t3958 (nat_lit 63678164) (nat_lit 11124460334) (nat_lit 0) A10K2.t3959 from rfl, allE_node, rows3958, irow3949, rows3959]
  all_goals rfl

theorem atot3949 : totK PA10K2 A10K2.u3949 = [0, 0, 804109052366, 3089698865791, 3941323969542, 1865650185667, 255651609373, 6904928264, 0, 0] := by
  rw [show A10K2.u3949 = KTree.node A10K2.t3958 (nat_lit 63678164) (nat_lit 11124460334) (nat_lit 0) A10K2.t3959 from rfl, totK_node, tot3958, tot3959]
  decide +kernel

theorem arows3952 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3952 = true := by
  rw [show A10K2.u3952 = KTree.node A10K2.t3960 (nat_lit 63683734) (nat_lit 15320969996) (nat_lit 0) A10K2.t3961 from rfl, allE_node, rows3960, irow3952, rows3961]
  all_goals rfl

theorem atot3952 : totK PA10K2 A10K2.u3952 = [0, 0, 534421757282, 2547205824765, 4081458363273, 2348534320512, 339755766583, 7047025452, 0, 0] := by
  rw [show A10K2.u3952 = KTree.node A10K2.t3960 (nat_lit 63683734) (nat_lit 15320969996) (nat_lit 0) A10K2.t3961 from rfl, totK_node, tot3960, tot3961]
  decide +kernel

theorem arows3953 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3953 = true := by
  rw [show A10K2.u3953 = KTree.node A10K2.t3962 (nat_lit 63696886) (nat_lit 16720836805) (nat_lit 0) A10K2.t3963 from rfl, allE_node, rows3962, irow3953, rows3963]
  all_goals rfl

theorem atot3953 : totK PA10K2 A10K2.u3953 = [0, 0, 327291078893, 2151091832102, 4217889406885, 2742426256402, 458422273245, 12224107035, 0, 0] := by
  rw [show A10K2.u3953 = KTree.node A10K2.t3962 (nat_lit 63696886) (nat_lit 16720836805) (nat_lit 0) A10K2.t3963 from rfl, totK_node, tot3962, tot3963]
  decide +kernel

theorem arows3955 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3955 = true := by
  rw [show A10K2.u3955 = KTree.node A10K2.t3964 (nat_lit 63776241) (nat_lit 6437539052) (nat_lit 0) A10K2.t3965 from rfl, allE_node, rows3964, irow3955, rows3965]
  all_goals rfl

theorem atot3955 : totK PA10K2 A10K2.u3955 = [0, 0, 777239743593, 2862069361817, 3539578632602, 1959202521542, 554875769323, 48886019071, 0, 0] := by
  rw [show A10K2.u3955 = KTree.node A10K2.t3964 (nat_lit 63776241) (nat_lit 6437539052) (nat_lit 0) A10K2.t3965 from rfl, totK_node, tot3964, tot3965]
  decide +kernel

theorem arows3956 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3956 = true := by
  rw [show A10K2.u3956 = KTree.node A10K2.t3966 (nat_lit 63780742) (nat_lit 14194853467) (nat_lit 0) A10K2.t3967 from rfl, allE_node, rows3966, irow3956, rows3967]
  all_goals rfl

theorem atot3956 : totK PA10K2 A10K2.u3956 = [0, 0, 169891412952, 1712936475206, 4128961925664, 3054559365475, 620333913995, 31768748853, 0, 0] := by
  rw [show A10K2.u3956 = KTree.node A10K2.t3966 (nat_lit 63780742) (nat_lit 14194853467) (nat_lit 0) A10K2.t3967 from rfl, totK_node, tot3966, tot3967]
  decide +kernel

theorem arows3963 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3963 = true := by
  rw [show A10K2.u3963 = KTree.node A10K2.t3968 (nat_lit 63785654) (nat_lit 11798772447) (nat_lit 0) A10K2.t3969 from rfl, allE_node, rows3968, irow3963, rows3969]
  all_goals rfl

theorem atot3963 : totK PA10K2 A10K2.u3963 = [0, 0, 557822838406, 2671283451838, 4069740692228, 1947319437599, 223282082586, 0, 0, 0] := by
  rw [show A10K2.u3963 = KTree.node A10K2.t3968 (nat_lit 63785654) (nat_lit 11798772447) (nat_lit 0) A10K2.t3969 from rfl, totK_node, tot3968, tot3969]
  decide +kernel

theorem arows3964 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3964 = true := by
  rw [show A10K2.u3964 = KTree.node A10K2.t3970 (nat_lit 63794244) (nat_lit 4423213217) (nat_lit 0) A10K2.t3971 from rfl, allE_node, rows3970, irow3964, rows3971]
  all_goals rfl

theorem atot3964 : totK PA10K2 A10K2.u3964 = [0, 0, 798744457886, 3236283474854, 4216599946971, 1770624660794, 175145100201, 6239673734, 0, 0] := by
  rw [show A10K2.u3964 = KTree.node A10K2.t3970 (nat_lit 63794244) (nat_lit 4423213217) (nat_lit 0) A10K2.t3971 from rfl, totK_node, tot3970, tot3971]
  decide +kernel

theorem arows3966 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3966 = true := by
  rw [show A10K2.u3966 = KTree.node A10K2.t3972 (nat_lit 63799191) (nat_lit 14550483610) (nat_lit 0) A10K2.t3973 from rfl, allE_node, rows3972, irow3966, rows3973]
  all_goals rfl

theorem atot3966 : totK PA10K2 A10K2.u3966 = [0, 0, 0, 1058694906671, 3737262416053, 3821903340751, 1102189639790, 67541609336, 0, 0] := by
  rw [show A10K2.u3966 = KTree.node A10K2.t3972 (nat_lit 63799191) (nat_lit 14550483610) (nat_lit 0) A10K2.t3973 from rfl, totK_node, tot3972, tot3973]
  decide +kernel

theorem arows3967 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3967 = true := by
  rw [show A10K2.u3967 = KTree.node A10K2.t3974 (nat_lit 63812968) (nat_lit 6570937036) (nat_lit 0) A10K2.t3975 from rfl, allE_node, rows3974, irow3967, rows3975]
  all_goals rfl

theorem atot3967 : totK PA10K2 A10K2.u3967 = [0, 0, 0, 287020209470, 2047446588106, 3968415820325, 2569968372981, 538143242785, 31018567651, 0] := by
  rw [show A10K2.u3967 = KTree.node A10K2.t3974 (nat_lit 63812968) (nat_lit 6570937036) (nat_lit 0) A10K2.t3975 from rfl, totK_node, tot3974, tot3975]
  decide +kernel

theorem arows3970 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3970 = true := by
  rw [show A10K2.u3970 = KTree.node A10K2.t3976 (nat_lit 63817911) (nat_lit 9745277275) (nat_lit 0) A10K2.t3977 from rfl, allE_node, rows3976, irow3970, rows3977]
  all_goals rfl

theorem atot3970 : totK PA10K2 A10K2.u3970 = [0, 0, 0, 637309194527, 2998344047767, 4107665970731, 1515556116950, 126544929179, 0, 0] := by
  rw [show A10K2.u3970 = KTree.node A10K2.t3976 (nat_lit 63817911) (nat_lit 9745277275) (nat_lit 0) A10K2.t3977 from rfl, totK_node, tot3976, tot3977]
  decide +kernel

theorem arows3971 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3971 = true := by
  rw [show A10K2.u3971 = KTree.node A10K2.t3978 (nat_lit 63826992) (nat_lit 13983522786) (nat_lit 0) A10K2.t3979 from rfl, allE_node, rows3978, irow3971, rows3979]
  all_goals rfl

theorem atot3971 : totK PA10K2 A10K2.u3971 = [0, 0, 308899695994, 1735293931668, 3400686479253, 3098814622354, 1243958094695, 179856586273, 5685526223, 0] := by
  rw [show A10K2.u3971 = KTree.node A10K2.t3978 (nat_lit 63826992) (nat_lit 13983522786) (nat_lit 0) A10K2.t3979 from rfl, totK_node, tot3978, tot3979]
  decide +kernel

theorem arows3973 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3973 = true := by
  rw [show A10K2.u3973 = KTree.node A10K2.t3980 (nat_lit 63844051) (nat_lit 10602640485) (nat_lit 0) A10K2.t3981 from rfl, allE_node, rows3980, irow3973, rows3981]
  all_goals rfl

theorem atot3973 : totK PA10K2 A10K2.u3973 = [0, 0, 487128049630, 2542938502484, 4078711609383, 2255351218482, 429088077119, 25734533292, 0, 0] := by
  rw [show A10K2.u3973 = KTree.node A10K2.t3980 (nat_lit 63844051) (nat_lit 10602640485) (nat_lit 0) A10K2.t3981 from rfl, totK_node, tot3980, tot3981]
  decide +kernel

theorem arows3974 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3974 = true := by
  rw [show A10K2.u3974 = KTree.node A10K2.t3982 (nat_lit 63849793) (nat_lit 9109876184) (nat_lit 0) A10K2.t3983 from rfl, allE_node, rows3982, irow3974, rows3983]
  all_goals rfl

theorem atot3974 : totK PA10K2 A10K2.u3974 = [0, 0, 742077765612, 2982534119776, 3905408266744, 1770146681885, 225371086403, 6034215561, 0, 0] := by
  rw [show A10K2.u3974 = KTree.node A10K2.t3982 (nat_lit 63849793) (nat_lit 9109876184) (nat_lit 0) A10K2.t3983 from rfl, totK_node, tot3982, tot3983]
  decide +kernel

theorem arows3978 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3978 = true := by
  rw [show A10K2.u3978 = KTree.node A10K2.t3984 (nat_lit 63874234) (nat_lit 15100844572) (nat_lit 0) A10K2.t3985 from rfl, allE_node, rows3984, irow3978, rows3985]
  all_goals rfl

theorem atot3978 : totK PA10K2 A10K2.u3978 = [0, 0, 0, 1238061333949, 4101557370451, 3440194400041, 671787432127, 32470817489, 0, 0] := by
  rw [show A10K2.u3978 = KTree.node A10K2.t3984 (nat_lit 63874234) (nat_lit 15100844572) (nat_lit 0) A10K2.t3985 from rfl, totK_node, tot3984, tot3985]
  decide +kernel

theorem arows3979 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3979 = true := by
  rw [show A10K2.u3979 = KTree.node A10K2.t3986 (nat_lit 63882650) (nat_lit 14610255845) (nat_lit 0) A10K2.t3987 from rfl, allE_node, rows3986, irow3979, rows3987]
  all_goals rfl

theorem atot3979 : totK PA10K2 A10K2.u3979 = [0, 0, 0, 957998340937, 3634398996783, 3939506819783, 1014042036139, 50422943179, 0, 0] := by
  rw [show A10K2.u3979 = KTree.node A10K2.t3986 (nat_lit 63882650) (nat_lit 14610255845) (nat_lit 0) A10K2.t3987 from rfl, totK_node, tot3986, tot3987]
  decide +kernel

theorem arows3981 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3981 = true := by
  rw [show A10K2.u3981 = KTree.node A10K2.t3988 (nat_lit 63898056) (nat_lit 14209543142) (nat_lit 0) A10K2.t3989 from rfl, allE_node, rows3988, irow3981, rows3989]
  all_goals rfl

theorem atot3981 : totK PA10K2 A10K2.u3981 = [0, 0, 556621861187, 2152663042839, 3086294240260, 2540901803874, 1165204404964, 189164816705, 6239673734, 0] := by
  rw [show A10K2.u3981 = KTree.node A10K2.t3988 (nat_lit 63898056) (nat_lit 14209543142) (nat_lit 0) A10K2.t3989 from rfl, totK_node, tot3988, tot3989]
  decide +kernel

theorem arows3982 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3982 = true := by
  rw [show A10K2.u3982 = KTree.node A10K2.t3990 (nat_lit 63907314) (nat_lit 14298392437) (nat_lit 0) A10K2.t3991 from rfl, allE_node, rows3990, irow3982, rows3991]
  all_goals rfl

theorem atot3982 : totK PA10K2 A10K2.u3982 = [0, 0, 803762330463, 3124373328156, 3949536681194, 1843468782155, 246206288515, 7007974415, 0, 0] := by
  rw [show A10K2.u3982 = KTree.node A10K2.t3990 (nat_lit 63907314) (nat_lit 14298392437) (nat_lit 0) A10K2.t3991 from rfl, totK_node, tot3990, tot3991]
  decide +kernel

theorem arows3985 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3985 = true := by
  rw [show A10K2.u3985 = KTree.node A10K2.t3992 (nat_lit 63912158) (nat_lit 10648075800) (nat_lit 0) A10K2.t3993 from rfl, allE_node, rows3992, irow3985, rows3993]
  all_goals rfl

theorem atot3985 : totK PA10K2 A10K2.u3985 = [0, 0, 246819733237, 1833633735156, 4068334989647, 3013205522157, 622625467582, 31285368086, 0, 0] := by
  rw [show A10K2.u3985 = KTree.node A10K2.t3992 (nat_lit 63912158) (nat_lit 10648075800) (nat_lit 0) A10K2.t3993 from rfl, totK_node, tot3992, tot3993]
  decide +kernel

theorem arows3986 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3986 = true := by
  rw [show A10K2.u3986 = KTree.node A10K2.t3994 (nat_lit 63925719) (nat_lit 14430147840) (nat_lit 0) A10K2.t3995 from rfl, allE_node, rows3994, irow3986, rows3995]
  all_goals rfl

theorem atot3986 : totK PA10K2 A10K2.u3986 = [0, 0, 615112866711, 2799939734094, 4124771545383, 2127148925500, 292908645599, 6281495166, 0, 0] := by
  rw [show A10K2.u3986 = KTree.node A10K2.t3994 (nat_lit 63925719) (nat_lit 14430147840) (nat_lit 0) A10K2.t3995 from rfl, totK_node, tot3994, tot3995]
  decide +kernel

theorem arows3988 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3988 = true := by
  rw [show A10K2.u3988 = KTree.node A10K2.t3996 (nat_lit 63930309) (nat_lit 2063918848) (nat_lit 0) A10K2.t3997 from rfl, allE_node, rows3996, irow3988, rows3997]
  all_goals rfl

theorem atot3988 : totK PA10K2 A10K2.u3988 = [0, 480657707117, 1746481795039, 2224785566270, 2329176252293, 2253940076169, 755682338874, 56100664475, 0, 0] := by
  rw [show A10K2.u3988 = KTree.node A10K2.t3996 (nat_lit 63930309) (nat_lit 2063918848) (nat_lit 0) A10K2.t3997 from rfl, totK_node, tot3996, tot3997]
  decide +kernel

theorem arows3989 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3989 = true := by
  rw [show A10K2.u3989 = KTree.node A10K2.t3998 (nat_lit 64492031) (nat_lit 10271769328) (nat_lit 0) A10K2.t3999 from rfl, allE_node, rows3998, irow3989, rows3999]
  all_goals rfl

theorem atot3989 : totK PA10K2 A10K2.u3989 = [0, 407084578226, 2138381334751, 4044090166231, 2753715266293, 519570796569, 25371180993, 0, 0, 0] := by
  rw [show A10K2.u3989 = KTree.node A10K2.t3998 (nat_lit 64492031) (nat_lit 10271769328) (nat_lit 0) A10K2.t3999 from rfl, totK_node, tot3998, tot3999]
  decide +kernel

theorem arows3994 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3994 = true := by
  rw [show A10K2.u3994 = KTree.node A10K2.t4000 (nat_lit 64512506) (nat_lit 12395036344) (nat_lit 0) A10K2.t4001 from rfl, allE_node, rows4000, irow3994, rows4001]
  all_goals rfl

theorem atot3994 : totK PA10K2 A10K2.u3994 = [0, 982976898703, 3633983726582, 4021007093706, 1297021804351, 91570608165, 0, 0, 0, 0] := by
  rw [show A10K2.u3994 = KTree.node A10K2.t4000 (nat_lit 64512506) (nat_lit 12395036344) (nat_lit 0) A10K2.t4001 from rfl, totK_node, tot4000, tot4001]
  decide +kernel

theorem arows3995 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3995 = true := by
  rw [show A10K2.u3995 = KTree.node A10K2.t4002 (nat_lit 64517349) (nat_lit 4657515076) (nat_lit 0) A10K2.t4003 from rfl, allE_node, rows4002, irow3995, rows4003]
  all_goals rfl

theorem atot3995 : totK PA10K2 A10K2.u3995 = [0, 0, 1233169976646, 3996862407936, 3858935878962, 1048603213174, 62979767238, 0, 0, 0] := by
  rw [show A10K2.u3995 = KTree.node A10K2.t4002 (nat_lit 64517349) (nat_lit 4657515076) (nat_lit 0) A10K2.t4003 from rfl, totK_node, tot4002, tot4003]
  decide +kernel

theorem arows3997 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3997 = true := by
  rw [show A10K2.u3997 = KTree.node A10K2.t4004 (nat_lit 64523342) (nat_lit 10937012839) (nat_lit 0) A10K2.t4005 from rfl, allE_node, rows4004, irow3997, rows4005]
  all_goals rfl

theorem atot3997 : totK PA10K2 A10K2.u3997 = [0, 0, 734427369600, 3087910910475, 3900850171121, 1644368585967, 275210478722, 13364899180, 0, 0] := by
  rw [show A10K2.u3997 = KTree.node A10K2.t4004 (nat_lit 64523342) (nat_lit 10937012839) (nat_lit 0) A10K2.t4005 from rfl, totK_node, tot4004, tot4005]
  decide +kernel

theorem arows3998 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3998 = true := by
  rw [show A10K2.u3998 = KTree.node A10K2.t4006 (nat_lit 64537137) (nat_lit 9952319228) (nat_lit 0) A10K2.t4007 from rfl, allE_node, rows4006, irow3998, rows4007]
  all_goals rfl

theorem atot3998 : totK PA10K2 A10K2.u3998 = [0, 0, 576474954975, 2747205774812, 4134244287180, 2022262998553, 246740487739, 0, 0, 0] := by
  rw [show A10K2.u3998 = KTree.node A10K2.t4006 (nat_lit 64537137) (nat_lit 9952319228) (nat_lit 0) A10K2.t4007 from rfl, totK_node, tot4006, tot4007]
  decide +kernel

theorem arows4001 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4001 = true := by
  rw [show A10K2.u4001 = KTree.node A10K2.t4008 (nat_lit 64548793) (nat_lit 6821941981) (nat_lit 0) A10K2.t4009 from rfl, allE_node, rows4008, irow4001, rows4009]
  all_goals rfl

theorem atot4001 : totK PA10K2 A10K2.u4001 = [0, 525241347744, 2285310416750, 3635878417679, 2724019369079, 807986020754, 57551169768, 0, 0, 0] := by
  rw [show A10K2.u4001 = KTree.node A10K2.t4008 (nat_lit 64548793) (nat_lit 6821941981) (nat_lit 0) A10K2.t4009 from rfl, totK_node, tot4008, tot4009]
  decide +kernel

theorem arows4002 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4002 = true := by
  rw [show A10K2.u4002 = KTree.node A10K2.t4010 (nat_lit 64566662) (nat_lit 14832189078) (nat_lit 0) A10K2.t4011 from rfl, allE_node, rows4010, irow4002, rows4011]
  all_goals rfl

theorem atot4002 : totK PA10K2 A10K2.u4002 = [0, 297779599935, 1982800109274, 4061971291105, 2859316338081, 593534580152, 31768748853, 0, 0, 0] := by
  rw [show A10K2.u4002 = KTree.node A10K2.t4010 (nat_lit 64566662) (nat_lit 14832189078) (nat_lit 0) A10K2.t4011 from rfl, totK_node, tot4010, tot4011]
  decide +kernel

theorem arows4004 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4004 = true := by
  rw [show A10K2.u4004 = KTree.node A10K2.t4012 (nat_lit 64572182) (nat_lit 8244030846) (nat_lit 0) A10K2.t4013 from rfl, allE_node, rows4012, irow4004, rows4013]
  all_goals rfl

theorem atot4004 : totK PA10K2 A10K2.u4004 = [0, 695950962705, 2933723986200, 4044135281526, 1902158135077, 251786613768, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u4004 = KTree.node A10K2.t4012 (nat_lit 64572182) (nat_lit 8244030846) (nat_lit 0) A10K2.t4013 from rfl, totK_node, tot4012, tot4013]
  decide +kernel

theorem arows4005 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4005 = true := by
  rw [show A10K2.u4005 = KTree.node A10K2.t4014 (nat_lit 64581040) (nat_lit 14090070165) (nat_lit 0) A10K2.t4015 from rfl, allE_node, rows4014, irow4005, rows4015]
  all_goals rfl

theorem atot4005 : totK PA10K2 A10K2.u4005 = [0, 614762885360, 2815895038623, 4183198041520, 2170015636673, 329020202887, 6851704726, 0, 0, 0] := by
  rw [show A10K2.u4005 = KTree.node A10K2.t4014 (nat_lit 64581040) (nat_lit 14090070165) (nat_lit 0) A10K2.t4015 from rfl, totK_node, tot4014, tot4015]
  decide +kernel

theorem arows4009 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4009 = true := by
  rw [show A10K2.u4009 = KTree.node A10K2.t4016 (nat_lit 64585685) (nat_lit 1963823179) (nat_lit 0) A10K2.t4017 from rfl, allE_node, rows4016, irow4009, rows4017]
  all_goals rfl

theorem atot4009 : totK PA10K2 A10K2.u4009 = [0, 0, 958698828852, 3650283096008, 3991206506790, 1208655868658, 82605879954, 0, 0, 0] := by
  rw [show A10K2.u4009 = KTree.node A10K2.t4016 (nat_lit 64585685) (nat_lit 1963823179) (nat_lit 0) A10K2.t4017 from rfl, totK_node, tot4016, tot4017]
  decide +kernel

theorem arows4010 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4010 = true := by
  rw [show A10K2.u4010 = KTree.node A10K2.t4018 (nat_lit 64599483) (nat_lit 7056582059) (nat_lit 0) A10K2.t4019 from rfl, allE_node, rows4018, irow4010, rows4019]
  all_goals rfl

theorem atot4010 : totK PA10K2 A10K2.u4010 = [0, 0, 296957029898, 1986289857499, 4040016890557, 2728019665401, 558840893770, 31082886609, 0, 0] := by
  rw [show A10K2.u4010 = KTree.node A10K2.t4018 (nat_lit 64599483) (nat_lit 7056582059) (nat_lit 0) A10K2.t4019 from rfl, totK_node, tot4018, tot4019]
  decide +kernel

theorem arows4012 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4012 = true := by
  rw [show A10K2.u4012 = KTree.node A10K2.t4020 (nat_lit 64607405) (nat_lit 6276761685) (nat_lit 0) A10K2.t4021 from rfl, allE_node, rows4020, irow4012, rows4021]
  all_goals rfl

theorem atot4012 : totK PA10K2 A10K2.u4012 = [0, 0, 695115401484, 3015125627317, 4043324017276, 1758580670039, 234775328044, 6121173289, 0, 0] := by
  rw [show A10K2.u4012 = KTree.node A10K2.t4020 (nat_lit 64607405) (nat_lit 6276761685) (nat_lit 0) A10K2.t4021 from rfl, totK_node, tot4020, tot4021]
  decide +kernel

theorem arows4013 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4013 = true := by
  rw [show A10K2.u4013 = KTree.node A10K2.t4022 (nat_lit 64613943) (nat_lit 14895522512) (nat_lit 0) A10K2.t4023 from rfl, allE_node, rows4022, irow4013, rows4023]
  all_goals rfl

theorem atot4013 : totK PA10K2 A10K2.u4013 = [0, 383428828220, 1883113259588, 3511352078016, 2984936644294, 978297768092, 76161461406, 0, 0, 0] := by
  rw [show A10K2.u4013 = KTree.node A10K2.t4022 (nat_lit 64613943) (nat_lit 14895522512) (nat_lit 0) A10K2.t4023 from rfl, totK_node, tot4022, tot4023]
  decide +kernel

theorem arows4016 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4016 = true := by
  rw [show A10K2.u4016 = KTree.node A10K2.t4024 (nat_lit 64688455) (nat_lit 6051473360) (nat_lit 0) A10K2.t4025 from rfl, allE_node, rows4024, irow4016, rows4025]
  all_goals rfl

theorem atot4016 : totK PA10K2 A10K2.u4016 = [0, 404278702795, 2204627274762, 4039120231811, 2603659785201, 481076634185, 18429085292, 0, 0, 0] := by
  rw [show A10K2.u4016 = KTree.node A10K2.t4024 (nat_lit 64688455) (nat_lit 6051473360) (nat_lit 0) A10K2.t4025 from rfl, totK_node, tot4024, tot4025]
  decide +kernel

theorem arows4017 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4017 = true := by
  rw [show A10K2.u4017 = KTree.node A10K2.t4026 (nat_lit 64695459) (nat_lit 10467782193) (nat_lit 0) A10K2.t4027 from rfl, allE_node, rows4026, irow4017, rows4027]
  all_goals rfl

theorem atot4017 : totK PA10K2 A10K2.u4017 = [0, 696064853925, 3038805364379, 4034722508013, 1827782280660, 273398380523, 15167097304, 0, 0, 0] := by
  rw [show A10K2.u4017 = KTree.node A10K2.t4026 (nat_lit 64695459) (nat_lit 10467782193) (nat_lit 0) A10K2.t4027 from rfl, totK_node, tot4026, tot4027]
  decide +kernel

theorem arows4019 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4019 = true := by
  rw [show A10K2.u4019 = KTree.node A10K2.t4028 (nat_lit 64709004) (nat_lit 8125911805) (nat_lit 0) A10K2.t4029 from rfl, allE_node, rows4028, irow4019, rows4029]
  all_goals rfl

theorem atot4019 : totK PA10K2 A10K2.u4019 = [0, 665346055962, 2746526908389, 3884176501439, 2151147194555, 372795627788, 16283799455, 0, 0, 0] := by
  rw [show A10K2.u4019 = KTree.node A10K2.t4028 (nat_lit 64709004) (nat_lit 8125911805) (nat_lit 0) A10K2.t4029 from rfl, totK_node, tot4028, tot4029]
  decide +kernel

theorem arows4020 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4020 = true := by
  rw [show A10K2.u4020 = KTree.node A10K2.t4030 (nat_lit 64713261) (nat_lit 4862654380) (nat_lit 0) A10K2.t4031 from rfl, allE_node, rows4030, irow4020, rows4031]
  all_goals rfl

theorem atot4020 : totK PA10K2 A10K2.u4020 = [0, 227979659980, 1896737106570, 4267406245214, 3096318114366, 558546492048, 13816090359, 0, 0, 0] := by
  rw [show A10K2.u4020 = KTree.node A10K2.t4030 (nat_lit 64713261) (nat_lit 4862654380) (nat_lit 0) A10K2.t4031 from rfl, totK_node, tot4030, tot4031]
  decide +kernel

theorem arows4026 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4026 = true := by
  rw [show A10K2.u4026 = KTree.node A10K2.t4032 (nat_lit 64718857) (nat_lit 9791040699) (nat_lit 0) A10K2.t4033 from rfl, allE_node, rows4032, irow4026, rows4033]
  all_goals rfl

theorem atot4026 : totK PA10K2 A10K2.u4026 = [0, 0, 724923113105, 3153220333677, 4156499023478, 1620123428187, 136859661949, 0, 0, 0] := by
  rw [show A10K2.u4026 = KTree.node A10K2.t4032 (nat_lit 64718857) (nat_lit 9791040699) (nat_lit 0) A10K2.t4033 from rfl, totK_node, tot4032, tot4033]
  decide +kernel

theorem arows4027 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4027 = true := by
  rw [show A10K2.u4027 = KTree.node A10K2.t4034 (nat_lit 64726257) (nat_lit 4836326203) (nat_lit 0) A10K2.t4035 from rfl, allE_node, rows4034, irow4027, rows4035]
  all_goals rfl

theorem atot4027 : totK PA10K2 A10K2.u4027 = [0, 0, 649617017525, 2785147688872, 3966369482151, 1965648640347, 269455097965, 6904928264, 0, 0] := by
  rw [show A10K2.u4027 = KTree.node A10K2.t4034 (nat_lit 64726257) (nat_lit 4836326203) (nat_lit 0) A10K2.t4035 from rfl, totK_node, tot4034, tot4035]
  decide +kernel

theorem arows4029 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4029 = true := by
  rw [show A10K2.u4029 = KTree.node A10K2.t4036 (nat_lit 64731064) (nat_lit 8095560237) (nat_lit 0) A10K2.t4037 from rfl, allE_node, rows4036, irow4029, rows4037]
  all_goals rfl

theorem atot4029 : totK PA10K2 A10K2.u4029 = [0, 0, 396975800664, 2392416758514, 4294680794057, 2468648928054, 345257431695, 7047025452, 0, 0] := by
  rw [show A10K2.u4029 = KTree.node A10K2.t4036 (nat_lit 64731064) (nat_lit 8095560237) (nat_lit 0) A10K2.t4037 from rfl, totK_node, tot4036, tot4037]
  decide +kernel

theorem arows4030 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4030 = true := by
  rw [show A10K2.u4030 = KTree.node A10K2.t4038 (nat_lit 64745023) (nat_lit 14145557035) (nat_lit 0) A10K2.t4039 from rfl, allE_node, rows4038, irow4030, rows4039]
  all_goals rfl

theorem atot4030 : totK PA10K2 A10K2.u4030 = [0, 0, 614163989865, 2777940814242, 4137204270688, 2126819606032, 268567049141, 6066958478, 0, 0] := by
  rw [show A10K2.u4030 = KTree.node A10K2.t4038 (nat_lit 64745023) (nat_lit 14145557035) (nat_lit 0) A10K2.t4039 from rfl, totK_node, tot4038, tot4039]
  decide +kernel

theorem arows4033 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4033 = true := by
  rw [show A10K2.u4033 = KTree.node A10K2.t4040 (nat_lit 64749608) (nat_lit 12863397079) (nat_lit 0) A10K2.t4041 from rfl, allE_node, rows4040, irow4033, rows4041]
  all_goals rfl

theorem atot4033 : totK PA10K2 A10K2.u4033 = [0, 0, 590157910828, 2363208085833, 3529843973211, 2518537207845, 738207838133, 55043167628, 0, 0] := by
  rw [show A10K2.u4033 = KTree.node A10K2.t4040 (nat_lit 64749608) (nat_lit 12863397079) (nat_lit 0) A10K2.t4041 from rfl, totK_node, tot4040, tot4041]
  decide +kernel

theorem arows4034 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4034 = true := by
  rw [show A10K2.u4034 = KTree.node A10K2.t4042 (nat_lit 64754441) (nat_lit 9729940307) (nat_lit 0) A10K2.t4043 from rfl, allE_node, rows4042, irow4034, rows4043]
  all_goals rfl

theorem atot4034 : totK PA10K2 A10K2.u4034 = [0, 0, 452541875273, 2236521895015, 4026508085309, 2681654743603, 472454580037, 13364899180, 0, 0] := by
  rw [show A10K2.u4034 = KTree.node A10K2.t4042 (nat_lit 64754441) (nat_lit 9729940307) (nat_lit 0) A10K2.t4043 from rfl, totK_node, tot4042, tot4043]
  decide +kernel

theorem arows4036 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4036 = true := by
  rw [show A10K2.u4036 = KTree.node A10K2.t4044 (nat_lit 64774954) (nat_lit 11933677) (nat_lit 0) A10K2.t4045 from rfl, allE_node, rows4044, irow4036, rows4045]
  all_goals rfl

theorem atot4036 : totK PA10K2 A10K2.u4036 = [0, 0, 826016771734, 3484004245084, 4292209674873, 1394078400539, 85366073640, 0, 0, 0] := by
  rw [show A10K2.u4036 = KTree.node A10K2.t4044 (nat_lit 64774954) (nat_lit 11933677) (nat_lit 0) A10K2.t4045 from rfl, totK_node, tot4044, tot4045]
  decide +kernel

theorem arows4037 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4037 = true := by
  rw [show A10K2.u4037 = KTree.node A10K2.t4046 (nat_lit 64779960) (nat_lit 9693615719) (nat_lit 0) A10K2.t4047 from rfl, allE_node, rows4046, irow4037, rows4047]
  all_goals rfl

theorem atot4037 : totK PA10K2 A10K2.u4037 = [0, 0, 0, 1140468774239, 3939680819695, 3876708964760, 1024914518325, 62351816811, 0, 0] := by
  rw [show A10K2.u4037 = KTree.node A10K2.t4046 (nat_lit 64779960) (nat_lit 9693615719) (nat_lit 0) A10K2.t4047 from rfl, totK_node, tot4046, tot4047]
  decide +kernel

theorem arows4041 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4041 = true := by
  rw [show A10K2.u4041 = KTree.node A10K2.t4048 (nat_lit 64785907) (nat_lit 7946139412) (nat_lit 0) A10K2.t4049 from rfl, allE_node, rows4048, irow4041, rows4049]
  all_goals rfl

theorem atot4041 : totK PA10K2 A10K2.u4041 = [0, 0, 0, 580077621842, 2903447700957, 4293328154804, 1828980186653, 218794108925, 7007974415, 0] := by
  rw [show A10K2.u4041 = KTree.node A10K2.t4048 (nat_lit 64785907) (nat_lit 7946139412) (nat_lit 0) A10K2.t4049 from rfl, totK_node, tot4048, tot4049]
  decide +kernel

theorem arows4042 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4042 = true := by
  rw [show A10K2.u4042 = KTree.node A10K2.t4050 (nat_lit 64807469) (nat_lit 3622845740) (nat_lit 32) A10K2.t4051 from rfl, allE_node, rows4050, irow4042, rows4051]
  all_goals rfl

theorem atot4042 : totK PA10K2 A10K2.u4042 = [0, 0, 0, 1088767194688, 3944410724254, 3951330575331, 1015209482976, 56520765960, 0, 0] := by
  rw [show A10K2.u4042 = KTree.node A10K2.t4050 (nat_lit 64807469) (nat_lit 3622845740) (nat_lit 32) A10K2.t4051 from rfl, totK_node, tot4050, tot4051]
  decide +kernel

theorem arows4044 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4044 = true := by
  rw [show A10K2.u4044 = KTree.node A10K2.t4052 (nat_lit 64825563) (nat_lit 9769904926) (nat_lit 0) A10K2.t4053 from rfl, allE_node, rows4052, irow4044, rows4053]
  all_goals rfl

theorem atot4044 : totK PA10K2 A10K2.u4044 = [0, 0, 822522717865, 3131520219829, 3691728359819, 1727159722315, 469191057992, 43720954405, 0, 0] := by
  rw [show A10K2.u4044 = KTree.node A10K2.t4052 (nat_lit 64825563) (nat_lit 9769904926) (nat_lit 0) A10K2.t4053 from rfl, totK_node, tot4052, tot4053]
  decide +kernel

theorem arows4045 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4045 = true := by
  rw [show A10K2.u4045 = KTree.node A10K2.t4054 (nat_lit 64830515) (nat_lit 6879635832) (nat_lit 0) A10K2.t4055 from rfl, allE_node, rows4054, irow4045, rows4055]
  all_goals rfl

theorem atot4045 : totK PA10K2 A10K2.u4045 = [0, 0, 405501146328, 2023190257975, 3828363265313, 2787473474956, 598837562240, 31306924438, 0, 0] := by
  rw [show A10K2.u4045 = KTree.node A10K2.t4054 (nat_lit 64830515) (nat_lit 6879635832) (nat_lit 0) A10K2.t4055 from rfl, totK_node, tot4054, tot4055]
  decide +kernel

theorem arows4048 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4048 = true := by
  rw [show A10K2.u4048 = KTree.node A10K2.t4056 (nat_lit 64839780) (nat_lit 4979102470) (nat_lit 0) A10K2.t4057 from rfl, allE_node, rows4056, irow4048, rows4057]
  all_goals rfl

theorem atot4048 : totK PA10K2 A10K2.u4048 = [0, 0, 675972554754, 2996995837937, 4136154455725, 1787190264988, 222147136619, 6239673734, 0, 0] := by
  rw [show A10K2.u4048 = KTree.node A10K2.t4056 (nat_lit 64839780) (nat_lit 4979102470) (nat_lit 0) A10K2.t4057 from rfl, totK_node, tot4056, tot4057]
  decide +kernel

theorem arows4049 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4049 = true := by
  rw [show A10K2.u4049 = KTree.node A10K2.t4058 (nat_lit 64844955) (nat_lit 10043584245) (nat_lit 0) A10K2.t4059 from rfl, allE_node, rows4058, irow4049, rows4059]
  all_goals rfl

theorem atot4049 : totK PA10K2 A10K2.u4049 = [0, 0, 227740758055, 1757876772764, 4176740334861, 3358061454371, 685941565630, 19087212590, 0, 0] := by
  rw [show A10K2.u4049 = KTree.node A10K2.t4058 (nat_lit 64844955) (nat_lit 10043584245) (nat_lit 0) A10K2.t4059 from rfl, totK_node, tot4058, tot4059]
  decide +kernel

theorem arows4051 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4051 = true := by
  rw [show A10K2.u4051 = KTree.node A10K2.t4060 (nat_lit 64858402) (nat_lit 13255969661) (nat_lit 0) A10K2.t4061 from rfl, allE_node, rows4060, irow4051, rows4061]
  all_goals rfl

theorem atot4051 : totK PA10K2 A10K2.u4051 = [0, 0, 0, 820030128603, 3273999862844, 4035709214083, 1545922923014, 130487754519, 0, 0] := by
  rw [show A10K2.u4051 = KTree.node A10K2.t4060 (nat_lit 64858402) (nat_lit 13255969661) (nat_lit 0) A10K2.t4061 from rfl, totK_node, tot4060, tot4061]
  decide +kernel

theorem arows4052 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4052 = true := by
  rw [show A10K2.u4052 = KTree.node A10K2.t4062 (nat_lit 64865540) (nat_lit 12244579610) (nat_lit 0) A10K2.t4063 from rfl, allE_node, rows4062, irow4052, rows4063]
  all_goals rfl

theorem atot4052 : totK PA10K2 A10K2.u4052 = [0, 0, 0, 806877092183, 3073890816825, 3876186068241, 1763415182362, 261015748542, 7151180950, 0] := by
  rw [show A10K2.u4052 = KTree.node A10K2.t4062 (nat_lit 64865540) (nat_lit 12244579610) (nat_lit 0) A10K2.t4063 from rfl, totK_node, tot4062, tot4063]
  decide +kernel

theorem arows4057 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4057 = true := by
  rw [show A10K2.u4057 = KTree.node A10K2.t4064 (nat_lit 64876216) (nat_lit 11243827491) (nat_lit 0) A10K2.t4065 from rfl, allE_node, rows4064, irow4057, rows4065]
  all_goals rfl

theorem atot4057 : totK PA10K2 A10K2.u4057 = [0, 0, 417243045409, 2014378385602, 3526921860823, 2862456964622, 903263007093, 62632138461, 0, 0] := by
  rw [show A10K2.u4057 = KTree.node A10K2.t4064 (nat_lit 64876216) (nat_lit 11243827491) (nat_lit 0) A10K2.t4065 from rfl, totK_node, tot4064, tot4065]
  decide +kernel

theorem arows4058 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4058 = true := by
  rw [show A10K2.u4058 = KTree.node A10K2.t4066 (nat_lit 64950782) (nat_lit 15046685384) (nat_lit 0) A10K2.t4067 from rfl, allE_node, rows4066, irow4058, rows4067]
  all_goals rfl

theorem atot4058 : totK PA10K2 A10K2.u4058 = [0, 0, 496290354451, 2345777944390, 3969801350687, 2518324463141, 403120723646, 11991740650, 0, 0] := by
  rw [show A10K2.u4058 = KTree.node A10K2.t4066 (nat_lit 64950782) (nat_lit 15046685384) (nat_lit 0) A10K2.t4067 from rfl, totK_node, tot4066, tot4067]
  decide +kernel

theorem arows4060 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4060 = true := by
  rw [show A10K2.u4060 = KTree.node A10K2.t4068 (nat_lit 64957916) (nat_lit 4574356716) (nat_lit 0) A10K2.t4069 from rfl, allE_node, rows4068, irow4060, rows4069]
  all_goals rfl

theorem atot4060 : totK PA10K2 A10K2.u4060 = [0, 0, 581144644929, 2734316471786, 4071127784906, 2147851354794, 373170363017, 12219140272, 0, 0] := by
  rw [show A10K2.u4060 = KTree.node A10K2.t4068 (nat_lit 64957916) (nat_lit 4574356716) (nat_lit 0) A10K2.t4069 from rfl, totK_node, tot4068, tot4069]
  decide +kernel

theorem arows4061 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4061 = true := by
  rw [show A10K2.u4061 = KTree.node A10K2.t4070 (nat_lit 64971533) (nat_lit 4834675152) (nat_lit 0) A10K2.t4071 from rfl, allE_node, rows4070, irow4061, rows4071]
  all_goals rfl

theorem atot4061 : totK PA10K2 A10K2.u4061 = [0, 0, 891342416461, 3270671550419, 3937897354705, 1703451140975, 162853900276, 0, 0, 0] := by
  rw [show A10K2.u4061 = KTree.node A10K2.t4070 (nat_lit 64971533) (nat_lit 4834675152) (nat_lit 0) A10K2.t4071 from rfl, totK_node, tot4070, tot4071]
  decide +kernel

theorem arows4064 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4064 = true := by
  rw [show A10K2.u4064 = KTree.node A10K2.t4072 (nat_lit 64976101) (nat_lit 5472747305) (nat_lit 0) A10K2.t4073 from rfl, allE_node, rows4072, irow4064, rows4073]
  all_goals rfl

theorem atot4064 : totK PA10K2 A10K2.u4064 = [0, 0, 0, 1261459000538, 4156976524013, 3765273627826, 807200529365, 25509470722, 0, 0] := by
  rw [show A10K2.u4064 = KTree.node A10K2.t4072 (nat_lit 64976101) (nat_lit 5472747305) (nat_lit 0) A10K2.t4073 from rfl, totK_node, tot4072, tot4073]
  decide +kernel

theorem arows4065 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4065 = true := by
  rw [show A10K2.u4065 = KTree.node A10K2.t4074 (nat_lit 64982164) (nat_lit 6842554534) (nat_lit 0) A10K2.t4075 from rfl, allE_node, rows4074, irow4065, rows4075]
  all_goals rfl

theorem atot4065 : totK PA10K2 A10K2.u4065 = [0, 0, 0, 722020647186, 2926800272002, 3957803485715, 1812225830733, 242387278631, 6318667960, 0] := by
  rw [show A10K2.u4065 = KTree.node A10K2.t4074 (nat_lit 64982164) (nat_lit 6842554534) (nat_lit 0) A10K2.t4075 from rfl, totK_node, tot4074, tot4075]
  decide +kernel

theorem arows4067 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4067 = true := by
  rw [show A10K2.u4067 = KTree.node A10K2.t4076 (nat_lit 64989027) (nat_lit 8426336287) (nat_lit 0) A10K2.t4077 from rfl, allE_node, rows4076, irow4067, rows4077]
  all_goals rfl

theorem atot4067 : totK PA10K2 A10K2.u4067 = [0, 0, 0, 766035887095, 3229721307121, 4178141043565, 1636841309210, 142219884794, 0, 0] := by
  rw [show A10K2.u4067 = KTree.node A10K2.t4076 (nat_lit 64989027) (nat_lit 8426336287) (nat_lit 0) A10K2.t4077 from rfl, totK_node, tot4076, tot4077]
  decide +kernel

theorem arows4068 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4068 = true := by
  rw [show A10K2.u4068 = KTree.node A10K2.t4078 (nat_lit 65003629) (nat_lit 2789903474) (nat_lit 0) A10K2.t4079 from rfl, allE_node, rows4078, irow4068, rows4079]
  all_goals rfl

theorem atot4068 : totK PA10K2 A10K2.u4068 = [0, 0, 0, 614948741438, 2789354893552, 4092124260176, 2031038849597, 248846912834, 6439430839, 0] := by
  rw [show A10K2.u4068 = KTree.node A10K2.t4078 (nat_lit 65003629) (nat_lit 2789903474) (nat_lit 0) A10K2.t4079 from rfl, totK_node, tot4078, tot4079]
  decide +kernel

theorem arows4072 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4072 = true := by
  rw [show A10K2.u4072 = KTree.node A10K2.t4080 (nat_lit 65008141) (nat_lit 2609886680) (nat_lit 0) A10K2.t4081 from rfl, allE_node, rows4080, irow4072, rows4081]
  all_goals rfl

theorem atot4072 : totK PA10K2 A10K2.u4072 = [0, 0, 0, 269216628779, 1985386040730, 4196373633478, 2888532059742, 472909249236, 12132367858, 0] := by
  rw [show A10K2.u4072 = KTree.node A10K2.t4080 (nat_lit 65008141) (nat_lit 2609886680) (nat_lit 0) A10K2.t4081 from rfl, totK_node, tot4080, tot4081]
  decide +kernel

theorem arows4073 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4073 = true := by
  rw [show A10K2.u4073 = KTree.node A10K2.t4082 (nat_lit 67110921) (nat_lit 9791040699) (nat_lit 0) A10K2.t4083 from rfl, allE_node, rows4082, irow4073, rows4083]
  all_goals rfl

theorem atot4073 : totK PA10K2 A10K2.u4073 = [869984120561, 3103308310460, 3170048165460, 879326732093, 40330130203, 312585060820, 838925398534, 488280079436, 48886019071, 0] := by
  rw [show A10K2.u4073 = KTree.node A10K2.t4082 (nat_lit 67110921) (nat_lit 9791040699) (nat_lit 0) A10K2.t4083 from rfl, totK_node, tot4082, tot4083]
  decide +kernel

theorem arows4075 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4075 = true := by
  rw [show A10K2.u4075 = KTree.node A10K2.t4084 (nat_lit 67115333) (nat_lit 6931832855) (nat_lit 0) A10K2.t4085 from rfl, allE_node, rows4084, irow4075, rows4085]
  all_goals rfl

theorem atot4075 : totK PA10K2 A10K2.u4075 = [293873915135, 1845818127963, 3917118039502, 2919560860082, 608609963539, 30831673886, 0, 0, 0, 0] := by
  rw [show A10K2.u4075 = KTree.node A10K2.t4084 (nat_lit 67115333) (nat_lit 6931832855) (nat_lit 0) A10K2.t4085 from rfl, totK_node, tot4084, tot4085]
  decide +kernel

theorem arows4076 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4076 = true := by
  rw [show A10K2.u4076 = KTree.node A10K2.t4086 (nat_lit 67128106) (nat_lit 11615766623) (nat_lit 0) A10K2.t4087 from rfl, allE_node, rows4086, irow4076, rows4087]
  all_goals rfl

theorem atot4076 : totK PA10K2 A10K2.u4076 = [433290635575, 2446494132457, 4139787319494, 1996802598742, 200563997796, 0, 0, 0, 0, 0] := by
  rw [show A10K2.u4076 = KTree.node A10K2.t4086 (nat_lit 67128106) (nat_lit 11615766623) (nat_lit 0) A10K2.t4087 from rfl, totK_node, tot4086, tot4087]
  decide +kernel

theorem arows4079 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4079 = true := by
  rw [show A10K2.u4079 = KTree.node A10K2.t4088 (nat_lit 67136580) (nat_lit 9682573901) (nat_lit 0) A10K2.t4089 from rfl, allE_node, rows4088, irow4079, rows4089]
  all_goals rfl

theorem atot4079 : totK PA10K2 A10K2.u4079 = [741544312551, 3025033359746, 3989747432788, 1849946307238, 266806198050, 6354482628, 0, 0, 0, 0] := by
  rw [show A10K2.u4079 = KTree.node A10K2.t4088 (nat_lit 67136580) (nat_lit 9682573901) (nat_lit 0) A10K2.t4089 from rfl, totK_node, tot4088, tot4089]
  decide +kernel

theorem arows4080 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4080 = true := by
  rw [show A10K2.u4080 = KTree.node A10K2.t4090 (nat_lit 67141533) (nat_lit 1730942941) (nat_lit 0) A10K2.t4091 from rfl, allE_node, rows4090, irow4080, rows4091]
  all_goals rfl

theorem atot4080 : totK PA10K2 A10K2.u4080 = [0, 1020614095192, 3609761616995, 3852874796990, 1170563308586, 80908104087, 0, 0, 0, 0] := by
  rw [show A10K2.u4080 = KTree.node A10K2.t4090 (nat_lit 67141533) (nat_lit 1730942941) (nat_lit 0) A10K2.t4091 from rfl, totK_node, tot4090, tot4091]
  decide +kernel

theorem arows4082 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4082 = true := by
  rw [show A10K2.u4082 = KTree.node A10K2.t4092 (nat_lit 67146029) (nat_lit 6314124959) (nat_lit 0) A10K2.t4093 from rfl, allE_node, rows4092, irow4082, rows4093]
  all_goals rfl

theorem atot4082 : totK PA10K2 A10K2.u4082 = [0, 286204115926, 2022829583446, 4018173830477, 2546480390059, 532402596715, 30650496230, 0, 0, 0] := by
  rw [show A10K2.u4082 = KTree.node A10K2.t4092 (nat_lit 67146029) (nat_lit 6314124959) (nat_lit 0) A10K2.t4093 from rfl, totK_node, tot4092, tot4093]
  decide +kernel

theorem arows4083 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4083 = true := by
  rw [show A10K2.u4083 = KTree.node A10K2.t4094 (nat_lit 67159829) (nat_lit 6936884917) (nat_lit 0) A10K2.t4095 from rfl, allE_node, rows4094, irow4083, rows4095]
  all_goals rfl

theorem atot4083 : totK PA10K2 A10K2.u4083 = [0, 724917506774, 3205316172090, 4028425333772, 1379166664138, 94209790661, 0, 0, 0, 0] := by
  rw [show A10K2.u4083 = KTree.node A10K2.t4094 (nat_lit 67159829) (nat_lit 6936884917) (nat_lit 0) A10K2.t4095 from rfl, totK_node, tot4094, tot4095]
  decide +kernel

theorem arows4095 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4095 = true := by
  rw [show A10K2.u4095 = KTree.node A10K2.t4096 (nat_lit 67166818) (nat_lit 3345419136) (nat_lit 0) A10K2.t4097 from rfl, allE_node, rows4096, irow4095, rows4097]
  all_goals rfl

theorem atot4095 : totK PA10K2 A10K2.u4095 = [0, 739014639184, 3024247367519, 3985206196397, 1641655564375, 191631790177, 5546304973, 0, 0, 0] := by
  rw [show A10K2.u4095 = KTree.node A10K2.t4096 (nat_lit 67166818) (nat_lit 3345419136) (nat_lit 0) A10K2.t4097 from rfl, totK_node, tot4096, tot4097]
  decide +kernel

theorem arows4096 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4096 = true := by
  rw [show A10K2.u4096 = KTree.node A10K2.t4098 (nat_lit 67242349) (nat_lit 6396598253) (nat_lit 0) A10K2.t4099 from rfl, allE_node, rows4098, irow4096, rows4099]
  all_goals rfl

theorem atot4096 : totK PA10K2 A10K2.u4096 = [797268155618, 3215263451399, 3947534566103, 1541976665707, 302374684117, 37646807062, 0, 0, 0, 0] := by
  rw [show A10K2.u4096 = KTree.node A10K2.t4098 (nat_lit 67242349) (nat_lit 6396598253) (nat_lit 0) A10K2.t4099 from rfl, totK_node, tot4098, tot4099]
  decide +kernel

theorem arows4098 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4098 = true := by
  rw [show A10K2.u4098 = KTree.node A10K2.t4100 (nat_lit 67247602) (nat_lit 12374278943) (nat_lit 0) A10K2.t4101 from rfl, allE_node, rows4100, irow4098, rows4101]
  all_goals rfl

theorem atot4098 : totK PA10K2 A10K2.u4098 = [469591264720, 2267389156141, 3734090708993, 2493768810591, 546078014497, 30831673886, 0, 0, 0, 0] := by
  rw [show A10K2.u4098 = KTree.node A10K2.t4100 (nat_lit 67247602) (nat_lit 12374278943) (nat_lit 0) A10K2.t4101 from rfl, totK_node, tot4100, tot4101]
  decide +kernel

theorem arows4099 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4099 = true := by
  rw [show A10K2.u4099 = KTree.node A10K2.t4102 (nat_lit 67256429) (nat_lit 5466235624) (nat_lit 0) A10K2.t4103 from rfl, allE_node, rows4102, irow4099, rows4103]
  all_goals rfl

theorem atot4099 : totK PA10K2 A10K2.u4099 = [590701440334, 2356043957802, 3597938521522, 2322088287700, 520748864922, 31768748853, 0, 0, 0, 0] := by
  rw [show A10K2.u4099 = KTree.node A10K2.t4102 (nat_lit 67256429) (nat_lit 5466235624) (nat_lit 0) A10K2.t4103 from rfl, totK_node, tot4102, tot4103]
  decide +kernel

theorem arows4102 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4102 = true := by
  rw [show A10K2.u4102 = KTree.node A10K2.t4104 (nat_lit 67261792) (nat_lit 10654885628) (nat_lit 0) A10K2.t4105 from rfl, allE_node, rows4104, irow4102, rows4105]
  all_goals rfl

theorem atot4102 : totK PA10K2 A10K2.u4102 = [198880611318, 1982308916830, 4266094864731, 2567365071984, 358723743762, 6354482628, 0, 0, 0, 0] := by
  rw [show A10K2.u4102 = KTree.node A10K2.t4104 (nat_lit 67261792) (nat_lit 10654885628) (nat_lit 0) A10K2.t4105 from rfl, totK_node, tot4104, tot4105]
  decide +kernel

theorem arows4103 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4103 = true := by
  rw [show A10K2.u4103 = KTree.node A10K2.t4106 (nat_lit 67276296) (nat_lit 14334121386) (nat_lit 0) A10K2.t4107 from rfl, allE_node, rows4106, irow4103, rows4107]
  all_goals rfl

theorem atot4103 : totK PA10K2 A10K2.u4103 = [0, 955994984932, 3587601208279, 3930768202936, 1112453048440, 64899520130, 0, 0, 0, 0] := by
  rw [show A10K2.u4103 = KTree.node A10K2.t4106 (nat_lit 67276296) (nat_lit 14334121386) (nat_lit 0) A10K2.t4107 from rfl, totK_node, tot4106, tot4107]
  decide +kernel

theorem arows4105 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4105 = true := by
  rw [show A10K2.u4105 = KTree.node A10K2.t4108 (nat_lit 67290864) (nat_lit 11933677) (nat_lit 0) A10K2.t4109 from rfl, allE_node, rows4108, irow4105, rows4109]
  all_goals rfl

theorem atot4105 : totK PA10K2 A10K2.u4105 = [0, 785737938173, 3266467371674, 3946978349449, 1229239941966, 88866877739, 0, 0, 0, 0] := by
  rw [show A10K2.u4105 = KTree.node A10K2.t4108 (nat_lit 67290864) (nat_lit 11933677) (nat_lit 0) A10K2.t4109 from rfl, totK_node, tot4108, tot4109]
  decide +kernel

theorem arows4106 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4106 = true := by
  rw [show A10K2.u4106 = KTree.node A10K2.t4110 (nat_lit 67305914) (nat_lit 12028605723) (nat_lit 0) A10K2.t4111 from rfl, allE_node, rows4110, irow4106, rows4111]
  all_goals rfl

theorem atot4106 : totK PA10K2 A10K2.u4106 = [809589589006, 2572406679911, 2724649527845, 1998392750966, 1177483177492, 233528391130, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u4106 = KTree.node A10K2.t4110 (nat_lit 67305914) (nat_lit 12028605723) (nat_lit 0) A10K2.t4111 from rfl, totK_node, tot4110, tot4111]
  decide +kernel

theorem arows4110 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4110 = true := by
  rw [show A10K2.u4110 = KTree.node A10K2.t4112 (nat_lit 67311628) (nat_lit 11641740415) (nat_lit 0) A10K2.t4113 from rfl, allE_node, rows4112, irow4110, rows4113]
  all_goals rfl

theorem atot4110 : totK PA10K2 A10K2.u4110 = [280582103063, 1962517495391, 4117712171216, 2897561961625, 591976260838, 30810868011, 0, 0, 0, 0] := by
  rw [show A10K2.u4110 = KTree.node A10K2.t4112 (nat_lit 67311628) (nat_lit 11641740415) (nat_lit 0) A10K2.t4113 from rfl, totK_node, tot4112, tot4113]
  decide +kernel

theorem arows4111 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4111 = true := by
  rw [show A10K2.u4111 = KTree.node A10K2.t4114 (nat_lit 67330633) (nat_lit 9560104829) (nat_lit 0) A10K2.t4115 from rfl, allE_node, rows4114, irow4111, rows4115]
  all_goals rfl

theorem atot4111 : totK PA10K2 A10K2.u4111 = [798245797634, 3282365097762, 4248825830028, 1747988863419, 157556490937, 0, 0, 0, 0, 0] := by
  rw [show A10K2.u4111 = KTree.node A10K2.t4114 (nat_lit 67330633) (nat_lit 9560104829) (nat_lit 0) A10K2.t4115 from rfl, totK_node, tot4114, tot4115]
  decide +kernel

theorem arows4113 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4113 = true := by
  rw [show A10K2.u4113 = KTree.node A10K2.t4116 (nat_lit 67335862) (nat_lit 16028661167) (nat_lit 0) A10K2.t4117 from rfl, allE_node, rows4116, irow4113, rows4117]
  all_goals rfl

theorem atot4113 : totK PA10K2 A10K2.u4113 = [0, 1186895732224, 3956241836625, 3781356198839, 1046133064577, 62996513375, 0, 0, 0, 0] := by
  rw [show A10K2.u4113 = KTree.node A10K2.t4116 (nat_lit 67335862) (nat_lit 16028661167) (nat_lit 0) A10K2.t4117 from rfl, totK_node, tot4116, tot4117]
  decide +kernel

theorem arows4114 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4114 = true := by
  rw [show A10K2.u4114 = KTree.node A10K2.t4118 (nat_lit 67341701) (nat_lit 4380394034) (nat_lit 0) A10K2.t4119 from rfl, allE_node, rows4118, irow4114, rows4119]
  all_goals rfl

theorem atot4114 : totK PA10K2 A10K2.u4114 = [0, 608459682534, 2770929867652, 4091736648335, 2053859487371, 288859573275, 6904928264, 0, 0, 0] := by
  rw [show A10K2.u4114 = KTree.node A10K2.t4118 (nat_lit 67341701) (nat_lit 4380394034) (nat_lit 0) A10K2.t4119 from rfl, totK_node, tot4118, tot4119]
  decide +kernel

theorem arows4117 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4117 = true := by
  rw [show A10K2.u4117 = KTree.node A10K2.t4120 (nat_lit 67350258) (nat_lit 14849180383) (nat_lit 0) A10K2.t4121 from rfl, allE_node, rows4120, irow4117, rows4121]
  all_goals rfl

theorem atot4117 : totK PA10K2 A10K2.u4117 = [0, 567723269000, 2858837743008, 4397580443354, 2033987005040, 185748166897, 0, 0, 0, 0] := by
  rw [show A10K2.u4117 = KTree.node A10K2.t4120 (nat_lit 67350258) (nat_lit 14849180383) (nat_lit 0) A10K2.t4121 from rfl, totK_node, tot4120, tot4121]
  decide +kernel

theorem arows4118 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4118 = true := by
  rw [show A10K2.u4118 = KTree.node A10K2.t4122 (nat_lit 67366846) (nat_lit 16396326754) (nat_lit 0) A10K2.t4123 from rfl, allE_node, rows4122, irow4118, rows4123]
  all_goals rfl

theorem atot4118 : totK PA10K2 A10K2.u4118 = [0, 509527639890, 2453875174846, 4066805386233, 2589853558638, 460497002641, 12224107035, 0, 0, 0] := by
  rw [show A10K2.u4118 = KTree.node A10K2.t4122 (nat_lit 67366846) (nat_lit 16396326754) (nat_lit 0) A10K2.t4123 from rfl, totK_node, tot4122, tot4123]
  decide +kernel

theorem arows4120 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4120 = true := by
  rw [show A10K2.u4120 = KTree.node A10K2.t4124 (nat_lit 67371556) (nat_lit 12996636639) (nat_lit 0) A10K2.t4125 from rfl, allE_node, rows4124, irow4120, rows4125]
  all_goals rfl

theorem atot4120 : totK PA10K2 A10K2.u4120 = [0, 867440094412, 2948625757347, 3398849869838, 1829473709280, 540964810455, 48886019071, 0, 0, 0] := by
  rw [show A10K2.u4120 = KTree.node A10K2.t4124 (nat_lit 67371556) (nat_lit 12996636639) (nat_lit 0) A10K2.t4125 from rfl, totK_node, tot4124, tot4125]
  decide +kernel

theorem arows4121 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4121 = true := by
  rw [show A10K2.u4121 = KTree.node A10K2.t4126 (nat_lit 67376063) (nat_lit 9955663627) (nat_lit 0) A10K2.t4127 from rfl, allE_node, rows4126, irow4121, rows4127]
  all_goals rfl

theorem atot4121 : totK PA10K2 A10K2.u4121 = [0, 212919441758, 1787311601031, 4040850046964, 2911082896122, 585145896603, 30831673886, 0, 0, 0] := by
  rw [show A10K2.u4121 = KTree.node A10K2.t4126 (nat_lit 67376063) (nat_lit 9955663627) (nat_lit 0) A10K2.t4127 from rfl, totK_node, tot4126, tot4127]
  decide +kernel

theorem arows4126 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4126 = true := by
  rw [show A10K2.u4126 = KTree.node A10K2.t4128 (nat_lit 67389781) (nat_lit 6980450443) (nat_lit 0) A10K2.t4129 from rfl, allE_node, rows4128, irow4126, rows4129]
  all_goals rfl

theorem atot4126 : totK PA10K2 A10K2.u4126 = [0, 513572489737, 2846476733641, 4229501735287, 1605876678790, 108862444279, 0, 0, 0, 0] := by
  rw [show A10K2.u4126 = KTree.node A10K2.t4128 (nat_lit 67389781) (nat_lit 6980450443) (nat_lit 0) A10K2.t4129 from rfl, totK_node, tot4128, tot4129]
  decide +kernel

theorem arows4127 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4127 = true := by
  rw [show A10K2.u4127 = KTree.node A10K2.t4130 (nat_lit 67397297) (nat_lit 5260917258) (nat_lit 0) A10K2.t4131 from rfl, allE_node, rows4130, irow4127, rows4131]
  all_goals rfl

theorem atot4127 : totK PA10K2 A10K2.u4127 = [0, 740599976690, 2948060390051, 3939294673747, 1836130374934, 230248539210, 5705019915, 0, 0, 0] := by
  rw [show A10K2.u4127 = KTree.node A10K2.t4130 (nat_lit 67397297) (nat_lit 5260917258) (nat_lit 0) A10K2.t4131 from rfl, totK_node, tot4130, tot4131]
  decide +kernel

theorem arows4129 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4129 = true := by
  rw [show A10K2.u4129 = KTree.node A10K2.t4132 (nat_lit 67403671) (nat_lit 14550483610) (nat_lit 0) A10K2.t4133 from rfl, allE_node, rows4132, irow4129, rows4133]
  all_goals rfl

theorem atot4129 : totK PA10K2 A10K2.u4129 = [0, 0, 1086051071055, 3807647009323, 3773104619850, 1003665536275, 60698249753, 0, 0, 0] := by
  rw [show A10K2.u4129 = KTree.node A10K2.t4132 (nat_lit 67403671) (nat_lit 14550483610) (nat_lit 0) A10K2.t4133 from rfl, totK_node, tot4132, tot4133]
  decide +kernel

theorem arows4130 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4130 = true := by
  rw [show A10K2.u4130 = KTree.node A10K2.t4134 (nat_lit 67408257) (nat_lit 10422756214) (nat_lit 0) A10K2.t4135 from rfl, allE_node, rows4134, irow4130, rows4135]
  all_goals rfl

theorem atot4130 : totK PA10K2 A10K2.u4130 = [0, 0, 282002292585, 2017323470159, 3965790687799, 2507818241329, 527148285369, 30605747850, 0, 0] := by
  rw [show A10K2.u4130 = KTree.node A10K2.t4134 (nat_lit 67408257) (nat_lit 10422756214) (nat_lit 0) A10K2.t4135 from rfl, totK_node, tot4134, tot4135]
  decide +kernel

theorem arows4133 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4133 = true := by
  rw [show A10K2.u4133 = KTree.node A10K2.t4136 (nat_lit 67422209) (nat_lit 10401506608) (nat_lit 0) A10K2.t4137 from rfl, allE_node, rows4136, irow4133, rows4137]
  all_goals rfl

theorem atot4133 : totK PA10K2 A10K2.u4133 = [0, 0, 719111798190, 3150247409547, 3931141878494, 1294387903794, 99009048472, 0, 0, 0] := by
  rw [show A10K2.u4133 = KTree.node A10K2.t4136 (nat_lit 67422209) (nat_lit 10401506608) (nat_lit 0) A10K2.t4137 from rfl, totK_node, tot4136, tot4137]
  decide +kernel

theorem arows4134 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4134 = true := by
  rw [show A10K2.u4134 = KTree.node A10K2.t4138 (nat_lit 67429296) (nat_lit 14609840793) (nat_lit 0) A10K2.t4139 from rfl, allE_node, rows4138, irow4134, rows4139]
  all_goals rfl

theorem atot4134 : totK PA10K2 A10K2.u4134 = [0, 237700837005, 1314926548950, 3050595404606, 3412795108590, 1394095119186, 195477646924, 5528811039, 0, 0] := by
  rw [show A10K2.u4134 = KTree.node A10K2.t4138 (nat_lit 67429296) (nat_lit 14609840793) (nat_lit 0) A10K2.t4139 from rfl, totK_node, tot4138, tot4139]
  decide +kernel

theorem arows4136 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4136 = true := by
  rw [show A10K2.u4136 = KTree.node A10K2.t4140 (nat_lit 67505260) (nat_lit 11126500675) (nat_lit 0) A10K2.t4141 from rfl, allE_node, rows4140, irow4136, rows4141]
  all_goals rfl

theorem atot4136 : totK PA10K2 A10K2.u4136 = [0, 544141641578, 2709294913428, 4031359949419, 2051656051259, 395450058706, 25371180993, 0, 0, 0] := by
  rw [show A10K2.u4136 = KTree.node A10K2.t4140 (nat_lit 67505260) (nat_lit 11126500675) (nat_lit 0) A10K2.t4141 from rfl, totK_node, tot4140, tot4141]
  decide +kernel

theorem arows4137 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4137 = true := by
  rw [show A10K2.u4137 = KTree.node A10K2.t4142 (nat_lit 67512042) (nat_lit 12287459258) (nat_lit 0) A10K2.t4143 from rfl, allE_node, rows4142, irow4137, rows4143]
  all_goals rfl

theorem atot4137 : totK PA10K2 A10K2.u4137 = [0, 469339957255, 2459000160639, 4104433034303, 2180582819865, 280718055481, 5460492893, 0, 0, 0] := by
  rw [show A10K2.u4137 = KTree.node A10K2.t4142 (nat_lit 67512042) (nat_lit 12287459258) (nat_lit 0) A10K2.t4143 from rfl, totK_node, tot4142, tot4143]
  decide +kernel

theorem arows4141 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4141 = true := by
  rw [show A10K2.u4141 = KTree.node A10K2.t4144 (nat_lit 67519722) (nat_lit 12496322621) (nat_lit 0) A10K2.t4145 from rfl, allE_node, rows4144, irow4141, rows4145]
  all_goals rfl

theorem atot4141 : totK PA10K2 A10K2.u4141 = [0, 788883354754, 3059111009643, 3694128732529, 1563024969117, 205659391278, 6034215561, 0, 0, 0] := by
  rw [show A10K2.u4141 = KTree.node A10K2.t4144 (nat_lit 67519722) (nat_lit 12496322621) (nat_lit 0) A10K2.t4145 from rfl, totK_node, tot4144, tot4145]
  decide +kernel

theorem arows4142 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4142 = true := by
  rw [show A10K2.u4142 = KTree.node A10K2.t4146 (nat_lit 67525418) (nat_lit 11406714635) (nat_lit 0) A10K2.t4147 from rfl, allE_node, rows4146, irow4142, rows4147]
  all_goals rfl

theorem atot4142 : totK PA10K2 A10K2.u4142 = [0, 0, 1265566237584, 4086033763810, 3291254909561, 664244315519, 31987755669, 0, 0, 0] := by
  rw [show A10K2.u4142 = KTree.node A10K2.t4146 (nat_lit 67525418) (nat_lit 11406714635) (nat_lit 0) A10K2.t4147 from rfl, totK_node, tot4146, tot4147]
  decide +kernel

theorem arows4144 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4144 = true := by
  rw [show A10K2.u4144 = KTree.node A10K2.t4148 (nat_lit 67545372) (nat_lit 12193009390) (nat_lit 0) A10K2.t4149 from rfl, allE_node, rows4148, irow4144, rows4149]
  all_goals rfl

theorem atot4144 : totK PA10K2 A10K2.u4144 = [0, 0, 1145207128620, 3842239904628, 3631405661576, 851276751522, 43891732673, 0, 0, 0] := by
  rw [show A10K2.u4144 = KTree.node A10K2.t4148 (nat_lit 67545372) (nat_lit 12193009390) (nat_lit 0) A10K2.t4149 from rfl, totK_node, tot4148, tot4149]
  decide +kernel

theorem arows4145 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4145 = true := by
  rw [show A10K2.u4145 = KTree.node A10K2.t4150 (nat_lit 67555688) (nat_lit 9812550568) (nat_lit 0) A10K2.t4151 from rfl, allE_node, rows4150, irow4145, rows4151]
  all_goals rfl

theorem atot4145 : totK PA10K2 A10K2.u4145 = [0, 308867641608, 1043838280107, 2520119146746, 3535570143869, 1556069907121, 198193725560, 5676195732, 0, 0] := by
  rw [show A10K2.u4145 = KTree.node A10K2.t4150 (nat_lit 67555688) (nat_lit 9812550568) (nat_lit 0) A10K2.t4151 from rfl, totK_node, tot4150, tot4151]
  decide +kernel

theorem arows4148 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4148 = true := by
  rw [show A10K2.u4148 = KTree.node A10K2.t4152 (nat_lit 67571157) (nat_lit 1488897440) (nat_lit 0) A10K2.t4153 from rfl, allE_node, rows4152, irow4148, rows4153]
  all_goals rfl

theorem atot4148 : totK PA10K2 A10K2.u4148 = [0, 497548885211, 2592940915558, 4100030029867, 2149690915116, 407536555575, 25313348169, 0, 0, 0] := by
  rw [show A10K2.u4148 = KTree.node A10K2.t4152 (nat_lit 67571157) (nat_lit 1488897440) (nat_lit 0) A10K2.t4153 from rfl, totK_node, tot4152, tot4153]
  decide +kernel

theorem arows4149 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4149 = true := by
  rw [show A10K2.u4149 = KTree.node A10K2.t4154 (nat_lit 67579794) (nat_lit 15204535253) (nat_lit 0) A10K2.t4155 from rfl, allE_node, rows4154, irow4149, rows4155]
  all_goals rfl

theorem atot4149 : totK PA10K2 A10K2.u4149 = [0, 606943300452, 2841602485504, 4342332441570, 2111995931055, 213940030470, 0, 0, 0, 0] := by
  rw [show A10K2.u4149 = KTree.node A10K2.t4154 (nat_lit 67579794) (nat_lit 15204535253) (nat_lit 0) A10K2.t4155 from rfl, totK_node, tot4154, tot4155]
  decide +kernel

theorem arows4151 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4151 = true := by
  rw [show A10K2.u4151 = KTree.node A10K2.t4156 (nat_lit 67596238) (nat_lit 14588966310) (nat_lit 0) A10K2.t4157 from rfl, allE_node, rows4156, irow4151, rows4157]
  all_goals rfl

theorem atot4151 : totK PA10K2 A10K2.u4151 = [0, 470800666846, 2394792444476, 4116572959847, 2665656629300, 511367107269, 13231026584, 0, 0, 0] := by
  rw [show A10K2.u4151 = KTree.node A10K2.t4156 (nat_lit 67596238) (nat_lit 14588966310) (nat_lit 0) A10K2.t4157 from rfl, totK_node, tot4156, tot4157]
  decide +kernel

theorem arows4152 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4152 = true := by
  rw [show A10K2.u4152 = KTree.node A10K2.t4158 (nat_lit 68157989) (nat_lit 6956416829) (nat_lit 0) A10K2.t4159 from rfl, allE_node, rows4158, irow4152, rows4159]
  all_goals rfl

theorem atot4152 : totK PA10K2 A10K2.u4152 = [833436429740, 2726276726936, 2719664460110, 1551684645780, 1291088503798, 515345721022, 49137536365, 0, 0, 0] := by
  rw [show A10K2.u4152 = KTree.node A10K2.t4158 (nat_lit 68157989) (nat_lit 6956416829) (nat_lit 0) A10K2.t4159 from rfl, totK_node, tot4158, tot4159]
  decide +kernel

theorem arows4158 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4158 = true := by
  rw [show A10K2.u4158 = KTree.node A10K2.t4160 (nat_lit 68163640) (nat_lit 14671596437) (nat_lit 0) A10K2.t4161 from rfl, allE_node, rows4160, irow4158, rows4161]
  all_goals rfl

theorem atot4158 : totK PA10K2 A10K2.u4158 = [288483183456, 1830993444840, 3882599223661, 2861138112064, 585795407127, 30831673886, 0, 0, 0, 0] := by
  rw [show A10K2.u4158 = KTree.node A10K2.t4160 (nat_lit 68163640) (nat_lit 14671596437) (nat_lit 0) A10K2.t4161 from rfl, totK_node, tot4160, tot4161]
  decide +kernel

theorem arows4159 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4159 = true := by
  rw [show A10K2.u4159 = KTree.node A10K2.t4162 (nat_lit 68176172) (nat_lit 13552313479) (nat_lit 0) A10K2.t4163 from rfl, allE_node, rows4162, irow4159, rows4163]
  all_goals rfl

theorem atot4159 : totK PA10K2 A10K2.u4159 = [481540779949, 2747373900648, 4312164624079, 1832104181688, 159402439840, 0, 0, 0, 0, 0] := by
  rw [show A10K2.u4159 = KTree.node A10K2.t4162 (nat_lit 68176172) (nat_lit 13552313479) (nat_lit 0) A10K2.t4163 from rfl, totK_node, tot4162, tot4163]
  decide +kernel

theorem arows4161 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4161 = true := by
  rw [show A10K2.u4161 = KTree.node A10K2.t4164 (nat_lit 68185164) (nat_lit 9346681583) (nat_lit 0) A10K2.t4165 from rfl, allE_node, rows4164, irow4161, rows4165]
  all_goals rfl

theorem atot4161 : totK PA10K2 A10K2.u4161 = [552312781151, 2428551463327, 3880411661687, 2436317682709, 446186496493, 13207830636, 0, 0, 0, 0] := by
  rw [show A10K2.u4161 = KTree.node A10K2.t4164 (nat_lit 68185164) (nat_lit 9346681583) (nat_lit 0) A10K2.t4165 from rfl, totK_node, tot4164, tot4165]
  decide +kernel

theorem arows4162 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4162 = true := by
  rw [show A10K2.u4162 = KTree.node A10K2.t4166 (nat_lit 68190769) (nat_lit 9984173080) (nat_lit 0) A10K2.t4167 from rfl, allE_node, rows4166, irow4162, rows4167]
  all_goals rfl

theorem atot4162 : totK PA10K2 A10K2.u4162 = [0, 1087700474005, 3742151559311, 3726035226768, 1026927679654, 73919303287, 0, 0, 0, 0] := by
  rw [show A10K2.u4162 = KTree.node A10K2.t4166 (nat_lit 68190769) (nat_lit 9984173080) (nat_lit 0) A10K2.t4167 from rfl, totK_node, tot4166, tot4167]
  decide +kernel

theorem arows4165 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4165 = true := by
  rw [show A10K2.u4165 = KTree.node A10K2.t4168 (nat_lit 68196499) (nat_lit 9599143371) (nat_lit 0) A10K2.t4169 from rfl, allE_node, rows4168, irow4165, rows4169]
  all_goals rfl

theorem atot4165 : totK PA10K2 A10K2.u4165 = [0, 287912073481, 1956289944315, 3936033978934, 2658402192331, 549802920840, 30650496230, 0, 0, 0] := by
  rw [show A10K2.u4165 = KTree.node A10K2.t4168 (nat_lit 68196499) (nat_lit 9599143371) (nat_lit 0) A10K2.t4169 from rfl, totK_node, tot4168, tot4169]
  decide +kernel

theorem arows4166 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4166 = true := by
  rw [show A10K2.u4166 = KTree.node A10K2.t4170 (nat_lit 68209330) (nat_lit 10492908025) (nat_lit 0) A10K2.t4171 from rfl, allE_node, rows4170, irow4166, rows4171]
  all_goals rfl

theorem atot4166 : totK PA10K2 A10K2.u4166 = [0, 480572733570, 2672415844120, 4300278982175, 1814233393834, 150062644756, 0, 0, 0, 0] := by
  rw [show A10K2.u4166 = KTree.node A10K2.t4170 (nat_lit 68209330) (nat_lit 10492908025) (nat_lit 0) A10K2.t4171 from rfl, totK_node, tot4170, tot4171]
  decide +kernel

theorem arows4168 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4168 = true := by
  rw [show A10K2.u4168 = KTree.node A10K2.t4172 (nat_lit 68218440) (nat_lit 13520811228) (nat_lit 0) A10K2.t4173 from rfl, allE_node, rows4172, irow4168, rows4173]
  all_goals rfl

theorem atot4168 : totK PA10K2 A10K2.u4168 = [469390687660, 2074182621010, 3470886791669, 2685671173308, 962034195375, 144645268522, 5546304973, 0, 0, 0] := by
  rw [show A10K2.u4168 = KTree.node A10K2.t4172 (nat_lit 68218440) (nat_lit 13520811228) (nat_lit 0) A10K2.t4173 from rfl, totK_node, tot4172, tot4173]
  decide +kernel

theorem arows4169 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4169 = true := by
  rw [show A10K2.u4169 = KTree.node A10K2.t4174 (nat_lit 68236720) (nat_lit 6763816986) (nat_lit 0) A10K2.t4175 from rfl, allE_node, rows4174, irow4169, rows4175]
  all_goals rfl

theorem atot4169 : totK PA10K2 A10K2.u4169 = [293593425400, 2025854377492, 4021610736154, 2798790767922, 589511926772, 31768748853, 0, 0, 0, 0] := by
  rw [show A10K2.u4169 = KTree.node A10K2.t4174 (nat_lit 68236720) (nat_lit 6763816986) (nat_lit 0) A10K2.t4175 from rfl, totK_node, tot4174, tot4175]
  decide +kernel

theorem arows4173 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4173 = true := by
  rw [show A10K2.u4173 = KTree.node A10K2.t4176 (nat_lit 68241249) (nat_lit 5265847866) (nat_lit 0) A10K2.t4177 from rfl, allE_node, rows4176, irow4173, rows4177]
  all_goals rfl

theorem atot4173 : totK PA10K2 A10K2.u4173 = [779393338859, 3235786339866, 4029536882819, 1555925360080, 139018090122, 0, 0, 0, 0, 0] := by
  rw [show A10K2.u4173 = KTree.node A10K2.t4176 (nat_lit 68241249) (nat_lit 5265847866) (nat_lit 0) A10K2.t4177 from rfl, totK_node, tot4176, tot4177]
  decide +kernel

theorem arows4174 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4174 = true := by
  rw [show A10K2.u4174 = KTree.node A10K2.t4178 (nat_lit 68265470) (nat_lit 15692080028) (nat_lit 0) A10K2.t4179 from rfl, allE_node, rows4178, irow4174, rows4179]
  all_goals rfl

theorem atot4174 : totK PA10K2 A10K2.u4174 = [0, 1134894905873, 4005533828549, 3625668758580, 828519077360, 38878015291, 0, 0, 0, 0] := by
  rw [show A10K2.u4174 = KTree.node A10K2.t4178 (nat_lit 68265470) (nat_lit 15692080028) (nat_lit 0) A10K2.t4179 from rfl, totK_node, tot4178, tot4179]
  decide +kernel

theorem arows4176 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4176 = true := by
  rw [show A10K2.u4176 = KTree.node A10K2.t4180 (nat_lit 68270358) (nat_lit 9764687505) (nat_lit 0) A10K2.t4181 from rfl, allE_node, rows4180, irow4176, rows4181]
  all_goals rfl

theorem atot4176 : totK PA10K2 A10K2.u4176 = [0, 367218047613, 1979274329582, 3910327127941, 2726132586854, 577199748868, 31082886609, 0, 0, 0] := by
  rw [show A10K2.u4176 = KTree.node A10K2.t4180 (nat_lit 68270358) (nat_lit 9764687505) (nat_lit 0) A10K2.t4181 from rfl, totK_node, tot4180, tot4181]
  decide +kernel

theorem arows4177 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4177 = true := by
  rw [show A10K2.u4177 = KTree.node A10K2.t4182 (nat_lit 68276258) (nat_lit 7502316404) (nat_lit 0) A10K2.t4183 from rfl, allE_node, rows4182, irow4177, rows4183]
  all_goals rfl

theorem atot4177 : totK PA10K2 A10K2.u4177 = [0, 411757640958, 2511961576069, 4236468592175, 2056023660803, 245885793701, 0, 0, 0, 0] := by
  rw [show A10K2.u4177 = KTree.node A10K2.t4182 (nat_lit 68276258) (nat_lit 7502316404) (nat_lit 0) A10K2.t4183 from rfl, totK_node, tot4182, tot4183]
  decide +kernel

theorem arows4180 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4180 = true := by
  rw [show A10K2.u4180 = KTree.node A10K2.t4184 (nat_lit 68291223) (nat_lit 6122631513) (nat_lit 0) A10K2.t4185 from rfl, allE_node, rows4184, irow4180, rows4185]
  all_goals rfl

theorem atot4180 : totK PA10K2 A10K2.u4180 = [762214156616, 3070515681374, 3874661500281, 1637013594833, 267535478947, 20070762815, 0, 0, 0, 0] := by
  rw [show A10K2.u4180 = KTree.node A10K2.t4184 (nat_lit 68291223) (nat_lit 6122631513) (nat_lit 0) A10K2.t4185 from rfl, totK_node, tot4184, tot4185]
  decide +kernel

theorem arows4181 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4181 = true := by
  rw [show A10K2.u4181 = KTree.node A10K2.t4186 (nat_lit 68297996) (nat_lit 11466341189) (nat_lit 0) A10K2.t4187 from rfl, allE_node, rows4186, irow4181, rows4187]
  all_goals rfl

theorem atot4181 : totK PA10K2 A10K2.u4181 = [627019398483, 2612364240953, 3805028851395, 2160275906682, 372734215008, 10760911071, 0, 0, 0, 0] := by
  rw [show A10K2.u4181 = KTree.node A10K2.t4186 (nat_lit 68297996) (nat_lit 11466341189) (nat_lit 0) A10K2.t4187 from rfl, totK_node, tot4186, tot4187]
  decide +kernel

theorem arows4183 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4183 = true := by
  rw [show A10K2.u4183 = KTree.node A10K2.t4188 (nat_lit 68303189) (nat_lit 6950965519) (nat_lit 0) A10K2.t4189 from rfl, allE_node, rows4188, irow4183, rows4189]
  all_goals rfl

theorem atot4183 : totK PA10K2 A10K2.u4183 = [404407101374, 2102202998500, 3845138692009, 2672702336347, 572231691716, 31768748853, 0, 0, 0, 0] := by
  rw [show A10K2.u4183 = KTree.node A10K2.t4188 (nat_lit 68303189) (nat_lit 6950965519) (nat_lit 0) A10K2.t4189 from rfl, totK_node, tot4188, tot4189]
  decide +kernel

theorem arows4184 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4184 = true := by
  rw [show A10K2.u4184 = KTree.node A10K2.t4190 (nat_lit 68307798) (nat_lit 7980548004) (nat_lit 0) A10K2.t4191 from rfl, allE_node, rows4190, irow4184, rows4191]
  all_goals rfl

theorem atot4184 : totK PA10K2 A10K2.u4184 = [460446214129, 2661759452265, 4272497042195, 1916982500351, 167647991769, 0, 0, 0, 0, 0] := by
  rw [show A10K2.u4184 = KTree.node A10K2.t4190 (nat_lit 68307798) (nat_lit 7980548004) (nat_lit 0) A10K2.t4191 from rfl, totK_node, tot4190, tot4191]
  decide +kernel

theorem arows4189 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4189 = true := by
  rw [show A10K2.u4189 = KTree.node A10K2.t4192 (nat_lit 68323598) (nat_lit 9108338875) (nat_lit 0) A10K2.t4193 from rfl, allE_node, rows4192, irow4189, rows4193]
  all_goals rfl

theorem atot4189 : totK PA10K2 A10K2.u4189 = [0, 1036793140016, 3760964812940, 3813584393300, 982203207096, 45137667897, 0, 0, 0, 0] := by
  rw [show A10K2.u4189 = KTree.node A10K2.t4192 (nat_lit 68323598) (nat_lit 9108338875) (nat_lit 0) A10K2.t4193 from rfl, totK_node, tot4192, tot4193]
  decide +kernel

theorem arows4190 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4190 = true := by
  rw [show A10K2.u4190 = KTree.node A10K2.t4194 (nat_lit 68337712) (nat_lit 14676329589) (nat_lit 0) A10K2.t4195 from rfl, allE_node, rows4194, irow4190, rows4195]
  all_goals rfl

theorem atot4190 : totK PA10K2 A10K2.u4190 = [0, 903084749366, 3437164197033, 3908525819711, 1171752628815, 83707831423, 0, 0, 0, 0] := by
  rw [show A10K2.u4190 = KTree.node A10K2.t4194 (nat_lit 68337712) (nat_lit 14676329589) (nat_lit 0) A10K2.t4195 from rfl, totK_node, tot4194, tot4195]
  decide +kernel

theorem arows4192 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4192 = true := by
  rw [show A10K2.u4192 = KTree.node A10K2.t4196 (nat_lit 68343024) (nat_lit 259589464) (nat_lit 0) A10K2.t4197 from rfl, allE_node, rows4196, irow4192, rows4197]
  all_goals rfl

theorem atot4192 : totK PA10K2 A10K2.u4192 = [0, 622058145005, 2759749375959, 3901495347304, 1803746649796, 271677105452, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u4192 = KTree.node A10K2.t4196 (nat_lit 68343024) (nat_lit 259589464) (nat_lit 0) A10K2.t4197 from rfl, totK_node, tot4196, tot4197]
  decide +kernel

theorem arows4193 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4193 = true := by
  rw [show A10K2.u4193 = KTree.node A10K2.t4198 (nat_lit 68423052) (nat_lit 7922043605) (nat_lit 0) A10K2.t4199 from rfl, allE_node, rows4198, irow4193, rows4199]
  all_goals rfl

theorem atot4193 : totK PA10K2 A10K2.u4193 = [0, 517845628431, 2568846511259, 3965788962263, 2051787552983, 383017059753, 25371180993, 0, 0, 0] := by
  rw [show A10K2.u4193 = KTree.node A10K2.t4198 (nat_lit 68423052) (nat_lit 7922043605) (nat_lit 0) A10K2.t4199 from rfl, totK_node, tot4198, tot4199]
  decide +kernel

theorem arows4196 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4196 = true := by
  rw [show A10K2.u4196 = KTree.node A10K2.t4200 (nat_lit 68436324) (nat_lit 13775768551) (nat_lit 0) A10K2.t4201 from rfl, allE_node, rows4200, irow4196, rows4201]
  all_goals rfl

theorem atot4196 : totK PA10K2 A10K2.u4196 = [0, 673951267757, 2727139255548, 3847933176800, 1970712361255, 268464938618, 5447185874, 0, 0, 0] := by
  rw [show A10K2.u4196 = KTree.node A10K2.t4200 (nat_lit 68436324) (nat_lit 13775768551) (nat_lit 0) A10K2.t4201 from rfl, totK_node, tot4200, tot4201]
  decide +kernel

theorem arows4197 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4197 = true := by
  rw [show A10K2.u4197 = KTree.node A10K2.t4202 (nat_lit 68442280) (nat_lit 8804959660) (nat_lit 0) A10K2.t4203 from rfl, allE_node, rows4202, irow4197, rows4203]
  all_goals rfl

theorem atot4197 : totK PA10K2 A10K2.u4197 = [0, 429888743399, 2460667476063, 4170750178107, 2151609668141, 300094393860, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u4197 = KTree.node A10K2.t4202 (nat_lit 68442280) (nat_lit 8804959660) (nat_lit 0) A10K2.t4203 from rfl, totK_node, tot4202, tot4203]
  decide +kernel

theorem arows4199 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4199 = true := by
  rw [show A10K2.u4199 = KTree.node A10K2.t4204 (nat_lit 68449036) (nat_lit 11034608976) (nat_lit 0) A10K2.t4205 from rfl, allE_node, rows4204, irow4199, rows4205]
  all_goals rfl

theorem atot4199 : totK PA10K2 A10K2.u4199 = [0, 558339051073, 2607618980025, 4095372276315, 2274473989113, 333342421526, 6853348008, 0, 0, 0] := by
  rw [show A10K2.u4199 = KTree.node A10K2.t4204 (nat_lit 68449036) (nat_lit 11034608976) (nat_lit 0) A10K2.t4205 from rfl, totK_node, tot4204, tot4205]
  decide +kernel

theorem arows4200 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4200 = true := by
  rw [show A10K2.u4200 = KTree.node A10K2.t4206 (nat_lit 68498661) (nat_lit 6670153125) (nat_lit 0) A10K2.t4207 from rfl, allE_node, rows4206, irow4200, rows4207]
  all_goals rfl

theorem atot4200 : totK PA10K2 A10K2.u4200 = [0, 413295823201, 2240144749513, 3880356414374, 2590002413381, 548384520956, 31452573850, 0, 0, 0] := by
  rw [show A10K2.u4200 = KTree.node A10K2.t4206 (nat_lit 68498661) (nat_lit 6670153125) (nat_lit 0) A10K2.t4207 from rfl, totK_node, tot4206, tot4207]
  decide +kernel

theorem arows4204 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4204 = true := by
  rw [show A10K2.u4204 = KTree.node A10K2.t4208 (nat_lit 68503231) (nat_lit 10848443569) (nat_lit 0) A10K2.t4209 from rfl, allE_node, rows4208, irow4204, rows4209]
  all_goals rfl

theorem atot4204 : totK PA10K2 A10K2.u4204 = [0, 777370108884, 3245686216761, 4040727830922, 1504104337306, 133575032910, 0, 0, 0, 0] := by
  rw [show A10K2.u4204 = KTree.node A10K2.t4208 (nat_lit 68503231) (nat_lit 10848443569) (nat_lit 0) A10K2.t4209 from rfl, totK_node, tot4208, tot4209]
  decide +kernel

theorem arows4205 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4205 = true := by
  rw [show A10K2.u4205 = KTree.node A10K2.t4210 (nat_lit 68550981) (nat_lit 6847209463) (nat_lit 0) A10K2.t4211 from rfl, allE_node, rows4210, irow4205, rows4211]
  all_goals rfl

theorem atot4205 : totK PA10K2 A10K2.u4205 = [0, 685091111476, 2751770206119, 3886113873656, 1906919717133, 274153204740, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u4205 = KTree.node A10K2.t4210 (nat_lit 68550981) (nat_lit 6847209463) (nat_lit 0) A10K2.t4211 from rfl, totK_node, tot4210, tot4211]
  decide +kernel

theorem arows4207 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4207 = true := by
  rw [show A10K2.u4207 = KTree.node A10K2.t4212 (nat_lit 68556904) (nat_lit 12088476169) (nat_lit 0) A10K2.t4213 from rfl, allE_node, rows4212, irow4207, rows4213]
  all_goals rfl

theorem atot4207 : totK PA10K2 A10K2.u4207 = [0, 352831378081, 2114267238403, 3947694269412, 2525809736011, 476164571398, 30074883546, 0, 0, 0] := by
  rw [show A10K2.u4207 = KTree.node A10K2.t4212 (nat_lit 68556904) (nat_lit 12088476169) (nat_lit 0) A10K2.t4213 from rfl, totK_node, tot4212, tot4213]
  decide +kernel

theorem arows4208 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4208 = true := by
  rw [show A10K2.u4208 = KTree.node A10K2.t4214 (nat_lit 68564204) (nat_lit 11455311571) (nat_lit 0) A10K2.t4215 from rfl, allE_node, rows4214, irow4208, rows4215]
  all_goals rfl

theorem atot4208 : totK PA10K2 A10K2.u4208 = [0, 377659829977, 2186037380453, 3971299323707, 2493583939347, 477817493383, 31003444686, 0, 0, 0] := by
  rw [show A10K2.u4208 = KTree.node A10K2.t4214 (nat_lit 68564204) (nat_lit 11455311571) (nat_lit 0) A10K2.t4215 from rfl, totK_node, tot4214, tot4215]
  decide +kernel

theorem arows4211 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4211 = true := by
  rw [show A10K2.u4211 = KTree.node A10K2.t4216 (nat_lit 68568802) (nat_lit 13740511356) (nat_lit 0) A10K2.t4217 from rfl, allE_node, rows4216, irow4211, rows4217]
  all_goals rfl

theorem atot4211 : totK PA10K2 A10K2.u4211 = [0, 835897603759, 3302391395876, 3899450307887, 1314389645554, 100162055907, 0, 0, 0, 0] := by
  rw [show A10K2.u4211 = KTree.node A10K2.t4216 (nat_lit 68568802) (nat_lit 13740511356) (nat_lit 0) A10K2.t4217 from rfl, totK_node, tot4216, tot4217]
  decide +kernel

theorem arows4212 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4212 = true := by
  rw [show A10K2.u4212 = KTree.node A10K2.t4218 (nat_lit 68583680) (nat_lit 15049380543) (nat_lit 0) A10K2.t4219 from rfl, allE_node, rows4218, irow4212, rows4219]
  all_goals rfl

theorem atot4212 : totK PA10K2 A10K2.u4212 = [0, 0, 1162538084413, 3903922326770, 3413171848734, 747224473021, 37547833973, 0, 0, 0] := by
  rw [show A10K2.u4212 = KTree.node A10K2.t4218 (nat_lit 68583680) (nat_lit 15049380543) (nat_lit 0) A10K2.t4219 from rfl, totK_node, tot4218, tot4219]
  decide +kernel

theorem arows4214 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4214 = true := by
  rw [show A10K2.u4214 = KTree.node A10K2.t4220 (nat_lit 68593957) (nat_lit 7473897057) (nat_lit 0) A10K2.t4221 from rfl, allE_node, rows4220, irow4214, rows4221]
  all_goals rfl

theorem atot4214 : totK PA10K2 A10K2.u4214 = [0, 0, 1160479807655, 3867905511889, 3486329470485, 838195288859, 56346053544, 0, 0, 0] := by
  rw [show A10K2.u4214 = KTree.node A10K2.t4220 (nat_lit 68593957) (nat_lit 7473897057) (nat_lit 0) A10K2.t4221 from rfl, totK_node, tot4220, tot4221]
  decide +kernel

theorem arows4215 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4215 = true := by
  rw [show A10K2.u4215 = KTree.node A10K2.t4222 (nat_lit 68602730) (nat_lit 9078931481) (nat_lit 0) A10K2.t4223 from rfl, allE_node, rows4222, irow4215, rows4223]
  all_goals rfl

theorem atot4215 : totK PA10K2 A10K2.u4215 = [0, 0, 451885222873, 2580430984810, 4042092948066, 1828091649561, 199528122827, 0, 0, 0] := by
  rw [show A10K2.u4215 = KTree.node A10K2.t4222 (nat_lit 68602730) (nat_lit 9078931481) (nat_lit 0) A10K2.t4223 from rfl, totK_node, tot4222, tot4223]
  decide +kernel

theorem arows4222 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4222 = true := by
  rw [show A10K2.u4222 = KTree.node A10K2.t4224 (nat_lit 68684343) (nat_lit 13933339310) (nat_lit 0) A10K2.t4225 from rfl, allE_node, rows4224, irow4222, rows4225]
  all_goals rfl

theorem atot4222 : totK PA10K2 A10K2.u4222 = [842822735057, 3289402214160, 3914550371163, 1391859914733, 107992674505, 93840089069, 84918787380, 6354482628, 0, 0] := by
  rw [show A10K2.u4222 = KTree.node A10K2.t4224 (nat_lit 68684343) (nat_lit 13933339310) (nat_lit 0) A10K2.t4225 from rfl, totK_node, tot4224, tot4225]
  decide +kernel

theorem arows4223 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4223 = true := by
  rw [show A10K2.u4223 = KTree.node A10K2.t4226 (nat_lit 68689114) (nat_lit 10551123565) (nat_lit 0) A10K2.t4227 from rfl, allE_node, rows4226, irow4223, rows4227]
  all_goals rfl

theorem atot4223 : totK PA10K2 A10K2.u4223 = [559707398140, 2245002521036, 3699033468331, 2540064919041, 554364903354, 30831673886, 0, 0, 0, 0] := by
  rw [show A10K2.u4223 = KTree.node A10K2.t4226 (nat_lit 68689114) (nat_lit 10551123565) (nat_lit 0) A10K2.t4227 from rfl, totK_node, tot4226, tot4227]
  decide +kernel

theorem arows4225 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4225 = true := by
  rw [show A10K2.u4225 = KTree.node A10K2.t4228 (nat_lit 68705046) (nat_lit 3584909325) (nat_lit 0) A10K2.t4229 from rfl, allE_node, rows4228, irow4225, rows4229]
  all_goals rfl

theorem atot4225 : totK PA10K2 A10K2.u4225 = [486355993374, 2710441491328, 4222826434287, 2029865702847, 287489004006, 6354482628, 0, 0, 0, 0] := by
  rw [show A10K2.u4225 = KTree.node A10K2.t4228 (nat_lit 68705046) (nat_lit 3584909325) (nat_lit 0) A10K2.t4229 from rfl, totK_node, tot4228, tot4229]
  decide +kernel

theorem arows4226 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4226 = true := by
  rw [show A10K2.u4226 = KTree.node A10K2.t4230 (nat_lit 68710867) (nat_lit 8148536192) (nat_lit 0) A10K2.t4231 from rfl, allE_node, rows4230, irow4226, rows4231]
  all_goals rfl

theorem atot4226 : totK PA10K2 A10K2.u4226 = [316555443509, 1996020058230, 4189869463156, 3130115638154, 584870443649, 13814455608, 0, 0, 0, 0] := by
  rw [show A10K2.u4226 = KTree.node A10K2.t4230 (nat_lit 68710867) (nat_lit 8148536192) (nat_lit 0) A10K2.t4231 from rfl, totK_node, tot4230, tot4231]
  decide +kernel

theorem arows4229 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4229 = true := by
  rw [show A10K2.u4229 = KTree.node A10K2.t4232 (nat_lit 68716641) (nat_lit 9952831216) (nat_lit 0) A10K2.t4233 from rfl, allE_node, rows4232, irow4229, rows4233]
  all_goals rfl

theorem atot4229 : totK PA10K2 A10K2.u4229 = [0, 842335651861, 3358656998605, 4048116420762, 1405976500573, 109381178748, 0, 0, 0, 0] := by
  rw [show A10K2.u4229 = KTree.node A10K2.t4232 (nat_lit 68716641) (nat_lit 9952831216) (nat_lit 0) A10K2.t4233 from rfl, totK_node, tot4232, tot4233]
  decide +kernel

theorem arows4230 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4230 = true := by
  rw [show A10K2.u4230 = KTree.node A10K2.t4234 (nat_lit 68721493) (nat_lit 6064408592) (nat_lit 0) A10K2.t4235 from rfl, allE_node, rows4234, irow4230, rows4235]
  all_goals rfl

theorem atot4230 : totK PA10K2 A10K2.u4230 = [0, 418471038443, 2105977373646, 3776122320630, 2536369162351, 546121303300, 30650496230, 0, 0, 0] := by
  rw [show A10K2.u4230 = KTree.node A10K2.t4234 (nat_lit 68721493) (nat_lit 6064408592) (nat_lit 0) A10K2.t4235 from rfl, totK_node, tot4234, tot4235]
  decide +kernel

theorem arows4232 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4232 = true := by
  rw [show A10K2.u4232 = KTree.node A10K2.t4236 (nat_lit 68737543) (nat_lit 8302419463) (nat_lit 0) A10K2.t4237 from rfl, allE_node, rows4236, irow4232, rows4237]
  all_goals rfl

theorem atot4232 : totK PA10K2 A10K2.u4232 = [0, 625087059197, 2897098667937, 4099055538546, 1784571381815, 212991782732, 5546304973, 0, 0, 0] := by
  rw [show A10K2.u4232 = KTree.node A10K2.t4236 (nat_lit 68737543) (nat_lit 8302419463) (nat_lit 0) A10K2.t4237 from rfl, totK_node, tot4236, tot4237]
  decide +kernel

theorem arows4233 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4233 = true := by
  rw [show A10K2.u4233 = KTree.node A10K2.t4238 (nat_lit 68878732) (nat_lit 8743027510) (nat_lit 0) A10K2.t4239 from rfl, allE_node, rows4238, irow4233, rows4239]
  all_goals rfl

theorem atot4233 : totK PA10K2 A10K2.u4233 = [780629253406, 2790621834795, 3499741721400, 2161107697465, 679980720917, 57551169768, 0, 0, 0, 0] := by
  rw [show A10K2.u4233 = KTree.node A10K2.t4238 (nat_lit 68878732) (nat_lit 8743027510) (nat_lit 0) A10K2.t4239 from rfl, totK_node, tot4238, tot4239]
  decide +kernel

theorem arows4237 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4237 = true := by
  rw [show A10K2.u4237 = KTree.node A10K2.t4240 (nat_lit 68884515) (nat_lit 3465588263) (nat_lit 0) A10K2.t4241 from rfl, allE_node, rows4240, irow4237, rows4241]
  all_goals rfl

theorem atot4237 : totK PA10K2 A10K2.u4237 = [287747644888, 2031221855320, 4121116467811, 2821122771568, 575492865006, 30749153377, 0, 0, 0, 0] := by
  rw [show A10K2.u4237 = KTree.node A10K2.t4240 (nat_lit 68884515) (nat_lit 3465588263) (nat_lit 0) A10K2.t4241 from rfl, totK_node, tot4240, tot4241]
  decide +kernel

theorem arows4238 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4238 = true := by
  rw [show A10K2.u4238 = KTree.node A10K2.t4242 (nat_lit 68891931) (nat_lit 10054382329) (nat_lit 0) A10K2.t4243 from rfl, allE_node, rows4242, irow4238, rows4243]
  all_goals rfl

theorem atot4238 : totK PA10K2 A10K2.u4238 = [589692706676, 2544700737029, 4027320813666, 2491243334283, 466130497210, 25580784005, 0, 0, 0, 0] := by
  rw [show A10K2.u4238 = KTree.node A10K2.t4242 (nat_lit 68891931) (nat_lit 10054382329) (nat_lit 0) A10K2.t4243 from rfl, totK_node, tot4242, tot4243]
  decide +kernel

theorem arows4240 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4240 = true := by
  rw [show A10K2.u4240 = KTree.node A10K2.t4244 (nat_lit 68906195) (nat_lit 10663384502) (nat_lit 0) A10K2.t4245 from rfl, allE_node, rows4244, irow4240, rows4245]
  all_goals rfl

theorem atot4240 : totK PA10K2 A10K2.u4240 = [585790443428, 2816781468408, 4223144217194, 2053246070888, 294594402618, 6853348008, 0, 0, 0, 0] := by
  rw [show A10K2.u4240 = KTree.node A10K2.t4244 (nat_lit 68906195) (nat_lit 10663384502) (nat_lit 0) A10K2.t4245 from rfl, totK_node, tot4244, tot4245]
  decide +kernel

theorem arows4241 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4241 = true := by
  rw [show A10K2.u4241 = KTree.node A10K2.t4246 (nat_lit 68910743) (nat_lit 14036657062) (nat_lit 0) A10K2.t4247 from rfl, allE_node, rows4246, irow4241, rows4247]
  all_goals rfl

theorem atot4241 : totK PA10K2 A10K2.u4241 = [0, 1057615284158, 3720546137746, 3906160228952, 1189550189068, 81606090030, 0, 0, 0, 0] := by
  rw [show A10K2.u4241 = KTree.node A10K2.t4246 (nat_lit 68910743) (nat_lit 14036657062) (nat_lit 0) A10K2.t4247 from rfl, totK_node, tot4246, tot4247]
  decide +kernel

theorem arows4244 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4244 = true := by
  rw [show A10K2.u4244 = KTree.node A10K2.t4248 (nat_lit 68915492) (nat_lit 12820342406) (nat_lit 0) A10K2.t4249 from rfl, allE_node, rows4248, irow4244, rows4249]
  all_goals rfl

theorem atot4244 : totK PA10K2 A10K2.u4244 = [0, 417606414120, 2396972955790, 4266049724149, 2400999230431, 341679780790, 6904928264, 0, 0, 0] := by
  rw [show A10K2.u4244 = KTree.node A10K2.t4248 (nat_lit 68915492) (nat_lit 12820342406) (nat_lit 0) A10K2.t4249 from rfl, totK_node, tot4248, tot4249]
  decide +kernel

theorem arows4245 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4245 = true := by
  rw [show A10K2.u4245 = KTree.node A10K2.t4250 (nat_lit 68923282) (nat_lit 15204535253) (nat_lit 0) A10K2.t4251 from rfl, allE_node, rows4250, irow4245, rows4251]
  all_goals rfl

theorem atot4245 : totK PA10K2 A10K2.u4245 = [0, 549592972424, 2619326479101, 4200756204801, 2432185134909, 353317075121, 7047025452, 0, 0, 0] := by
  rw [show A10K2.u4245 = KTree.node A10K2.t4250 (nat_lit 68923282) (nat_lit 15204535253) (nat_lit 0) A10K2.t4251 from rfl, totK_node, tot4250, tot4251]
  decide +kernel

theorem arows4247 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4247 = true := by
  rw [show A10K2.u4247 = KTree.node A10K2.t4252 (nat_lit 68937654) (nat_lit 16799536538) (nat_lit 0) A10K2.t4253 from rfl, allE_node, rows4252, irow4247, rows4253]
  all_goals rfl

theorem atot4247 : totK PA10K2 A10K2.u4247 = [0, 799109534873, 3352020000371, 4204519224282, 1514738721087, 93017162919, 0, 0, 0, 0] := by
  rw [show A10K2.u4247 = KTree.node A10K2.t4252 (nat_lit 68937654) (nat_lit 16799536538) (nat_lit 0) A10K2.t4253 from rfl, totK_node, tot4252, tot4253]
  decide +kernel

theorem arows4248 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4248 = true := by
  rw [show A10K2.u4248 = KTree.node A10K2.t4254 (nat_lit 68943305) (nat_lit 6453621258) (nat_lit 0) A10K2.t4255 from rfl, allE_node, rows4254, irow4248, rows4255]
  all_goals rfl

theorem atot4248 : totK PA10K2 A10K2.u4248 = [0, 315335427872, 1685130098010, 3576832460333, 3251257961237, 925453115492, 61110126106, 0, 0, 0] := by
  rw [show A10K2.u4248 = KTree.node A10K2.t4254 (nat_lit 68943305) (nat_lit 6453621258) (nat_lit 0) A10K2.t4255 from rfl, totK_node, tot4254, tot4255]
  decide +kernel

theorem arows4253 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4253 = true := by
  rw [show A10K2.u4253 = KTree.node A10K2.t4256 (nat_lit 68947859) (nat_lit 8389577289) (nat_lit 0) A10K2.t4257 from rfl, allE_node, rows4256, irow4253, rows4257]
  all_goals rfl

theorem atot4253 : totK PA10K2 A10K2.u4253 = [0, 527487307185, 2504379663204, 3951110013949, 2188950651183, 419505300993, 25333254304, 0, 0, 0] := by
  rw [show A10K2.u4253 = KTree.node A10K2.t4256 (nat_lit 68947859) (nat_lit 8389577289) (nat_lit 0) A10K2.t4257 from rfl, totK_node, tot4256, tot4257]
  decide +kernel

theorem arows4254 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4254 = true := by
  rw [show A10K2.u4254 = KTree.node A10K2.t4258 (nat_lit 68961068) (nat_lit 13235443842) (nat_lit 0) A10K2.t4259 from rfl, allE_node, rows4258, irow4254, rows4259]
  all_goals rfl

theorem atot4254 : totK PA10K2 A10K2.u4254 = [0, 559707398140, 2714531092538, 4088782493317, 1996013393753, 266107564478, 5447185874, 0, 0, 0] := by
  rw [show A10K2.u4254 = KTree.node A10K2.t4258 (nat_lit 68961068) (nat_lit 13235443842) (nat_lit 0) A10K2.t4259 from rfl, totK_node, tot4258, tot4259]
  decide +kernel

theorem arows4256 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4256 = true := by
  rw [show A10K2.u4256 = KTree.node A10K2.t4260 (nat_lit 68969630) (nat_lit 14941068844) (nat_lit 0) A10K2.t4261 from rfl, allE_node, rows4260, irow4256, rows4261]
  all_goals rfl

theorem atot4256 : totK PA10K2 A10K2.u4256 = [0, 802911436883, 3117822872305, 4019048137479, 1771603641413, 202746475987, 5705019915, 0, 0, 0] := by
  rw [show A10K2.u4256 = KTree.node A10K2.t4260 (nat_lit 68969630) (nat_lit 14941068844) (nat_lit 0) A10K2.t4261 from rfl, totK_node, tot4260, tot4261]
  decide +kernel

theorem arows4257 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4257 = true := by
  rw [show A10K2.u4257 = KTree.node A10K2.t4262 (nat_lit 68975713) (nat_lit 9681585294) (nat_lit 0) A10K2.t4263 from rfl, allE_node, rows4262, irow4257, rows4263]
  all_goals rfl

theorem atot4257 : totK PA10K2 A10K2.u4257 = [0, 0, 1113817249467, 3890140973101, 3940949309512, 1076451616075, 62351816811, 0, 0, 0] := by
  rw [show A10K2.u4257 = KTree.node A10K2.t4262 (nat_lit 68975713) (nat_lit 9681585294) (nat_lit 0) A10K2.t4263 from rfl, totK_node, tot4262, tot4263]
  decide +kernel

theorem arows4260 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4260 = true := by
  rw [show A10K2.u4260 = KTree.node A10K2.t4264 (nat_lit 68980228) (nat_lit 10621626163) (nat_lit 0) A10K2.t4265 from rfl, allE_node, rows4264, irow4260, rows4265]
  all_goals rfl

theorem atot4260 : totK PA10K2 A10K2.u4260 = [0, 0, 526111769267, 2646054736949, 4066936934414, 1991645817619, 291179317473, 7007974415, 0, 0] := by
  rw [show A10K2.u4260 = KTree.node A10K2.t4264 (nat_lit 68980228) (nat_lit 10621626163) (nat_lit 0) A10K2.t4265 from rfl, totK_node, tot4264, tot4265]
  decide +kernel

theorem arows4261 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4261 = true := by
  rw [show A10K2.u4261 = KTree.node A10K2.t4266 (nat_lit 68995299) (nat_lit 9417782808) (nat_lit 0) A10K2.t4267 from rfl, allE_node, rows4266, irow4261, rows4267]
  all_goals rfl

theorem atot4261 : totK PA10K2 A10K2.u4261 = [0, 0, 996615881793, 3682530394099, 3887208487193, 1065423033128, 60624848455, 0, 0, 0] := by
  rw [show A10K2.u4261 = KTree.node A10K2.t4266 (nat_lit 68995299) (nat_lit 9417782808) (nat_lit 0) A10K2.t4267 from rfl, totK_node, tot4266, tot4267]
  decide +kernel

theorem arows4263 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4263 = true := by
  rw [show A10K2.u4263 = KTree.node A10K2.t4268 (nat_lit 69140556) (nat_lit 10714686665) (nat_lit 0) A10K2.t4269 from rfl, allE_node, rows4268, irow4263, rows4269]
  all_goals rfl

theorem atot4263 : totK PA10K2 A10K2.u4263 = [0, 661091236459, 2545615893340, 3519365291472, 2440814186834, 758201377932, 56820615133, 0, 0, 0] := by
  rw [show A10K2.u4263 = KTree.node A10K2.t4268 (nat_lit 69140556) (nat_lit 10714686665) (nat_lit 0) A10K2.t4269 from rfl, totK_node, tot4268, tot4269]
  decide +kernel

theorem arows4264 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4264 = true := by
  rw [show A10K2.u4264 = KTree.node A10K2.t4270 (nat_lit 69145440) (nat_lit 12571607869) (nat_lit 0) A10K2.t4271 from rfl, allE_node, rows4270, irow4264, rows4271]
  all_goals rfl

theorem atot4264 : totK PA10K2 A10K2.u4264 = [0, 407285661835, 2217340312357, 4115382016136, 2699780514417, 466620807111, 11991740650, 0, 0, 0] := by
  rw [show A10K2.u4264 = KTree.node A10K2.t4270 (nat_lit 69145440) (nat_lit 12571607869) (nat_lit 0) A10K2.t4271 from rfl, totK_node, tot4270, tot4271]
  decide +kernel

theorem arows4268 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4268 = true := by
  rw [show A10K2.u4268 = KTree.node A10K2.t4272 (nat_lit 69154010) (nat_lit 14159968836) (nat_lit 0) A10K2.t4273 from rfl, allE_node, rows4272, irow4268, rows4273]
  all_goals rfl

theorem atot4268 : totK PA10K2 A10K2.u4268 = [0, 513590289165, 2498291417069, 4125342861314, 2499266689916, 435434445646, 12219140272, 0, 0, 0] := by
  rw [show A10K2.u4268 = KTree.node A10K2.t4272 (nat_lit 69154010) (nat_lit 14159968836) (nat_lit 0) A10K2.t4273 from rfl, totK_node, tot4272, tot4273]
  decide +kernel

theorem arows4269 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4269 = true := by
  rw [show A10K2.u4269 = KTree.node A10K2.t4274 (nat_lit 69168290) (nat_lit 13672110144) (nat_lit 0) A10K2.t4275 from rfl, allE_node, rows4274, irow4269, rows4275]
  all_goals rfl

theorem atot4269 : totK PA10K2 A10K2.u4269 = [0, 660402593777, 2974350170959, 4181259354328, 1941855132992, 259239946066, 6772895877, 0, 0, 0] := by
  rw [show A10K2.u4269 = KTree.node A10K2.t4274 (nat_lit 69168290) (nat_lit 13672110144) (nat_lit 0) A10K2.t4275 from rfl, totK_node, tot4274, tot4275]
  decide +kernel

theorem arows4271 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4271 = true := by
  rw [show A10K2.u4271 = KTree.node A10K2.t4276 (nat_lit 69172809) (nat_lit 5892831899) (nat_lit 0) A10K2.t4277 from rfl, allE_node, rows4276, irow4271, rows4277]
  all_goals rfl

theorem atot4271 : totK PA10K2 A10K2.u4271 = [0, 0, 1055881760462, 3724932002131, 3951019297233, 1138492378245, 68058142506, 0, 0, 0] := by
  rw [show A10K2.u4271 = KTree.node A10K2.t4276 (nat_lit 69172809) (nat_lit 5892831899) (nat_lit 0) A10K2.t4277 from rfl, totK_node, tot4276, tot4277]
  decide +kernel

theorem arows4272 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4272 = true := by
  rw [show A10K2.u4272 = KTree.node A10K2.t4278 (nat_lit 69177751) (nat_lit 14054900208) (nat_lit 0) A10K2.t4279 from rfl, allE_node, rows4278, irow4272, rows4279]
  all_goals rfl

theorem atot4272 : totK PA10K2 A10K2.u4272 = [0, 0, 591518098900, 2755262311271, 4154815643343, 2100093155805, 272646473745, 6318667960, 0, 0] := by
  rw [show A10K2.u4272 = KTree.node A10K2.t4278 (nat_lit 69177751) (nat_lit 14054900208) (nat_lit 0) A10K2.t4279 from rfl, totK_node, tot4278, tot4279]
  decide +kernel

theorem arows4275 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4275 = true := by
  rw [show A10K2.u4275 = KTree.node A10K2.t4280 (nat_lit 69186730) (nat_lit 12897075240) (nat_lit 0) A10K2.t4281 from rfl, allE_node, rows4280, irow4275, rows4281]
  all_goals rfl

theorem atot4275 : totK PA10K2 A10K2.u4275 = [0, 0, 540300439896, 2630960566543, 4201536794312, 2316396723139, 289377391356, 6439430839, 0, 0] := by
  rw [show A10K2.u4275 = KTree.node A10K2.t4280 (nat_lit 69186730) (nat_lit 12897075240) (nat_lit 0) A10K2.t4281 from rfl, totK_node, tot4280, tot4281]
  decide +kernel

theorem arows4276 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4276 = true := by
  rw [show A10K2.u4276 = KTree.node A10K2.t4282 (nat_lit 69201083) (nat_lit 7104203533) (nat_lit 0) A10K2.t4283 from rfl, allE_node, rows4282, irow4276, rows4283]
  all_goals rfl

theorem atot4276 : totK PA10K2 A10K2.u4276 = [0, 0, 612685603386, 2883910132274, 4179366559814, 1903142794058, 230405511103, 6021244195, 0, 0] := by
  rw [show A10K2.u4276 = KTree.node A10K2.t4282 (nat_lit 69201083) (nat_lit 7104203533) (nat_lit 0) A10K2.t4283 from rfl, totK_node, tot4282, tot4283]
  decide +kernel

theorem arows4278 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4278 = true := by
  rw [show A10K2.u4278 = KTree.node A10K2.t4284 (nat_lit 69205686) (nat_lit 16480875036) (nat_lit 0) A10K2.t4285 from rfl, allE_node, rows4284, irow4278, rows4285]
  all_goals rfl

theorem atot4278 : totK PA10K2 A10K2.u4278 = [0, 480036688775, 1560508115056, 2063764513507, 2526698232585, 2376795444949, 752892461066, 54997142734, 0, 0] := by
  rw [show A10K2.u4278 = KTree.node A10K2.t4284 (nat_lit 69205686) (nat_lit 16480875036) (nat_lit 0) A10K2.t4285 from rfl, totK_node, tot4284, tot4285]
  decide +kernel

theorem arows4279 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4279 = true := by
  rw [show A10K2.u4279 = KTree.node A10K2.t4286 (nat_lit 69210145) (nat_lit 10204605750) (nat_lit 0) A10K2.t4287 from rfl, allE_node, rows4286, irow4279, rows4287]
  all_goals rfl

theorem atot4279 : totK PA10K2 A10K2.u4279 = [0, 388985532535, 2183003469441, 3996280433767, 2493400802711, 467016218202, 25371180993, 0, 0, 0] := by
  rw [show A10K2.u4279 = KTree.node A10K2.t4286 (nat_lit 69210145) (nat_lit 10204605750) (nat_lit 0) A10K2.t4287 from rfl, totK_node, tot4286, tot4287]
  decide +kernel

theorem arows4285 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4285 = true := by
  rw [show A10K2.u4285 = KTree.node A10K2.t4288 (nat_lit 69223581) (nat_lit 5933400506) (nat_lit 0) A10K2.t4289 from rfl, allE_node, rows4288, irow4285, rows4289]
  all_goals rfl

theorem atot4285 : totK PA10K2 A10K2.u4285 = [0, 724326080113, 3024763253188, 3856470537115, 1605234763246, 198640528161, 5460492893, 0, 0, 0] := by
  rw [show A10K2.u4285 = KTree.node A10K2.t4288 (nat_lit 69223581) (nat_lit 5933400506) (nat_lit 0) A10K2.t4289 from rfl, totK_node, tot4288, tot4289]
  decide +kernel

theorem arows4286 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4286 = true := by
  rw [show A10K2.u4286 = KTree.node A10K2.t4290 (nat_lit 69230700) (nat_lit 11154945081) (nat_lit 0) A10K2.t4291 from rfl, allE_node, rows4290, irow4286, rows4291]
  all_goals rfl

theorem atot4286 : totK PA10K2 A10K2.u4286 = [0, 695776054514, 2822939064321, 3901830565512, 1848483483741, 233097506400, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u4286 = KTree.node A10K2.t4290 (nat_lit 69230700) (nat_lit 11154945081) (nat_lit 0) A10K2.t4291 from rfl, totK_node, tot4290, tot4291]
  decide +kernel

theorem arows4288 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4288 = true := by
  rw [show A10K2.u4288 = KTree.node A10K2.t4292 (nat_lit 69235954) (nat_lit 12186885809) (nat_lit 0) A10K2.t4293 from rfl, allE_node, rows4292, irow4288, rows4293]
  all_goals rfl

theorem atot4288 : totK PA10K2 A10K2.u4288 = [0, 31409270183, 1352804769113, 3970614804955, 3555037419098, 928960224599, 47398443899, 0, 0, 0] := by
  rw [show A10K2.u4288 = KTree.node A10K2.t4292 (nat_lit 69235954) (nat_lit 12186885809) (nat_lit 0) A10K2.t4293 from rfl, totK_node, tot4292, tot4293]
  decide +kernel

theorem arows4289 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4289 = true := by
  rw [show A10K2.u4289 = KTree.node A10K2.t4294 (nat_lit 69241669) (nat_lit 6570204875) (nat_lit 0) A10K2.t4295 from rfl, allE_node, rows4294, irow4289, rows4295]
  all_goals rfl

theorem atot4289 : totK PA10K2 A10K2.u4289 = [0, 0, 747041219070, 3206709051718, 4064051549800, 1489279473255, 129738228029, 0, 0, 0] := by
  rw [show A10K2.u4289 = KTree.node A10K2.t4294 (nat_lit 69241669) (nat_lit 6570204875) (nat_lit 0) A10K2.t4295 from rfl, totK_node, tot4294, tot4295]
  decide +kernel

theorem arows4292 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4292 = true := by
  rw [show A10K2.u4292 = KTree.node A10K2.t4296 (nat_lit 69255200) (nat_lit 14200915603) (nat_lit 0) A10K2.t4297 from rfl, allE_node, rows4296, irow4292, rows4297]
  all_goals rfl

theorem atot4292 : totK PA10K2 A10K2.u4292 = [0, 0, 572198776846, 2455989167169, 3632203743376, 2117667659597, 482517304736, 30650496230, 0, 0] := by
  rw [show A10K2.u4292 = KTree.node A10K2.t4296 (nat_lit 69255200) (nat_lit 14200915603) (nat_lit 0) A10K2.t4297 from rfl, totK_node, tot4296, tot4297]
  decide +kernel

theorem arows4293 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4293 = true := by
  rw [show A10K2.u4293 = KTree.node A10K2.t4298 (nat_lit 69261482) (nat_lit 11333891240) (nat_lit 0) A10K2.t4299 from rfl, allE_node, rows4298, irow4293, rows4299]
  all_goals rfl

theorem atot4293 : totK PA10K2 A10K2.u4293 = [0, 0, 578579977166, 2739122587567, 4004206055639, 1734681793859, 219178372242, 5546304973, 0, 0] := by
  rw [show A10K2.u4293 = KTree.node A10K2.t4298 (nat_lit 69261482) (nat_lit 11333891240) (nat_lit 0) A10K2.t4299 from rfl, totK_node, tot4298, tot4299]
  decide +kernel

theorem arows4295 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4295 = true := by
  rw [show A10K2.u4295 = KTree.node A10K2.t4300 (nat_lit 69337372) (nat_lit 11520834563) (nat_lit 0) A10K2.t4301 from rfl, allE_node, rows4300, irow4295, rows4301]
  all_goals rfl

theorem atot4295 : totK PA10K2 A10K2.u4295 = [0, 623307060090, 2475234511169, 3570286079793, 2328812668097, 660396350952, 41737205306, 0, 0, 0] := by
  rw [show A10K2.u4295 = KTree.node A10K2.t4300 (nat_lit 69337372) (nat_lit 11520834563) (nat_lit 0) A10K2.t4301 from rfl, totK_node, tot4300, tot4301]
  decide +kernel

theorem arows4296 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4296 = true := by
  rw [show A10K2.u4296 = KTree.node A10K2.t4302 (nat_lit 69342080) (nat_lit 15343150485) (nat_lit 0) A10K2.t4303 from rfl, allE_node, rows4302, irow4296, rows4303]
  all_goals rfl

theorem atot4296 : totK PA10K2 A10K2.u4296 = [0, 374785640413, 2044163067416, 3909205842474, 2797163530560, 585096910331, 30831673886, 0, 0, 0] := by
  rw [show A10K2.u4296 = KTree.node A10K2.t4302 (nat_lit 69342080) (nat_lit 15343150485) (nat_lit 0) A10K2.t4303 from rfl, totK_node, tot4302, tot4303]
  decide +kernel

theorem arows4300 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4300 = true := by
  rw [show A10K2.u4300 = KTree.node A10K2.t4304 (nat_lit 69351594) (nat_lit 12841543123) (nat_lit 0) A10K2.t4305 from rfl, allE_node, rows4304, irow4300, rows4305]
  all_goals rfl

theorem atot4300 : totK PA10K2 A10K2.u4300 = [0, 635408562031, 2784392214780, 3981927265914, 1841648634511, 233890723394, 6034215561, 0, 0, 0] := by
  rw [show A10K2.u4300 = KTree.node A10K2.t4304 (nat_lit 69351594) (nat_lit 12841543123) (nat_lit 0) A10K2.t4305 from rfl, totK_node, tot4304, tot4305]
  decide +kernel

theorem arows4301 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4301 = true := by
  rw [show A10K2.u4301 = KTree.node A10K2.t4306 (nat_lit 69357577) (nat_lit 9802626900) (nat_lit 0) A10K2.t4307 from rfl, allE_node, rows4306, irow4301, rows4307]
  all_goals rfl

theorem atot4301 : totK PA10K2 A10K2.u4301 = [0, 421076849351, 2481831987621, 4145055089703, 1963468375825, 194995651311, 0, 0, 0, 0] := by
  rw [show A10K2.u4301 = KTree.node A10K2.t4306 (nat_lit 69357577) (nat_lit 9802626900) (nat_lit 0) A10K2.t4307 from rfl, totK_node, tot4306, tot4307]
  decide +kernel

theorem arows4303 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4303 = true := by
  rw [show A10K2.u4303 = KTree.node A10K2.t4308 (nat_lit 69372268) (nat_lit 12762111464) (nat_lit 0) A10K2.t4309 from rfl, allE_node, rows4308, irow4303, rows4309]
  all_goals rfl

theorem atot4303 : totK PA10K2 A10K2.u4303 = [0, 0, 1030936605296, 3701520955298, 3907556977242, 1017319134525, 50664460339, 0, 0, 0] := by
  rw [show A10K2.u4303 = KTree.node A10K2.t4308 (nat_lit 69372268) (nat_lit 12762111464) (nat_lit 0) A10K2.t4309 from rfl, totK_node, tot4308, tot4309]
  decide +kernel

theorem arows4304 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4304 = true := by
  rw [show A10K2.u4304 = KTree.node A10K2.t4310 (nat_lit 69387107) (nat_lit 5130200643) (nat_lit 0) A10K2.t4311 from rfl, allE_node, rows4310, irow4304, rows4311]
  all_goals rfl

theorem atot4304 : totK PA10K2 A10K2.u4304 = [0, 0, 1014368416322, 3757659609008, 3681590291404, 803743936716, 36992254861, 0, 0, 0] := by
  rw [show A10K2.u4304 = KTree.node A10K2.t4310 (nat_lit 69387107) (nat_lit 5130200643) (nat_lit 0) A10K2.t4311 from rfl, totK_node, tot4310, tot4311]
  decide +kernel

theorem arows4307 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4307 = true := by
  rw [show A10K2.u4307 = KTree.node A10K2.t4312 (nat_lit 69402657) (nat_lit 10204605750) (nat_lit 0) A10K2.t4313 from rfl, allE_node, rows4312, irow4307, rows4313]
  all_goals rfl

theorem atot4307 : totK PA10K2 A10K2.u4307 = [0, 577697119681, 1948718994248, 2725027257983, 2668826556661, 1327184038252, 193534632719, 5976421810, 0, 0] := by
  rw [show A10K2.u4307 = KTree.node A10K2.t4312 (nat_lit 69402657) (nat_lit 10204605750) (nat_lit 0) A10K2.t4313 from rfl, totK_node, tot4312, tot4313]
  decide +kernel

theorem arows4308 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4308 = true := by
  rw [show A10K2.u4308 = KTree.node A10K2.t4314 (nat_lit 69407269) (nat_lit 6572684471) (nat_lit 0) A10K2.t4315 from rfl, allE_node, rows4314, irow4308, rows4315]
  all_goals rfl

theorem atot4308 : totK PA10K2 A10K2.u4308 = [0, 312613731607, 1979843148306, 4022527779211, 2848904857789, 591052638692, 30810868011, 0, 0, 0] := by
  rw [show A10K2.u4308 = KTree.node A10K2.t4314 (nat_lit 69407269) (nat_lit 6572684471) (nat_lit 0) A10K2.t4315 from rfl, totK_node, tot4314, tot4315]
  decide +kernel

theorem arows4310 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4310 = true := by
  rw [show A10K2.u4310 = KTree.node A10K2.t4316 (nat_lit 69427489) (nat_lit 9867997345) (nat_lit 0) A10K2.t4317 from rfl, allE_node, rows4316, irow4310, rows4317]
  all_goals rfl

theorem atot4310 : totK PA10K2 A10K2.u4310 = [0, 889709205299, 3440199777708, 4133134905100, 1606296711960, 146678996887, 0, 0, 0, 0] := by
  rw [show A10K2.u4310 = KTree.node A10K2.t4316 (nat_lit 69427489) (nat_lit 9867997345) (nat_lit 0) A10K2.t4317 from rfl, totK_node, tot4316, tot4317]
  decide +kernel

theorem arows4311 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4311 = true := by
  rw [show A10K2.u4311 = KTree.node A10K2.t4318 (nat_lit 69432251) (nat_lit 5983504955) (nat_lit 0) A10K2.t4319 from rfl, allE_node, rows4318, irow4311, rows4319]
  all_goals rfl

theorem atot4311 : totK PA10K2 A10K2.u4311 = [0, 100137355278, 1431189967084, 4003777352577, 3649387267287, 879626179968, 25401055518, 0, 0, 0] := by
  rw [show A10K2.u4311 = KTree.node A10K2.t4318 (nat_lit 69432251) (nat_lit 5983504955) (nat_lit 0) A10K2.t4319 from rfl, totK_node, tot4318, tot4319]
  decide +kernel

theorem arows4316 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4316 = true := by
  rw [show A10K2.u4316 = KTree.node A10K2.t4320 (nat_lit 69438252) (nat_lit 13298561068) (nat_lit 0) A10K2.t4321 from rfl, allE_node, rows4320, irow4316, rows4321]
  all_goals rfl

theorem atot4316 : totK PA10K2 A10K2.u4316 = [0, 0, 808481376521, 3259703500103, 4028350515628, 1570453916106, 130269414368, 0, 0, 0] := by
  rw [show A10K2.u4316 = KTree.node A10K2.t4320 (nat_lit 69438252) (nat_lit 13298561068) (nat_lit 0) A10K2.t4321 from rfl, totK_node, tot4320, tot4321]
  decide +kernel

theorem arows4317 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4317 = true := by
  rw [show A10K2.u4317 = KTree.node A10K2.t4322 (nat_lit 69447098) (nat_lit 14470741792) (nat_lit 0) A10K2.t4323 from rfl, allE_node, rows4322, irow4317, rows4323]
  all_goals rfl

theorem atot4317 : totK PA10K2 A10K2.u4317 = [0, 0, 648905583915, 2758110029283, 4095093856893, 2172691172405, 305974397718, 6904928264, 0, 0] := by
  rw [show A10K2.u4317 = KTree.node A10K2.t4322 (nat_lit 69447098) (nat_lit 14470741792) (nat_lit 0) A10K2.t4323 from rfl, totK_node, tot4322, tot4323]
  decide +kernel

theorem arows4319 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4319 = true := by
  rw [show A10K2.u4319 = KTree.node A10K2.t4324 (nat_lit 69464065) (nat_lit 10590452259) (nat_lit 0) A10K2.t4325 from rfl, allE_node, rows4324, irow4319, rows4325]
  all_goals rfl

theorem atot4319 : totK PA10K2 A10K2.u4319 = [0, 0, 428345324975, 2484840981000, 4286249392789, 2462960111972, 316959984569, 6066958478, 0, 0] := by
  rw [show A10K2.u4319 = KTree.node A10K2.t4324 (nat_lit 69464065) (nat_lit 10590452259) (nat_lit 0) A10K2.t4325 from rfl, totK_node, tot4324, tot4325]
  decide +kernel

theorem arows4320 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4320 = true := by
  rw [show A10K2.u4320 = KTree.node A10K2.t4326 (nat_lit 69470307) (nat_lit 4926984521) (nat_lit 0) A10K2.t4327 from rfl, allE_node, rows4326, irow4320, rows4327]
  all_goals rfl

theorem atot4320 : totK PA10K2 A10K2.u4320 = [0, 0, 863930406233, 3142349619444, 3656495560636, 1616796708224, 385417755328, 28503589898, 0, 0] := by
  rw [show A10K2.u4320 = KTree.node A10K2.t4326 (nat_lit 69470307) (nat_lit 4926984521) (nat_lit 0) A10K2.t4327 from rfl, totK_node, tot4326, tot4327]
  decide +kernel

theorem arows4323 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4323 = true := by
  rw [show A10K2.u4323 = KTree.node A10K2.t4328 (nat_lit 69474976) (nat_lit 8696692861) (nat_lit 0) A10K2.t4329 from rfl, allE_node, rows4328, irow4323, rows4329]
  all_goals rfl

theorem atot4323 : totK PA10K2 A10K2.u4323 = [0, 0, 292562553233, 1905057795159, 3937914516945, 2764035996317, 588525307281, 30831673886, 0, 0] := by
  rw [show A10K2.u4323 = KTree.node A10K2.t4328 (nat_lit 69474976) (nat_lit 8696692861) (nat_lit 0) A10K2.t4329 from rfl, totK_node, tot4328, tot4329]
  decide +kernel

theorem arows4324 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4324 = true := by
  rw [show A10K2.u4324 = KTree.node A10K2.t4330 (nat_lit 69488903) (nat_lit 9718756484) (nat_lit 0) A10K2.t4331 from rfl, allE_node, rows4330, irow4324, rows4331]
  all_goals rfl

theorem atot4324 : totK PA10K2 A10K2.u4324 = [0, 0, 583339814238, 2631124050066, 3855255773437, 1729735409993, 211284875787, 5705019915, 0, 0] := by
  rw [show A10K2.u4324 = KTree.node A10K2.t4330 (nat_lit 69488903) (nat_lit 9718756484) (nat_lit 0) A10K2.t4331 from rfl, totK_node, tot4330, tot4331]
  decide +kernel

theorem arows4326 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4326 = true := by
  rw [show A10K2.u4326 = KTree.node A10K2.t4332 (nat_lit 69496313) (nat_lit 6315597177) (nat_lit 0) A10K2.t4333 from rfl, allE_node, rows4332, irow4326, rows4333]
  all_goals rfl

theorem atot4326 : totK PA10K2 A10K2.u4326 = [0, 0, 586772247909, 2780487986191, 4143014690464, 2124395556938, 311993985934, 6853348008, 0, 0] := by
  rw [show A10K2.u4326 = KTree.node A10K2.t4332 (nat_lit 69496313) (nat_lit 6315597177) (nat_lit 0) A10K2.t4333 from rfl, totK_node, tot4332, tot4333]
  decide +kernel

theorem arows4327 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4327 = true := by
  rw [show A10K2.u4327 = KTree.node A10K2.t4334 (nat_lit 69501517) (nat_lit 5408701773) (nat_lit 0) A10K2.t4335 from rfl, allE_node, rows4334, irow4327, rows4335]
  all_goals rfl

theorem atot4327 : totK PA10K2 A10K2.u4327 = [0, 0, 0, 1109519281418, 3872033306457, 3600337955934, 894470556282, 59400237386, 0, 0] := by
  rw [show A10K2.u4327 = KTree.node A10K2.t4334 (nat_lit 69501517) (nat_lit 5408701773) (nat_lit 0) A10K2.t4335 from rfl, totK_node, tot4334, tot4335]
  decide +kernel

theorem arows4331 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4331 = true := by
  rw [show A10K2.u4331 = KTree.node A10K2.t4336 (nat_lit 69507282) (nat_lit 4955389084) (nat_lit 0) A10K2.t4337 from rfl, allE_node, rows4336, irow4331, rows4337]
  all_goals rfl

theorem atot4331 : totK PA10K2 A10K2.u4331 = [0, 0, 0, 287930791013, 1935778927829, 3861576149007, 2612625718940, 558650944273, 30605747850, 0] := by
  rw [show A10K2.u4331 = KTree.node A10K2.t4336 (nat_lit 69507282) (nat_lit 4955389084) (nat_lit 0) A10K2.t4337 from rfl, totK_node, tot4336, tot4337]
  decide +kernel

theorem arows4332 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4332 = true := by
  rw [show A10K2.u4332 = KTree.node A10K2.t4338 (nat_lit 69520234) (nat_lit 7845445024) (nat_lit 0) A10K2.t4339 from rfl, allE_node, rows4338, irow4332, rows4339]
  all_goals rfl

theorem atot4332 : totK PA10K2 A10K2.u4332 = [0, 0, 0, 541490125820, 2585514154758, 3775765267200, 1683888421451, 210732871118, 5528811039, 0] := by
  rw [show A10K2.u4332 = KTree.node A10K2.t4338 (nat_lit 69520234) (nat_lit 7845445024) (nat_lit 0) A10K2.t4339 from rfl, totK_node, tot4338, tot4339]
  decide +kernel

theorem arows4334 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4334 = true := by
  rw [show A10K2.u4334 = KTree.node A10K2.t4340 (nat_lit 69529184) (nat_lit 12814510479) (nat_lit 0) A10K2.t4341 from rfl, allE_node, rows4340, irow4334, rows4341]
  all_goals rfl

theorem atot4334 : totK PA10K2 A10K2.u4334 = [0, 0, 510744180543, 2219222275867, 3796991488524, 2632136420426, 615055293751, 38394631736, 0, 0] := by
  rw [show A10K2.u4334 = KTree.node A10K2.t4340 (nat_lit 69529184) (nat_lit 12814510479) (nat_lit 0) A10K2.t4341 from rfl, totK_node, tot4340, tot4341]
  decide +kernel

theorem arows4335 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4335 = true := by
  rw [show A10K2.u4335 = KTree.node A10K2.t4342 (nat_lit 69603735) (nat_lit 10528525702) (nat_lit 0) A10K2.t4343 from rfl, allE_node, rows4342, irow4335, rows4343]
  all_goals rfl

theorem atot4335 : totK PA10K2 A10K2.u4335 = [0, 0, 282182245847, 2037456717670, 4025990970804, 2615134421829, 546802839611, 30831673886, 0, 0] := by
  rw [show A10K2.u4335 = KTree.node A10K2.t4342 (nat_lit 69603735) (nat_lit 10528525702) (nat_lit 0) A10K2.t4343 from rfl, totK_node, tot4342, tot4343]
  decide +kernel

theorem arows4338 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4338 = true := by
  rw [show A10K2.u4338 = KTree.node A10K2.t4344 (nat_lit 69612726) (nat_lit 12214904030) (nat_lit 0) A10K2.t4345 from rfl, allE_node, rows4344, irow4338, rows4345]
  all_goals rfl

theorem atot4338 : totK PA10K2 A10K2.u4338 = [0, 0, 747299397922, 3019756518607, 3882971986031, 1616385964362, 175903949956, 5656154743, 0, 0] := by
  rw [show A10K2.u4338 = KTree.node A10K2.t4344 (nat_lit 69612726) (nat_lit 12214904030) (nat_lit 0) A10K2.t4345 from rfl, totK_node, tot4344, tot4345]
  decide +kernel

theorem arows4339 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4339 = true := by
  rw [show A10K2.u4339 = KTree.node A10K2.t4346 (nat_lit 69618325) (nat_lit 6819468953) (nat_lit 0) A10K2.t4347 from rfl, allE_node, rows4346, irow4339, rows4347]
  all_goals rfl

theorem atot4339 : totK PA10K2 A10K2.u4339 = [0, 0, 509037370054, 2777030235810, 4241062171096, 1555729551758, 94165247409, 0, 0, 0] := by
  rw [show A10K2.u4339 = KTree.node A10K2.t4346 (nat_lit 69618325) (nat_lit 6819468953) (nat_lit 0) A10K2.t4347 from rfl, totK_node, tot4346, tot4347]
  decide +kernel

theorem arows4341 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4341 = true := by
  rw [show A10K2.u4341 = KTree.node A10K2.t4348 (nat_lit 69634262) (nat_lit 1246633653) (nat_lit 0) A10K2.t4349 from rfl, allE_node, rows4348, irow4341, rows4349]
  all_goals rfl

theorem atot4341 : totK PA10K2 A10K2.u4341 = [0, 0, 0, 1059436268963, 3816821809166, 3650637793727, 879994292214, 44905858284, 0, 0] := by
  rw [show A10K2.u4341 = KTree.node A10K2.t4348 (nat_lit 69634262) (nat_lit 1246633653) (nat_lit 0) A10K2.t4349 from rfl, totK_node, tot4348, tot4349]
  decide +kernel

theorem arows4342 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4342 = true := by
  rw [show A10K2.u4342 = KTree.node A10K2.t4350 (nat_lit 69649566) (nat_lit 10503743497) (nat_lit 0) A10K2.t4351 from rfl, allE_node, rows4350, irow4342, rows4351]
  all_goals rfl

theorem atot4342 : totK PA10K2 A10K2.u4342 = [0, 0, 0, 974202941480, 3667728263088, 3584745343296, 817198696472, 56554223674, 0, 0] := by
  rw [show A10K2.u4342 = KTree.node A10K2.t4350 (nat_lit 69649566) (nat_lit 10503743497) (nat_lit 0) A10K2.t4351 from rfl, totK_node, tot4350, tot4351]
  decide +kernel

theorem arows4350 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4350 = true := by
  rw [show A10K2.u4350 = KTree.node A10K2.t4352 (nat_lit 69665064) (nat_lit 12390657786) (nat_lit 0) A10K2.t4353 from rfl, allE_node, rows4352, irow4350, rows4353]
  all_goals rfl

theorem atot4350 : totK PA10K2 A10K2.u4350 = [0, 0, 687120682159, 2283241915261, 2798805422375, 2291533951306, 1102042498912, 171735004960, 5676195732, 0] := by
  rw [show A10K2.u4350 = KTree.node A10K2.t4352 (nat_lit 69665064) (nat_lit 12390657786) (nat_lit 0) A10K2.t4353 from rfl, totK_node, tot4352, tot4353]
  decide +kernel

theorem arows4351 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4351 = true := by
  rw [show A10K2.u4351 = KTree.node A10K2.t4354 (nat_lit 69669809) (nat_lit 8915330021) (nat_lit 0) A10K2.t4355 from rfl, allE_node, rows4354, irow4351, rows4355]
  all_goals rfl

theorem atot4351 : totK PA10K2 A10K2.u4351 = [0, 0, 398777643902, 2377335355283, 4342957519415, 2473376826652, 379150826200, 20058242317, 0, 0] := by
  rw [show A10K2.u4351 = KTree.node A10K2.t4354 (nat_lit 69669809) (nat_lit 8915330021) (nat_lit 0) A10K2.t4355 from rfl, totK_node, tot4354, tot4355]
  decide +kernel

theorem arows4353 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4353 = true := by
  rw [show A10K2.u4353 = KTree.node A10K2.t4356 (nat_lit 69691264) (nat_lit 14119814049) (nat_lit 0) A10K2.t4357 from rfl, allE_node, rows4356, irow4353, rows4357]
  all_goals rfl

theorem atot4353 : totK PA10K2 A10K2.u4353 = [0, 0, 797300748016, 3289497976109, 4196969460426, 1589819858564, 130882680500, 0, 0, 0] := by
  rw [show A10K2.u4353 = KTree.node A10K2.t4356 (nat_lit 69691264) (nat_lit 14119814049) (nat_lit 0) A10K2.t4357 from rfl, totK_node, tot4356, tot4357]
  decide +kernel

theorem arows4354 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4354 = true := by
  rw [show A10K2.u4354 = KTree.node A10K2.t4358 (nat_lit 69697521) (nat_lit 7922807282) (nat_lit 0) A10K2.t4359 from rfl, allE_node, rows4358, irow4354, rows4359]
  all_goals rfl

theorem atot4354 : totK PA10K2 A10K2.u4354 = [0, 583356039855, 1934648030866, 2317340325423, 2440416364174, 2084047644939, 568290734126, 35503361870, 0, 0] := by
  rw [show A10K2.u4354 = KTree.node A10K2.t4358 (nat_lit 69697521) (nat_lit 7922807282) (nat_lit 0) A10K2.t4359 from rfl, totK_node, tot4358, tot4359]
  decide +kernel

theorem arows4357 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4357 = true := by
  rw [show A10K2.u4357 = KTree.node A10K2.t4360 (nat_lit 70259099) (nat_lit 1535700861) (nat_lit 0) A10K2.t4361 from rfl, allE_node, rows4360, irow4357, rows4361]
  all_goals rfl

theorem atot4357 : totK PA10K2 A10K2.u4357 = [0, 249468953483, 1865456766914, 4009329288425, 2791974914430, 556992772928, 30831673886, 0, 0, 0] := by
  rw [show A10K2.u4357 = KTree.node A10K2.t4360 (nat_lit 70259099) (nat_lit 1535700861) (nat_lit 0) A10K2.t4361 from rfl, totK_node, tot4360, tot4361]
  decide +kernel

theorem arows4358 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4358 = true := by
  rw [show A10K2.u4358 = KTree.node A10K2.t4362 (nat_lit 70272736) (nat_lit 6681012515) (nat_lit 0) A10K2.t4363 from rfl, allE_node, rows4362, irow4358, rows4363]
  all_goals rfl

theorem atot4358 : totK PA10K2 A10K2.u4358 = [0, 769412541229, 3184040009989, 3952881945526, 1501648081457, 125845306108, 0, 0, 0, 0] := by
  rw [show A10K2.u4358 = KTree.node A10K2.t4362 (nat_lit 70272736) (nat_lit 6681012515) (nat_lit 0) A10K2.t4363 from rfl, totK_node, tot4362, tot4363]
  decide +kernel

theorem arows4360 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4360 = true := by
  rw [show A10K2.u4360 = KTree.node A10K2.t4364 (nat_lit 70279615) (nat_lit 14252228148) (nat_lit 0) A10K2.t4365 from rfl, allE_node, rows4364, irow4360, rows4365]
  all_goals rfl

theorem atot4360 : totK PA10K2 A10K2.u4360 = [0, 552312781151, 2594380642234, 4082497705823, 2144362632630, 310771568838, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u4360 = KTree.node A10K2.t4364 (nat_lit 70279615) (nat_lit 14252228148) (nat_lit 0) A10K2.t4365 from rfl, totK_node, tot4364, tot4365]
  decide +kernel

theorem arows4361 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4361 = true := by
  rw [show A10K2.u4361 = KTree.node A10K2.t4366 (nat_lit 70287415) (nat_lit 14448910211) (nat_lit 0) A10K2.t4367 from rfl, allE_node, rows4366, irow4361, rows4367]
  all_goals rfl

theorem atot4361 : totK PA10K2 A10K2.u4361 = [0, 0, 989128639010, 3756984335951, 3900607922807, 1032325708950, 61170437706, 0, 0, 0] := by
  rw [show A10K2.u4361 = KTree.node A10K2.t4366 (nat_lit 70287415) (nat_lit 14448910211) (nat_lit 0) A10K2.t4367 from rfl, totK_node, tot4366, tot4367]
  decide +kernel

theorem arows4365 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4365 = true := by
  rw [show A10K2.u4365 = KTree.node A10K2.t4368 (nat_lit 70292018) (nat_lit 5741245813) (nat_lit 0) A10K2.t4369 from rfl, allE_node, rows4368, irow4365, rows4369]
  all_goals rfl

theorem atot4365 : totK PA10K2 A10K2.u4365 = [0, 0, 326267187407, 1883065634865, 3898298728514, 2663089141806, 555358256481, 30650496230, 0, 0] := by
  rw [show A10K2.u4365 = KTree.node A10K2.t4368 (nat_lit 70292018) (nat_lit 5741245813) (nat_lit 0) A10K2.t4369 from rfl, totK_node, tot4368, tot4369]
  decide +kernel

theorem arows4366 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4366 = true := by
  rw [show A10K2.u4366 = KTree.node A10K2.t4370 (nat_lit 70305898) (nat_lit 5484142221) (nat_lit 0) A10K2.t4371 from rfl, allE_node, rows4370, irow4366, rows4371]
  all_goals rfl

theorem atot4366 : totK PA10K2 A10K2.u4366 = [0, 0, 690651565982, 3222239559161, 4146566614282, 1348470567323, 91432550180, 0, 0, 0] := by
  rw [show A10K2.u4366 = KTree.node A10K2.t4370 (nat_lit 70305898) (nat_lit 5484142221) (nat_lit 0) A10K2.t4371 from rfl, totK_node, tot4370, tot4371]
  decide +kernel

theorem arows4368 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4368 = true := by
  rw [show A10K2.u4368 = KTree.node A10K2.t4372 (nat_lit 70315052) (nat_lit 8294162041) (nat_lit 0) A10K2.t4373 from rfl, allE_node, rows4372, irow4368, rows4373]
  all_goals rfl

theorem atot4368 : totK PA10K2 A10K2.u4368 = [0, 303055287478, 1534516183354, 3081522987762, 3197530279013, 1401334066631, 189146478463, 5546304973, 0, 0] := by
  rw [show A10K2.u4368 = KTree.node A10K2.t4372 (nat_lit 70315052) (nat_lit 8294162041) (nat_lit 0) A10K2.t4373 from rfl, totK_node, tot4372, tot4373]
  decide +kernel

theorem arows4369 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4369 = true := by
  rw [show A10K2.u4369 = KTree.node A10K2.t4374 (nat_lit 70332371) (nat_lit 9231652012) (nat_lit 0) A10K2.t4375 from rfl, allE_node, rows4374, irow4369, rows4375]
  all_goals rfl

theorem atot4369 : totK PA10K2 A10K2.u4369 = [0, 459928825582, 2376264228013, 4050973503756, 2391544559517, 453113183746, 25734533292, 0, 0, 0] := by
  rw [show A10K2.u4369 = KTree.node A10K2.t4374 (nat_lit 70332371) (nat_lit 9231652012) (nat_lit 0) A10K2.t4375 from rfl, totK_node, tot4374, tot4375]
  decide +kernel

theorem arows4372 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4372 = true := by
  rw [show A10K2.u4372 = KTree.node A10K2.t4376 (nat_lit 70337893) (nat_lit 7280085236) (nat_lit 0) A10K2.t4377 from rfl, allE_node, rows4376, irow4372, rows4377]
  all_goals rfl

theorem atot4372 : totK PA10K2 A10K2.u4372 = [0, 778819795920, 3120949377966, 3892298771823, 1669929645898, 238384459872, 6034215561, 0, 0, 0] := by
  rw [show A10K2.u4372 = KTree.node A10K2.t4376 (nat_lit 70337893) (nat_lit 7280085236) (nat_lit 0) A10K2.t4377 from rfl, totK_node, tot4376, tot4377]
  decide +kernel

theorem arows4373 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4373 = true := by
  rw [show A10K2.u4373 = KTree.node A10K2.t4378 (nat_lit 70362282) (nat_lit 13057837668) (nat_lit 0) A10K2.t4379 from rfl, allE_node, rows4378, irow4373, rows4379]
  all_goals rfl

theorem atot4373 : totK PA10K2 A10K2.u4373 = [0, 0, 1245072108541, 4124864227896, 3449194648840, 701657343965, 32616029439, 0, 0, 0] := by
  rw [show A10K2.u4373 = KTree.node A10K2.t4378 (nat_lit 70362282) (nat_lit 13057837668) (nat_lit 0) A10K2.t4379 from rfl, totK_node, tot4378, tot4379]
  decide +kernel

theorem arows4375 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4375 = true := by
  rw [show A10K2.u4375 = KTree.node A10K2.t4380 (nat_lit 70370629) (nat_lit 6848863028) (nat_lit 0) A10K2.t4381 from rfl, allE_node, rows4380, irow4375, rows4381]
  all_goals rfl

theorem atot4375 : totK PA10K2 A10K2.u4375 = [0, 0, 964946403607, 3643315264450, 3981851759403, 1070718473175, 50775056318, 0, 0, 0] := by
  rw [show A10K2.u4375 = KTree.node A10K2.t4380 (nat_lit 70370629) (nat_lit 6848863028) (nat_lit 0) A10K2.t4381 from rfl, totK_node, tot4380, tot4381]
  decide +kernel

theorem arows4376 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4376 = true := by
  rw [show A10K2.u4376 = KTree.node A10K2.t4382 (nat_lit 70385764) (nat_lit 13017262675) (nat_lit 0) A10K2.t4383 from rfl, allE_node, rows4382, irow4376, rows4383]
  all_goals rfl

theorem atot4376 : totK PA10K2 A10K2.u4376 = [0, 579756899725, 2107815462945, 2755269659981, 2462988877520, 1293528362457, 205801519208, 6121173289, 0, 0] := by
  rw [show A10K2.u4376 = KTree.node A10K2.t4382 (nat_lit 70385764) (nat_lit 13017262675) (nat_lit 0) A10K2.t4383 from rfl, totK_node, tot4382, tot4383]
  decide +kernel

theorem arows4381 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4381 = true := by
  rw [show A10K2.u4381 = KTree.node A10K2.t4384 (nat_lit 70390661) (nat_lit 5047026404) (nat_lit 0) A10K2.t4385 from rfl, allE_node, rows4384, irow4381, rows4385]
  all_goals rfl

theorem atot4381 : totK PA10K2 A10K2.u4381 = [0, 444474430353, 2040382490350, 3771082063378, 2722639355015, 571708829181, 30831673886, 0, 0, 0] := by
  rw [show A10K2.u4381 = KTree.node A10K2.t4384 (nat_lit 70390661) (nat_lit 5047026404) (nat_lit 0) A10K2.t4385 from rfl, totK_node, tot4384, tot4385]
  decide +kernel

theorem arows4382 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4382 = true := by
  rw [show A10K2.u4382 = KTree.node A10K2.t4386 (nat_lit 70397630) (nat_lit 11842463174) (nat_lit 0) A10K2.t4387 from rfl, allE_node, rows4386, irow4382, rows4387]
  all_goals rfl

theorem atot4382 : totK PA10K2 A10K2.u4382 = [0, 390517805825, 2309292026940, 4112390335207, 2397416065710, 399591431520, 25299471099, 0, 0, 0] := by
  rw [show A10K2.u4382 = KTree.node A10K2.t4386 (nat_lit 70397630) (nat_lit 11842463174) (nat_lit 0) A10K2.t4387 from rfl, totK_node, tot4386, tot4387]
  decide +kernel

theorem arows4384 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4384 = true := by
  rw [show A10K2.u4384 = KTree.node A10K2.t4388 (nat_lit 70403436) (nat_lit 12695026321) (nat_lit 0) A10K2.t4389 from rfl, allE_node, rows4388, irow4384, rows4389]
  all_goals rfl

theorem atot4384 : totK PA10K2 A10K2.u4384 = [0, 836900465410, 3241855033312, 3777533619903, 1456835000583, 197300212758, 6034215561, 0, 0, 0] := by
  rw [show A10K2.u4384 = KTree.node A10K2.t4388 (nat_lit 70403436) (nat_lit 12695026321) (nat_lit 0) A10K2.t4389 from rfl, totK_node, tot4388, tot4389]
  decide +kernel

theorem arows4385 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4385 = true := by
  rw [show A10K2.u4385 = KTree.node A10K2.t4390 (nat_lit 70409029) (nat_lit 6792366345) (nat_lit 0) A10K2.t4391 from rfl, allE_node, rows4390, irow4385, rows4391]
  all_goals rfl

theorem atot4385 : totK PA10K2 A10K2.u4385 = [0, 0, 1303162634172, 4128507446078, 3315335121766, 668937344791, 31987755669, 0, 0, 0] := by
  rw [show A10K2.u4385 = KTree.node A10K2.t4390 (nat_lit 70409029) (nat_lit 6792366345) (nat_lit 0) A10K2.t4391 from rfl, totK_node, tot4390, tot4391]
  decide +kernel

theorem arows4388 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4388 = true := by
  rw [show A10K2.u4388 = KTree.node A10K2.t4392 (nat_lit 70428453) (nat_lit 7311967796) (nat_lit 0) A10K2.t4393 from rfl, allE_node, rows4392, irow4388, rows4393]
  all_goals rfl

theorem atot4388 : totK PA10K2 A10K2.u4388 = [0, 0, 1041983972185, 3778590318735, 3865526138861, 953343730194, 45185793998, 0, 0, 0] := by
  rw [show A10K2.u4388 = KTree.node A10K2.t4392 (nat_lit 70428453) (nat_lit 7311967796) (nat_lit 0) A10K2.t4393 from rfl, totK_node, tot4392, tot4393]
  decide +kernel

theorem arows4389 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4389 = true := by
  rw [show A10K2.u4389 = KTree.node A10K2.t4394 (nat_lit 70437025) (nat_lit 8323010573) (nat_lit 0) A10K2.t4395 from rfl, allE_node, rows4394, irow4389, rows4395]
  all_goals rfl

theorem atot4389 : totK PA10K2 A10K2.u4389 = [0, 0, 607105875163, 3072794081982, 4154523824629, 1374747681923, 108770940573, 0, 0, 0] := by
  rw [show A10K2.u4389 = KTree.node A10K2.t4394 (nat_lit 70437025) (nat_lit 8323010573) (nat_lit 0) A10K2.t4395 from rfl, totK_node, tot4394, tot4395]
  decide +kernel

theorem arows4391 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4391 = true := by
  rw [show A10K2.u4391 = KTree.node A10K2.t4396 (nat_lit 70517533) (nat_lit 5844644539) (nat_lit 0) A10K2.t4397 from rfl, allE_node, rows4396, irow4391, rows4397]
  all_goals rfl

theorem atot4391 : totK PA10K2 A10K2.u4391 = [0, 0, 831675448015, 3091455759691, 3738507838412, 1562651119652, 239310381162, 6354482628, 0, 0] := by
  rw [show A10K2.u4391 = KTree.node A10K2.t4396 (nat_lit 70517533) (nat_lit 5844644539) (nat_lit 0) A10K2.t4397 from rfl, totK_node, tot4396, tot4397]
  decide +kernel

theorem arows4392 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4392 = true := by
  rw [show A10K2.u4392 = KTree.node A10K2.t4398 (nat_lit 70523145) (nat_lit 9690107151) (nat_lit 0) A10K2.t4399 from rfl, allE_node, rows4398, irow4392, rows4399]
  all_goals rfl

theorem atot4392 : totK PA10K2 A10K2.u4392 = [0, 0, 287871761280, 1838216122252, 3901807039055, 2756982651893, 576338435213, 30818366867, 0, 0] := by
  rw [show A10K2.u4392 = KTree.node A10K2.t4398 (nat_lit 70523145) (nat_lit 9690107151) (nat_lit 0) A10K2.t4399 from rfl, totK_node, tot4398, tot4399]
  decide +kernel

theorem arows4396 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4396 = true := by
  rw [show A10K2.u4396 = KTree.node A10K2.t4400 (nat_lit 70535962) (nat_lit 12337948483) (nat_lit 0) A10K2.t4401 from rfl, allE_node, rows4400, irow4396, rows4401]
  all_goals rfl

theorem atot4396 : totK PA10K2 A10K2.u4396 = [0, 0, 478170626599, 2649609781981, 4279961877701, 1831022778132, 133412961237, 0, 0, 0] := by
  rw [show A10K2.u4396 = KTree.node A10K2.t4400 (nat_lit 70535962) (nat_lit 12337948483) (nat_lit 0) A10K2.t4401 from rfl, totK_node, tot4400, tot4401]
  decide +kernel

theorem arows4397 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4397 = true := by
  rw [show A10K2.u4397 = KTree.node A10K2.t4402 (nat_lit 70544929) (nat_lit 9757153013) (nat_lit 0) A10K2.t4403 from rfl, allE_node, rows4402, irow4397, rows4403]
  all_goals rfl

theorem atot4397 : totK PA10K2 A10K2.u4397 = [0, 0, 552312781151, 2570691221417, 4002225259225, 2286956080163, 404490169403, 13207830636, 0, 0] := by
  rw [show A10K2.u4397 = KTree.node A10K2.t4402 (nat_lit 70544929) (nat_lit 9757153013) (nat_lit 0) A10K2.t4403 from rfl, totK_node, tot4402, tot4403]
  decide +kernel

theorem arows4399 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4399 = true := by
  rw [show A10K2.u4399 = KTree.node A10K2.t4404 (nat_lit 70593214) (nat_lit 13255353418) (nat_lit 0) A10K2.t4405 from rfl, allE_node, rows4404, irow4399, rows4405]
  all_goals rfl

theorem atot4399 : totK PA10K2 A10K2.u4399 = [0, 0, 1060442834362, 3732809293422, 3796667256532, 1089430995292, 56362358423, 0, 0, 0] := by
  rw [show A10K2.u4399 = KTree.node A10K2.t4404 (nat_lit 70593214) (nat_lit 13255353418) (nat_lit 0) A10K2.t4405 from rfl, totK_node, tot4404, tot4405]
  decide +kernel

theorem arows4400 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4400 = true := by
  rw [show A10K2.u4400 = KTree.node A10K2.t4406 (nat_lit 70601536) (nat_lit 13042081337) (nat_lit 0) A10K2.t4407 from rfl, allE_node, rows4406, irow4400, rows4407]
  all_goals rfl

theorem atot4400 : totK PA10K2 A10K2.u4400 = [0, 0, 462785939474, 2634901026486, 4306885546517, 1897378719552, 172470743167, 0, 0, 0] := by
  rw [show A10K2.u4400 = KTree.node A10K2.t4406 (nat_lit 70601536) (nat_lit 13042081337) (nat_lit 0) A10K2.t4407 from rfl, totK_node, tot4406, tot4407]
  decide +kernel

theorem arows4403 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4403 = true := by
  rw [show A10K2.u4403 = KTree.node A10K2.t4408 (nat_lit 70650382) (nat_lit 11394377093) (nat_lit 0) A10K2.t4409 from rfl, allE_node, rows4408, irow4403, rows4409]
  all_goals rfl

theorem atot4403 : totK PA10K2 A10K2.u4403 = [0, 0, 758880489847, 3050412669495, 3775041177474, 1599989203821, 289776414040, 25668455103, 0, 0] := by
  rw [show A10K2.u4403 = KTree.node A10K2.t4408 (nat_lit 70650382) (nat_lit 11394377093) (nat_lit 0) A10K2.t4409 from rfl, totK_node, tot4408, tot4409]
  decide +kernel

theorem arows4404 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4404 = true := by
  rw [show A10K2.u4404 = KTree.node A10K2.t4410 (nat_lit 70657315) (nat_lit 10336289781) (nat_lit 0) A10K2.t4411 from rfl, allE_node, rows4410, irow4404, rows4411]
  all_goals rfl

theorem atot4404 : totK PA10K2 A10K2.u4404 = [0, 0, 653748130877, 2694295931452, 3825760269357, 1982420906833, 315305237123, 10760911071, 0, 0] := by
  rw [show A10K2.u4404 = KTree.node A10K2.t4410 (nat_lit 70657315) (nat_lit 10336289781) (nat_lit 0) A10K2.t4411 from rfl, totK_node, tot4410, tot4411]
  decide +kernel

theorem arows4406 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4406 = true := by
  rw [show A10K2.u4406 = KTree.node A10K2.t4412 (nat_lit 70664469) (nat_lit 7018165258) (nat_lit 0) A10K2.t4413 from rfl, allE_node, rows4412, irow4406, rows4413]
  all_goals rfl

theorem atot4406 : totK PA10K2 A10K2.u4406 = [0, 0, 624168802633, 2755332428105, 3936620963944, 1810214710908, 247162393697, 6034215561, 0, 0] := by
  rw [show A10K2.u4406 = KTree.node A10K2.t4412 (nat_lit 70664469) (nat_lit 7018165258) (nat_lit 0) A10K2.t4413 from rfl, totK_node, tot4412, tot4413]
  decide +kernel

theorem arows4407 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4407 = true := by
  rw [show A10K2.u4407 = KTree.node A10K2.t4414 (nat_lit 70669632) (nat_lit 12639463354) (nat_lit 0) A10K2.t4415 from rfl, allE_node, rows4414, irow4407, rows4415]
  all_goals rfl

theorem atot4407 : totK PA10K2 A10K2.u4407 = [0, 0, 209103078700, 2080984643218, 4324527539698, 2390629817897, 329404378484, 6354482628, 0, 0] := by
  rw [show A10K2.u4407 = KTree.node A10K2.t4414 (nat_lit 70669632) (nat_lit 12639463354) (nat_lit 0) A10K2.t4415 from rfl, totK_node, tot4414, tot4415]
  decide +kernel

theorem arows4413 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4413 = true := by
  rw [show A10K2.u4413 = KTree.node A10K2.t4416 (nat_lit 70689976) (nat_lit 4679765042) (nat_lit 0) A10K2.t4417 from rfl, allE_node, rows4416, irow4413, rows4417]
  all_goals rfl

theorem atot4413 : totK PA10K2 A10K2.u4413 = [0, 0, 0, 1308748528202, 4041777093368, 3209316163298, 696045285911, 37547960447, 0, 0] := by
  rw [show A10K2.u4413 = KTree.node A10K2.t4416 (nat_lit 70689976) (nat_lit 4679765042) (nat_lit 0) A10K2.t4417 from rfl, totK_node, tot4416, tot4417]
  decide +kernel

theorem arows4414 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4414 = true := by
  rw [show A10K2.u4414 = KTree.node A10K2.t4418 (nat_lit 70699271) (nat_lit 7047577829) (nat_lit 0) A10K2.t4419 from rfl, allE_node, rows4418, irow4414, rows4419]
  all_goals rfl

theorem atot4414 : totK PA10K2 A10K2.u4414 = [0, 0, 0, 611702430061, 3143317099555, 3955443680546, 1283087053528, 94390941945, 0, 0] := by
  rw [show A10K2.u4414 = KTree.node A10K2.t4418 (nat_lit 70699271) (nat_lit 7047577829) (nat_lit 0) A10K2.t4419 from rfl, totK_node, tot4418, tot4419]
  decide +kernel

theorem arows4416 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4416 = true := by
  rw [show A10K2.u4416 = KTree.node A10K2.t4420 (nat_lit 70781036) (nat_lit 11667306728) (nat_lit 0) A10K2.t4421 from rfl, allE_node, rows4420, irow4416, rows4421]
  all_goals rfl

theorem atot4416 : totK PA10K2 A10K2.u4416 = [0, 840900766144, 3099241726150, 3370695759307, 1121815609530, 520608349429, 533592381286, 129424075521, 5976421810, 0] := by
  rw [show A10K2.u4416 = KTree.node A10K2.t4420 (nat_lit 70781036) (nat_lit 11667306728) (nat_lit 0) A10K2.t4421 from rfl, totK_node, tot4420, tot4421]
  decide +kernel

theorem arows4417 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4417 = true := by
  rw [show A10K2.u4417 = KTree.node A10K2.t4422 (nat_lit 70785822) (nat_lit 11933677) (nat_lit 0) A10K2.t4423 from rfl, allE_node, rows4422, irow4417, rows4423]
  all_goals rfl

theorem atot4417 : totK PA10K2 A10K2.u4417 = [0, 352873183950, 1926116925999, 3892311068301, 2757435818250, 578671812874, 30831673886, 0, 0, 0] := by
  rw [show A10K2.u4417 = KTree.node A10K2.t4422 (nat_lit 70785822) (nat_lit 11933677) (nat_lit 0) A10K2.t4423 from rfl, totK_node, tot4422, tot4423]
  decide +kernel

theorem arows4420 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4420 = true := by
  rw [show A10K2.u4420 = KTree.node A10K2.t4424 (nat_lit 70801694) (nat_lit 2752679502) (nat_lit 0) A10K2.t4425 from rfl, allE_node, rows4424, irow4420, rows4425]
  all_goals rfl

theorem atot4420 : totK PA10K2 A10K2.u4420 = [0, 691287606472, 2940404183985, 3967382135579, 1768970392141, 220275698677, 5976421810, 0, 0, 0] := by
  rw [show A10K2.u4420 = KTree.node A10K2.t4424 (nat_lit 70801694) (nat_lit 2752679502) (nat_lit 0) A10K2.t4425 from rfl, totK_node, tot4424, tot4425]
  decide +kernel

theorem arows4421 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4421 = true := by
  rw [show A10K2.u4421 = KTree.node A10K2.t4426 (nat_lit 70807661) (nat_lit 5260089686) (nat_lit 0) A10K2.t4427 from rfl, allE_node, rows4426, irow4421, rows4427]
  all_goals rfl

theorem atot4421 : totK PA10K2 A10K2.u4421 = [0, 316555443509, 2153311535587, 4283085620863, 2915743984538, 530264910851, 13543209714, 0, 0, 0] := by
  rw [show A10K2.u4421 = KTree.node A10K2.t4426 (nat_lit 70807661) (nat_lit 5260089686) (nat_lit 0) A10K2.t4427 from rfl, totK_node, tot4426, tot4427]
  decide +kernel

theorem arows4423 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4423 = true := by
  rw [show A10K2.u4423 = KTree.node A10K2.t4428 (nat_lit 70812485) (nat_lit 6333615138) (nat_lit 0) A10K2.t4429 from rfl, allE_node, rows4428, irow4423, rows4429]
  all_goals rfl

theorem atot4423 : totK PA10K2 A10K2.u4423 = [0, 0, 922983651411, 3555547218411, 3953094856676, 1240044893739, 87183031427, 0, 0, 0] := by
  rw [show A10K2.u4423 = KTree.node A10K2.t4428 (nat_lit 70812485) (nat_lit 6333615138) (nat_lit 0) A10K2.t4429 from rfl, totK_node, tot4428, tot4429]
  decide +kernel

theorem arows4424 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4424 = true := by
  rw [show A10K2.u4424 = KTree.node A10K2.t4430 (nat_lit 70818313) (nat_lit 9707627861) (nat_lit 0) A10K2.t4431 from rfl, allE_node, rows4430, irow4424, rows4431]
  all_goals rfl

theorem atot4424 : totK PA10K2 A10K2.u4424 = [0, 0, 289478139766, 1961863445052, 3937250898762, 2649919540039, 561747244813, 30650496230, 0, 0] := by
  rw [show A10K2.u4424 = KTree.node A10K2.t4430 (nat_lit 70818313) (nat_lit 9707627861) (nat_lit 0) A10K2.t4431 from rfl, totK_node, tot4430, tot4431]
  decide +kernel

theorem arows4428 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4428 = true := by
  rw [show A10K2.u4428 = KTree.node A10K2.t4432 (nat_lit 70837032) (nat_lit 12158729684) (nat_lit 0) A10K2.t4433 from rfl, allE_node, rows4432, irow4428, rows4433]
  all_goals rfl

theorem atot4428 : totK PA10K2 A10K2.u4428 = [0, 0, 1068616027511, 3888154882633, 3979333186780, 1007063084990, 45640437169, 0, 0, 0] := by
  rw [show A10K2.u4428 = KTree.node A10K2.t4432 (nat_lit 70837032) (nat_lit 12158729684) (nat_lit 0) A10K2.t4433 from rfl, totK_node, tot4432, tot4433]
  decide +kernel

theorem arows4429 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4429 = true := by
  rw [show A10K2.u4429 = KTree.node A10K2.t4434 (nat_lit 70978339) (nat_lit 5073777319) (nat_lit 0) A10K2.t4435 from rfl, allE_node, rows4434, irow4429, rows4435]
  all_goals rfl

theorem atot4429 : totK PA10K2 A10K2.u4429 = [0, 779672340784, 3152486821554, 3916515826958, 1627043618896, 330121792124, 37674914273, 0, 0, 0] := by
  rw [show A10K2.u4429 = KTree.node A10K2.t4434 (nat_lit 70978339) (nat_lit 5073777319) (nat_lit 0) A10K2.t4435 from rfl, totK_node, tot4434, tot4435]
  decide +kernel

theorem arows4431 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4431 = true := by
  rw [show A10K2.u4431 = KTree.node A10K2.t4436 (nat_lit 70984914) (nat_lit 15688061821) (nat_lit 0) A10K2.t4437 from rfl, allE_node, rows4436, irow4431, rows4437]
  all_goals rfl

theorem atot4431 : totK PA10K2 A10K2.u4431 = [0, 594444043944, 2547474165128, 3931660162548, 2428512969175, 471868924198, 25295400199, 0, 0, 0] := by
  rw [show A10K2.u4431 = KTree.node A10K2.t4436 (nat_lit 70984914) (nat_lit 15688061821) (nat_lit 0) A10K2.t4437 from rfl, totK_node, tot4436, tot4437]
  decide +kernel

theorem arows4432 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4432 = true := by
  rw [show A10K2.u4432 = KTree.node A10K2.t4438 (nat_lit 70991317) (nat_lit 4366813880) (nat_lit 0) A10K2.t4439 from rfl, allE_node, rows4438, irow4432, rows4439]
  all_goals rfl

theorem atot4432 : totK PA10K2 A10K2.u4432 = [0, 538423298425, 2544547440000, 4052671052923, 2417860412208, 432461480414, 12692412833, 0, 0, 0] := by
  rw [show A10K2.u4432 = KTree.node A10K2.t4438 (nat_lit 70991317) (nat_lit 4366813880) (nat_lit 0) A10K2.t4439 from rfl, totK_node, tot4438, tot4439]
  decide +kernel

theorem arows4435 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4435 = true := by
  rw [show A10K2.u4435 = KTree.node A10K2.t4440 (nat_lit 71004485) (nat_lit 5405204354) (nat_lit 0) A10K2.t4441 from rfl, allE_node, rows4440, irow4435, rows4441]
  all_goals rfl

theorem atot4435 : totK PA10K2 A10K2.u4435 = [0, 329574811601, 2102823819227, 4221281124789, 2884243832952, 527611472706, 13816090359, 0, 0, 0] := by
  rw [show A10K2.u4435 = KTree.node A10K2.t4440 (nat_lit 71004485) (nat_lit 5405204354) (nat_lit 0) A10K2.t4441 from rfl, totK_node, tot4440, tot4441]
  decide +kernel

theorem arows4436 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4436 = true := by
  rw [show A10K2.u4436 = KTree.node A10K2.t4442 (nat_lit 71009037) (nat_lit 5701671550) (nat_lit 0) A10K2.t4443 from rfl, allE_node, rows4442, irow4436, rows4443]
  all_goals rfl

theorem atot4436 : totK PA10K2 A10K2.u4436 = [0, 0, 900415936818, 3539954724252, 4065218494412, 1307418471160, 87527964963, 0, 0, 0] := by
  rw [show A10K2.u4436 = KTree.node A10K2.t4442 (nat_lit 71009037) (nat_lit 5701671550) (nat_lit 0) A10K2.t4443 from rfl, totK_node, tot4442, tot4443]
  decide +kernel

theorem arows4438 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4438 = true := by
  rw [show A10K2.u4438 = KTree.node A10K2.t4444 (nat_lit 71015671) (nat_lit 14604207045) (nat_lit 0) A10K2.t4445 from rfl, allE_node, rows4444, irow4438, rows4445]
  all_goals rfl

theorem atot4438 : totK PA10K2 A10K2.u4438 = [0, 0, 592981215928, 2637131760731, 4070627349745, 2269936193548, 335715921395, 6904928264, 0, 0] := by
  rw [show A10K2.u4438 = KTree.node A10K2.t4444 (nat_lit 71015671) (nat_lit 14604207045) (nat_lit 0) A10K2.t4445 from rfl, totK_node, tot4444, tot4445]
  decide +kernel

theorem arows4439 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4439 = true := by
  rw [show A10K2.u4439 = KTree.node A10K2.t4446 (nat_lit 71023835) (nat_lit 8697526598) (nat_lit 0) A10K2.t4447 from rfl, allE_node, rows4446, irow4439, rows4447]
  all_goals rfl

theorem atot4439 : totK PA10K2 A10K2.u4439 = [0, 0, 537487968785, 2655233361199, 4218806220474, 2307818140953, 292381551289, 6766355402, 0, 0] := by
  rw [show A10K2.u4439 = KTree.node A10K2.t4446 (nat_lit 71023835) (nat_lit 8697526598) (nat_lit 0) A10K2.t4447 from rfl, totK_node, tot4446, tot4447]
  decide +kernel

theorem arows4444 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4444 = true := by
  rw [show A10K2.u4444 = KTree.node A10K2.t4448 (nat_lit 71036984) (nat_lit 14859874300) (nat_lit 0) A10K2.t4449 from rfl, allE_node, rows4448, irow4444, rows4449]
  all_goals rfl

theorem atot4444 : totK PA10K2 A10K2.u4444 = [0, 0, 328230673014, 2092865411726, 4138606460075, 2801295184663, 467242920073, 12224107035, 0, 0] := by
  rw [show A10K2.u4444 = KTree.node A10K2.t4448 (nat_lit 71036984) (nat_lit 14859874300) (nat_lit 0) A10K2.t4449 from rfl, totK_node, tot4448, tot4449]
  decide +kernel

theorem arows4445 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4445 = true := by
  rw [show A10K2.u4445 = KTree.node A10K2.t4450 (nat_lit 71902897) (nat_lit 4634824498) (nat_lit 0) A10K2.t4451 from rfl, allE_node, rows4450, irow4445, rows4451]
  all_goals rfl

theorem atot4445 : totK PA10K2 A10K2.u4445 = [872304469579, 2779957985724, 2522841733561, 853608867837, 978642067316, 1242908171025, 512095249310, 48886019071, 0, 0] := by
  rw [show A10K2.u4445 = KTree.node A10K2.t4450 (nat_lit 71902897) (nat_lit 4634824498) (nat_lit 0) A10K2.t4451 from rfl, totK_node, tot4450, tot4451]
  decide +kernel

theorem arows4447 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4447 = true := by
  rw [show A10K2.u4447 = KTree.node A10K2.t4452 (nat_lit 71907259) (nat_lit 6896286884) (nat_lit 0) A10K2.t4453 from rfl, allE_node, rows4452, irow4447, rows4453]
  all_goals rfl

theorem atot4447 : totK PA10K2 A10K2.u4447 = [152063379648, 1682795537147, 4063888912270, 3100733593053, 631053798595, 31768748853, 0, 0, 0, 0] := by
  rw [show A10K2.u4447 = KTree.node A10K2.t4452 (nat_lit 71907259) (nat_lit 6896286884) (nat_lit 0) A10K2.t4453 from rfl, totK_node, tot4452, tot4453]
  decide +kernel

theorem arows4448 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4448 = true := by
  rw [show A10K2.u4448 = KTree.node A10K2.t4454 (nat_lit 71911685) (nat_lit 7040787894) (nat_lit 0) A10K2.t4455 from rfl, allE_node, rows4454, irow4448, rows4455]
  all_goals rfl

theorem atot4448 : totK PA10K2 A10K2.u4448 = [576047241256, 2868598266892, 4140405839150, 1697413395055, 147306556710, 0, 0, 0, 0, 0] := by
  rw [show A10K2.u4448 = KTree.node A10K2.t4454 (nat_lit 71911685) (nat_lit 7040787894) (nat_lit 0) A10K2.t4455 from rfl, totK_node, tot4454, tot4455]
  decide +kernel

theorem arows4451 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4451 = true := by
  rw [show A10K2.u4451 = KTree.node A10K2.t4456 (nat_lit 71919286) (nat_lit 16028661167) (nat_lit 0) A10K2.t4457 from rfl, allE_node, rows4456, irow4451, rows4457]
  all_goals rfl

theorem atot4451 : totK PA10K2 A10K2.u4451 = [743410903023, 2984983575275, 3967533964009, 1828876523127, 256145402686, 6354482628, 0, 0, 0, 0] := by
  rw [show A10K2.u4451 = KTree.node A10K2.t4456 (nat_lit 71919286) (nat_lit 16028661167) (nat_lit 0) A10K2.t4457 from rfl, totK_node, tot4456, tot4457]
  decide +kernel

theorem arows4452 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4452 = true := by
  rw [show A10K2.u4452 = KTree.node A10K2.t4458 (nat_lit 71925206) (nat_lit 15883464952) (nat_lit 0) A10K2.t4459 from rfl, allE_node, rows4458, irow4452, rows4459]
  all_goals rfl

theorem atot4452 : totK PA10K2 A10K2.u4452 = [0, 921446940808, 3595222880457, 4033343992035, 1223863200907, 81804581622, 0, 0, 0, 0] := by
  rw [show A10K2.u4452 = KTree.node A10K2.t4458 (nat_lit 71925206) (nat_lit 15883464952) (nat_lit 0) A10K2.t4459 from rfl, totK_node, tot4458, tot4459]
  decide +kernel

theorem arows4454 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4454 = true := by
  rw [show A10K2.u4454 = KTree.node A10K2.t4460 (nat_lit 71937927) (nat_lit 14453318606) (nat_lit 0) A10K2.t4461 from rfl, allE_node, rows4460, irow4454, rows4461]
  all_goals rfl

theorem atot4454 : totK PA10K2 A10K2.u4454 = [0, 548577217461, 2578269748529, 3922542959822, 2077871499642, 404331712694, 25565504801, 0, 0, 0] := by
  rw [show A10K2.u4454 = KTree.node A10K2.t4460 (nat_lit 71937927) (nat_lit 14453318606) (nat_lit 0) A10K2.t4461 from rfl, totK_node, tot4460, tot4461]
  decide +kernel

theorem arows4455 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4455 = true := by
  rw [show A10K2.u4455 = KTree.node A10K2.t4462 (nat_lit 71943506) (nat_lit 14924499148) (nat_lit 0) A10K2.t4463 from rfl, allE_node, rows4462, irow4455, rows4463]
  all_goals rfl

theorem atot4455 : totK PA10K2 A10K2.u4455 = [0, 727485560022, 2984375355449, 3827174555276, 1671291208576, 211873521882, 5517381808, 0, 0, 0] := by
  rw [show A10K2.u4455 = KTree.node A10K2.t4462 (nat_lit 71943506) (nat_lit 14924499148) (nat_lit 0) A10K2.t4463 from rfl, totK_node, tot4462, tot4463]
  decide +kernel

theorem arows4459 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4459 = true := by
  rw [show A10K2.u4459 = KTree.node A10K2.t4464 (nat_lit 71950724) (nat_lit 11933677) (nat_lit 0) A10K2.t4465 from rfl, allE_node, rows4464, irow4459, rows4465]
  all_goals rfl

theorem atot4459 : totK PA10K2 A10K2.u4459 = [0, 621562383373, 2723083143180, 3976593661901, 1915125320254, 238838251310, 6121173289, 0, 0, 0] := by
  rw [show A10K2.u4459 = KTree.node A10K2.t4464 (nat_lit 71950724) (nat_lit 11933677) (nat_lit 0) A10K2.t4465 from rfl, totK_node, tot4464, tot4465]
  decide +kernel

theorem arows4460 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4460 = true := by
  rw [show A10K2.u4460 = KTree.node A10K2.t4466 (nat_lit 71960654) (nat_lit 8994845113) (nat_lit 0) A10K2.t4467 from rfl, allE_node, rows4466, irow4460, rows4467]
  all_goals rfl

theorem atot4460 : totK PA10K2 A10K2.u4460 = [468537272203, 2176616481943, 3459414342420, 2536054390647, 855548612847, 75101591598, 0, 0, 0, 0] := by
  rw [show A10K2.u4460 = KTree.node A10K2.t4466 (nat_lit 71960654) (nat_lit 8994845113) (nat_lit 0) A10K2.t4467 from rfl, totK_node, tot4466, tot4467]
  decide +kernel

theorem arows4462 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4462 = true := by
  rw [show A10K2.u4462 = KTree.node A10K2.t4468 (nat_lit 71968804) (nat_lit 13718824819) (nat_lit 0) A10K2.t4469 from rfl, allE_node, rows4468, irow4462, rows4469]
  all_goals rfl

theorem atot4462 : totK PA10K2 A10K2.u4462 = [799877054642, 3110003276833, 3920381268809, 1701991303311, 214411577320, 5460492893, 0, 0, 0, 0] := by
  rw [show A10K2.u4462 = KTree.node A10K2.t4468 (nat_lit 71968804) (nat_lit 13718824819) (nat_lit 0) A10K2.t4469 from rfl, totK_node, tot4468, tot4469]
  decide +kernel

theorem arows4463 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4463 = true := by
  rw [show A10K2.u4463 = KTree.node A10K2.t4470 (nat_lit 71973651) (nat_lit 10561199254) (nat_lit 0) A10K2.t4471 from rfl, allE_node, rows4470, irow4463, rows4471]
  all_goals rfl

theorem atot4463 : totK PA10K2 A10K2.u4463 = [423410675469, 1992269557384, 3681494621129, 2789068689729, 606557963964, 31768748853, 0, 0, 0, 0] := by
  rw [show A10K2.u4463 = KTree.node A10K2.t4470 (nat_lit 71973651) (nat_lit 10561199254) (nat_lit 0) A10K2.t4471 from rfl, totK_node, tot4470, tot4471]
  decide +kernel

theorem arows4466 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4466 = true := by
  rw [show A10K2.u4466 = KTree.node A10K2.t4472 (nat_lit 71979072) (nat_lit 15361014658) (nat_lit 0) A10K2.t4473 from rfl, allE_node, rows4472, irow4466, rows4473]
  all_goals rfl

theorem atot4466 : totK PA10K2 A10K2.u4466 = [366559876416, 2370553800605, 4275879733186, 2183266916353, 217148448047, 0, 0, 0, 0, 0] := by
  rw [show A10K2.u4466 = KTree.node A10K2.t4472 (nat_lit 71979072) (nat_lit 15361014658) (nat_lit 0) A10K2.t4473 from rfl, totK_node, tot4472, tot4473]
  decide +kernel

theorem arows4467 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4467 = true := by
  rw [show A10K2.u4467 = KTree.node A10K2.t4474 (nat_lit 72000667) (nat_lit 10068108498) (nat_lit 0) A10K2.t4475 from rfl, allE_node, rows4474, irow4467, rows4475]
  all_goals rfl

theorem atot4467 : totK PA10K2 A10K2.u4467 = [0, 1050273162140, 3683847885539, 3715382099287, 1046641287853, 64458694438, 0, 0, 0, 0] := by
  rw [show A10K2.u4467 = KTree.node A10K2.t4474 (nat_lit 72000667) (nat_lit 10068108498) (nat_lit 0) A10K2.t4475 from rfl, totK_node, tot4474, tot4475]
  decide +kernel

theorem arows4469 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4469 = true := by
  rw [show A10K2.u4469 = KTree.node A10K2.t4476 (nat_lit 72008584) (nat_lit 13358423910) (nat_lit 0) A10K2.t4477 from rfl, allE_node, rows4476, irow4469, rows4477]
  all_goals rfl

theorem atot4469 : totK PA10K2 A10K2.u4469 = [0, 1001606562601, 3638773380798, 3788032272277, 1027346291534, 63495312472, 0, 0, 0, 0] := by
  rw [show A10K2.u4469 = KTree.node A10K2.t4476 (nat_lit 72008584) (nat_lit 13358423910) (nat_lit 0) A10K2.t4477 from rfl, totK_node, tot4476, tot4477]
  decide +kernel

theorem arows4470 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4470 = true := by
  rw [show A10K2.u4470 = KTree.node A10K2.t4478 (nat_lit 72014380) (nat_lit 13000484332) (nat_lit 0) A10K2.t4479 from rfl, allE_node, rows4478, irow4470, rows4479]
  all_goals rfl

theorem atot4470 : totK PA10K2 A10K2.u4470 = [280546762594, 1285897854770, 2729970719149, 3383942759855, 1667706427268, 265773289542, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u4470 = KTree.node A10K2.t4478 (nat_lit 72014380) (nat_lit 13000484332) (nat_lit 0) A10K2.t4479 from rfl, totK_node, tot4478, tot4479]
  decide +kernel

theorem arows4477 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4477 = true := by
  rw [show A10K2.u4477 = KTree.node A10K2.t4480 (nat_lit 72035090) (nat_lit 14509021569) (nat_lit 0) A10K2.t4481 from rfl, allE_node, rows4480, irow4477, rows4481]
  all_goals rfl

theorem atot4477 : totK PA10K2 A10K2.u4477 = [812330024267, 3266210419189, 4110015729896, 1636196611927, 149088150929, 0, 0, 0, 0, 0] := by
  rw [show A10K2.u4477 = KTree.node A10K2.t4480 (nat_lit 72035090) (nat_lit 14509021569) (nat_lit 0) A10K2.t4481 from rfl, totK_node, tot4480, tot4481]
  decide +kernel

theorem arows4478 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4478 = true := by
  rw [show A10K2.u4478 = KTree.node A10K2.t4482 (nat_lit 72039878) (nat_lit 15630658893) (nat_lit 0) A10K2.t4483 from rfl, allE_node, rows4482, irow4478, rows4483]
  all_goals rfl

theorem atot4478 : totK PA10K2 A10K2.u4478 = [517935020351, 2364315136478, 3945385612742, 2654767329945, 583431382138, 31747192500, 0, 0, 0, 0] := by
  rw [show A10K2.u4478 = KTree.node A10K2.t4482 (nat_lit 72039878) (nat_lit 15630658893) (nat_lit 0) A10K2.t4483 from rfl, totK_node, tot4482, tot4483]
  decide +kernel

theorem arows4480 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4480 = true := by
  rw [show A10K2.u4480 = KTree.node A10K2.t4484 (nat_lit 72053646) (nat_lit 14876300518) (nat_lit 0) A10K2.t4485 from rfl, allE_node, rows4484, irow4480, rows4485]
  all_goals rfl

theorem atot4480 : totK PA10K2 A10K2.u4480 = [281487785300, 1903906815377, 4088900780193, 3106513115194, 646167988853, 19708922258, 0, 0, 0, 0] := by
  rw [show A10K2.u4480 = KTree.node A10K2.t4484 (nat_lit 72053646) (nat_lit 14876300518) (nat_lit 0) A10K2.t4485 from rfl, totK_node, tot4484, tot4485]
  decide +kernel

theorem arows4481 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4481 = true := by
  rw [show A10K2.u4481 = KTree.node A10K2.t4486 (nat_lit 72064211) (nat_lit 9393977099) (nat_lit 0) A10K2.t4487 from rfl, allE_node, rows4486, irow4481, rows4487]
  all_goals rfl

theorem atot4481 : totK PA10K2 A10K2.u4481 = [0, 794766333994, 3213867536217, 4107630023682, 1804540813753, 175915464323, 0, 0, 0, 0] := by
  rw [show A10K2.u4481 = KTree.node A10K2.t4486 (nat_lit 72064211) (nat_lit 9393977099) (nat_lit 0) A10K2.t4487 from rfl, totK_node, tot4486, tot4487]
  decide +kernel

theorem arows4484 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4484 = true := by
  rw [show A10K2.u4484 = KTree.node A10K2.t4488 (nat_lit 72070444) (nat_lit 11823921282) (nat_lit 0) A10K2.t4489 from rfl, allE_node, rows4488, irow4484, rows4489]
  all_goals rfl

theorem atot4484 : totK PA10K2 A10K2.u4484 = [0, 489002362713, 2463078984252, 4202942424823, 2401988234324, 338624184834, 7047025452, 0, 0, 0] := by
  rw [show A10K2.u4484 = KTree.node A10K2.t4488 (nat_lit 72070444) (nat_lit 11823921282) (nat_lit 0) A10K2.t4489 from rfl, totK_node, tot4488, tot4489]
  decide +kernel

theorem arows4485 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4485 = true := by
  rw [show A10K2.u4485 = KTree.node A10K2.t4490 (nat_lit 72084865) (nat_lit 9982413561) (nat_lit 0) A10K2.t4491 from rfl, allE_node, rows4490, irow4485, rows4491]
  all_goals rfl

theorem atot4485 : totK PA10K2 A10K2.u4485 = [0, 606928932868, 2921211940442, 4233849974298, 2025726580590, 273404326601, 6066958478, 0, 0, 0] := by
  rw [show A10K2.u4485 = KTree.node A10K2.t4490 (nat_lit 72084865) (nat_lit 9982413561) (nat_lit 0) A10K2.t4491 from rfl, totK_node, tot4490, tot4491]
  decide +kernel

theorem arows4487 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4487 = true := by
  rw [show A10K2.u4487 = KTree.node A10K2.t4492 (nat_lit 72089591) (nat_lit 14899910164) (nat_lit 0) A10K2.t4493 from rfl, allE_node, rows4492, irow4487, rows4493]
  all_goals rfl

theorem atot4487 : totK PA10K2 A10K2.u4487 = [0, 582386665861, 2372953252623, 3516514680432, 2504648912087, 735006938825, 55043167628, 0, 0, 0] := by
  rw [show A10K2.u4487 = KTree.node A10K2.t4492 (nat_lit 72089591) (nat_lit 14899910164) (nat_lit 0) A10K2.t4493 from rfl, totK_node, tot4492, tot4493]
  decide +kernel

theorem arows4488 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4488 = true := by
  rw [show A10K2.u4488 = KTree.node A10K2.t4494 (nat_lit 72168801) (nat_lit 4792600491) (nat_lit 0) A10K2.t4495 from rfl, allE_node, rows4494, irow4488, rows4495]
  all_goals rfl

theorem atot4488 : totK PA10K2 A10K2.u4488 = [0, 287423613328, 1932817352369, 4016898321888, 2791118365649, 571132695524, 31768748853, 0, 0, 0] := by
  rw [show A10K2.u4488 = KTree.node A10K2.t4494 (nat_lit 72168801) (nat_lit 4792600491) (nat_lit 0) A10K2.t4495 from rfl, totK_node, tot4494, tot4495]
  decide +kernel

theorem arows4492 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4492 = true := by
  rw [show A10K2.u4492 = KTree.node A10K2.t4496 (nat_lit 72173332) (nat_lit 13049808624) (nat_lit 0) A10K2.t4497 from rfl, allE_node, rows4496, irow4492, rows4497]
  all_goals rfl

theorem atot4492 : totK PA10K2 A10K2.u4492 = [0, 727445964447, 3114136758845, 3966357336342, 1536328337191, 126828849724, 0, 0, 0, 0] := by
  rw [show A10K2.u4492 = KTree.node A10K2.t4496 (nat_lit 72173332) (nat_lit 13049808624) (nat_lit 0) A10K2.t4497 from rfl, totK_node, tot4496, tot4497]
  decide +kernel

theorem arows4493 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4493 = true := by
  rw [show A10K2.u4493 = KTree.node A10K2.t4498 (nat_lit 72180919) (nat_lit 14583484606) (nat_lit 0) A10K2.t4499 from rfl, allE_node, rows4498, irow4493, rows4499]
  all_goals rfl

theorem atot4493 : totK PA10K2 A10K2.u4493 = [0, 742488449518, 2957558115214, 3939823468019, 1758801228441, 213105306015, 6239673734, 0, 0, 0] := by
  rw [show A10K2.u4493 = KTree.node A10K2.t4498 (nat_lit 72180919) (nat_lit 14583484606) (nat_lit 0) A10K2.t4499 from rfl, totK_node, tot4498, tot4499]
  decide +kernel

theorem arows4495 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4495 = true := by
  rw [show A10K2.u4495 = KTree.node A10K2.t4500 (nat_lit 72186886) (nat_lit 15385015361) (nat_lit 0) A10K2.t4501 from rfl, allE_node, rows4500, irow4495, rows4501]
  all_goals rfl

theorem atot4495 : totK PA10K2 A10K2.u4495 = [0, 0, 1240447591470, 4112222778969, 3690490045741, 873094709887, 41062513076, 0, 0, 0] := by
  rw [show A10K2.u4495 = KTree.node A10K2.t4500 (nat_lit 72186886) (nat_lit 15385015361) (nat_lit 0) A10K2.t4501 from rfl, totK_node, tot4500, tot4501]
  decide +kernel

theorem arows4496 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4496 = true := by
  rw [show A10K2.u4496 = KTree.node A10K2.t4502 (nat_lit 72199610) (nat_lit 14470741792) (nat_lit 0) A10K2.t4503 from rfl, allE_node, rows4502, irow4496, rows4503]
  all_goals rfl

theorem atot4496 : totK PA10K2 A10K2.u4496 = [0, 0, 542496059800, 2592597962121, 3899062875831, 2013540078187, 397832539392, 25565504801, 0, 0] := by
  rw [show A10K2.u4496 = KTree.node A10K2.t4502 (nat_lit 72199610) (nat_lit 14470741792) (nat_lit 0) A10K2.t4503 from rfl, totK_node, tot4502, tot4503]
  decide +kernel

theorem arows4499 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4499 = true := by
  rw [show A10K2.u4499 = KTree.node A10K2.t4504 (nat_lit 72205470) (nat_lit 13985280109) (nat_lit 0) A10K2.t4505 from rfl, allE_node, rows4504, irow4499, rows4505]
  all_goals rfl

theorem atot4499 : totK PA10K2 A10K2.u4499 = [0, 0, 720927804537, 2984862237731, 3756311699983, 1596474279038, 221703517211, 5453062850, 0, 0] := by
  rw [show A10K2.u4499 = KTree.node A10K2.t4504 (nat_lit 72205470) (nat_lit 13985280109) (nat_lit 0) A10K2.t4505 from rfl, totK_node, tot4504, tot4505]
  decide +kernel

theorem arows4500 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4500 = true := by
  rw [show A10K2.u4500 = KTree.node A10K2.t4506 (nat_lit 72211229) (nat_lit 6260748487) (nat_lit 0) A10K2.t4507 from rfl, allE_node, rows4506, irow4500, rows4507]
  all_goals rfl

theorem atot4500 : totK PA10K2 A10K2.u4500 = [0, 0, 693436352492, 2806806768307, 3938244758153, 1774827971530, 220211641996, 5685526223, 0, 0] := by
  rw [show A10K2.u4500 = KTree.node A10K2.t4506 (nat_lit 72211229) (nat_lit 6260748487) (nat_lit 0) A10K2.t4507 from rfl, totK_node, tot4506, tot4507]
  decide +kernel

theorem arows4502 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4502 = true := by
  rw [show A10K2.u4502 = KTree.node A10K2.t4508 (nat_lit 72222984) (nat_lit 13716224831) (nat_lit 0) A10K2.t4509 from rfl, allE_node, rows4508, irow4502, rows4509]
  all_goals rfl

theorem atot4502 : totK PA10K2 A10K2.u4502 = [0, 468537272203, 2206678454943, 3732904620102, 2492956886675, 580576421134, 31276155898, 0, 0, 0] := by
  rw [show A10K2.u4502 = KTree.node A10K2.t4508 (nat_lit 72222984) (nat_lit 13716224831) (nat_lit 0) A10K2.t4509 from rfl, totK_node, tot4508, tot4509]
  decide +kernel

theorem arows4503 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4503 = true := by
  rw [show A10K2.u4503 = KTree.node A10K2.t4510 (nat_lit 72231580) (nat_lit 11811204118) (nat_lit 0) A10K2.t4511 from rfl, allE_node, rows4510, irow4503, rows4511]
  all_goals rfl

theorem atot4503 : totK PA10K2 A10K2.u4503 = [0, 799877054642, 3231583130540, 4085188234333, 1618271126641, 140170276869, 5460492893, 0, 0, 0] := by
  rw [show A10K2.u4503 = KTree.node A10K2.t4510 (nat_lit 72231580) (nat_lit 11811204118) (nat_lit 0) A10K2.t4511 from rfl, totK_node, tot4510, tot4511]
  decide +kernel

theorem arows4508 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4508 = true := by
  rw [show A10K2.u4508 = KTree.node A10K2.t4512 (nat_lit 72237092) (nat_lit 13324647755) (nat_lit 0) A10K2.t4513 from rfl, allE_node, rows4512, irow4508, rows4513]
  all_goals rfl

theorem atot4508 : totK PA10K2 A10K2.u4508 = [0, 491707397545, 2258457960201, 3668262641573, 2464634548246, 548952496216, 31768748853, 0, 0, 0] := by
  rw [show A10K2.u4508 = KTree.node A10K2.t4512 (nat_lit 72237092) (nat_lit 13324647755) (nat_lit 0) A10K2.t4513 from rfl, totK_node, tot4512, tot4513]
  decide +kernel

theorem arows4509 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4509 = true := by
  rw [show A10K2.u4509 = KTree.node A10K2.t4514 (nat_lit 72242467) (nat_lit 10289999058) (nat_lit 0) A10K2.t4515 from rfl, allE_node, rows4514, irow4509, rows4515]
  all_goals rfl

theorem atot4509 : totK PA10K2 A10K2.u4509 = [0, 298263154340, 2082265423821, 4131298866664, 2447017082358, 349343352035, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u4509 = KTree.node A10K2.t4514 (nat_lit 72242467) (nat_lit 10289999058) (nat_lit 0) A10K2.t4515 from rfl, totK_node, tot4514, tot4515]
  decide +kernel

theorem arows4511 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4511 = true := by
  rw [show A10K2.u4511 = KTree.node A10K2.t4516 (nat_lit 72263400) (nat_lit 4208830913) (nat_lit 0) A10K2.t4517 from rfl, allE_node, rows4516, irow4511, rows4517]
  all_goals rfl

theorem atot4511 : totK PA10K2 A10K2.u4511 = [0, 0, 1061724207470, 3761952294760, 3799048326360, 904277213730, 43864921862, 0, 0, 0] := by
  rw [show A10K2.u4511 = KTree.node A10K2.t4516 (nat_lit 72263400) (nat_lit 4208830913) (nat_lit 0) A10K2.t4517 from rfl, totK_node, tot4516, tot4517]
  decide +kernel

theorem arows4512 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4512 = true := by
  rw [show A10K2.u4512 = KTree.node A10K2.t4518 (nat_lit 72271715) (nat_lit 9256583585) (nat_lit 0) A10K2.t4519 from rfl, allE_node, rows4518, irow4512, rows4519]
  all_goals rfl

theorem atot4512 : totK PA10K2 A10K2.u4512 = [0, 0, 785154310839, 3339161994688, 3931258960538, 1139493514692, 75726602420, 0, 0, 0] := by
  rw [show A10K2.u4512 = KTree.node A10K2.t4518 (nat_lit 72271715) (nat_lit 9256583585) (nat_lit 0) A10K2.t4519 from rfl, totK_node, tot4518, tot4519]
  decide +kernel

theorem arows4515 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4515 = true := by
  rw [show A10K2.u4515 = KTree.node A10K2.t4520 (nat_lit 72289906) (nat_lit 11052421359) (nat_lit 0) A10K2.t4521 from rfl, allE_node, rows4520, irow4515, rows4521]
  all_goals rfl

theorem atot4515 : totK PA10K2 A10K2.u4515 = [0, 590805433127, 2258998525527, 3182499729088, 2520580870868, 1067180961266, 176749557325, 6239673734, 0, 0] := by
  rw [show A10K2.u4515 = KTree.node A10K2.t4520 (nat_lit 72289906) (nat_lit 11052421359) (nat_lit 0) A10K2.t4521 from rfl, totK_node, tot4520, tot4521]
  decide +kernel

theorem arows4516 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4516 = true := by
  rw [show A10K2.u4516 = KTree.node A10K2.t4522 (nat_lit 72298169) (nat_lit 5554587333) (nat_lit 0) A10K2.t4523 from rfl, allE_node, rows4522, irow4516, rows4523]
  all_goals rfl

theorem atot4516 : totK PA10K2 A10K2.u4516 = [0, 498968294647, 2532152927567, 4085327915059, 2261439665945, 428015247373, 25660650750, 0, 0, 0] := by
  rw [show A10K2.u4516 = KTree.node A10K2.t4522 (nat_lit 72298169) (nat_lit 5554587333) (nat_lit 0) A10K2.t4523 from rfl, totK_node, tot4522, tot4523]
  decide +kernel

theorem arows4518 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4518 = true := by
  rw [show A10K2.u4518 = KTree.node A10K2.t4524 (nat_lit 72312099) (nat_lit 10277341493) (nat_lit 0) A10K2.t4525 from rfl, allE_node, rows4524, irow4518, rows4525]
  all_goals rfl

theorem atot4518 : totK PA10K2 A10K2.u4518 = [0, 798499989054, 3137212880598, 3998790279295, 1839357046062, 244944789037, 5624717336, 0, 0, 0] := by
  rw [show A10K2.u4518 = KTree.node A10K2.t4524 (nat_lit 72312099) (nat_lit 10277341493) (nat_lit 0) A10K2.t4525 from rfl, totK_node, tot4524, tot4525]
  decide +kernel

theorem arows4519 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4519 = true := by
  rw [show A10K2.u4519 = KTree.node A10K2.t4526 (nat_lit 72317953) (nat_lit 10226759303) (nat_lit 0) A10K2.t4527 from rfl, allE_node, rows4526, irow4519, rows4527]
  all_goals rfl

theorem atot4519 : totK PA10K2 A10K2.u4519 = [301604122727, 764078323321, 1312497155903, 3257967090373, 3386068769131, 999541831849, 62382159641, 0, 0, 0] := by
  rw [show A10K2.u4519 = KTree.node A10K2.t4526 (nat_lit 72317953) (nat_lit 10226759303) (nat_lit 0) A10K2.t4527 from rfl, totK_node, tot4526, tot4527]
  decide +kernel

theorem arows4523 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4523 = true := by
  rw [show A10K2.u4523 = KTree.node A10K2.t4528 (nat_lit 72355313) (nat_lit 8621216862) (nat_lit 0) A10K2.t4529 from rfl, allE_node, rows4528, irow4523, rows4529]
  all_goals rfl

theorem atot4523 : totK PA10K2 A10K2.u4523 = [458361379514, 2470146716361, 4083934481938, 2246672022438, 425242345806, 25371180993, 0, 0, 0, 0] := by
  rw [show A10K2.u4523 = KTree.node A10K2.t4528 (nat_lit 72355313) (nat_lit 8621216862) (nat_lit 0) A10K2.t4529 from rfl, totK_node, tot4528, tot4529]
  decide +kernel

theorem arows4524 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4524 = true := by
  rw [show A10K2.u4524 = KTree.node A10K2.t4530 (nat_lit 72368938) (nat_lit 9688560109) (nat_lit 0) A10K2.t4531 from rfl, allE_node, rows4530, irow4524, rows4531]
  all_goals rfl

theorem atot4524 : totK PA10K2 A10K2.u4524 = [778695291548, 3080666460174, 3839122948078, 1724788479832, 241184745270, 5460492893, 0, 0, 0, 0] := by
  rw [show A10K2.u4524 = KTree.node A10K2.t4530 (nat_lit 72368938) (nat_lit 9688560109) (nat_lit 0) A10K2.t4531 from rfl, totK_node, tot4530, tot4531]
  decide +kernel

theorem arows4526 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4526 = true := by
  rw [show A10K2.u4526 = KTree.node A10K2.t4532 (nat_lit 72374949) (nat_lit 7279318189) (nat_lit 0) A10K2.t4533 from rfl, allE_node, rows4532, irow4526, rows4533]
  all_goals rfl

theorem atot4526 : totK PA10K2 A10K2.u4526 = [0, 1383506445618, 4243542539992, 3240583515158, 654747119931, 32021558464, 0, 0, 0, 0] := by
  rw [show A10K2.u4526 = KTree.node A10K2.t4532 (nat_lit 72374949) (nat_lit 7279318189) (nat_lit 0) A10K2.t4533 from rfl, totK_node, tot4532, tot4533]
  decide +kernel

theorem arows4527 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4527 = true := by
  rw [show A10K2.u4527 = KTree.node A10K2.t4534 (nat_lit 72389156) (nat_lit 12560932107) (nat_lit 0) A10K2.t4535 from rfl, allE_node, rows4534, irow4527, rows4535]
  all_goals rfl

theorem atot4527 : totK PA10K2 A10K2.u4527 = [0, 298265148177, 1950967024323, 3986367314713, 2670712910418, 555358256481, 30650496230, 0, 0, 0] := by
  rw [show A10K2.u4527 = KTree.node A10K2.t4534 (nat_lit 72389156) (nat_lit 12560932107) (nat_lit 0) A10K2.t4535 from rfl, totK_node, tot4534, tot4535]
  decide +kernel

theorem arows4530 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4530 = true := by
  rw [show A10K2.u4530 = KTree.node A10K2.t4536 (nat_lit 72403102) (nat_lit 9530656595) (nat_lit 0) A10K2.t4537 from rfl, allE_node, rows4536, irow4530, rows4537]
  all_goals rfl

theorem atot4530 : totK PA10K2 A10K2.u4530 = [0, 667270778467, 3206650945787, 4206463003681, 1416850426505, 96935201668, 0, 0, 0, 0] := by
  rw [show A10K2.u4530 = KTree.node A10K2.t4536 (nat_lit 72403102) (nat_lit 9530656595) (nat_lit 0) A10K2.t4537 from rfl, totK_node, tot4536, tot4537]
  decide +kernel

theorem arows4531 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4531 = true := by
  rw [show A10K2.u4531 = KTree.node A10K2.t4538 (nat_lit 72427441) (nat_lit 5399407213) (nat_lit 0) A10K2.t4539 from rfl, allE_node, rows4538, irow4531, rows4539]
  all_goals rfl

theorem atot4531 : totK PA10K2 A10K2.u4531 = [836243354860, 3016308934386, 3255717617569, 1593373679110, 699632601733, 133756988527, 5546304973, 0, 0, 0] := by
  rw [show A10K2.u4531 = KTree.node A10K2.t4538 (nat_lit 72427441) (nat_lit 5399407213) (nat_lit 0) A10K2.t4539 from rfl, totK_node, tot4538, tot4539]
  decide +kernel

theorem arows4533 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4533 = true := by
  rw [show A10K2.u4533 = KTree.node A10K2.t4540 (nat_lit 72431959) (nat_lit 5589189278) (nat_lit 0) A10K2.t4541 from rfl, allE_node, rows4540, irow4533, rows4541]
  all_goals rfl

theorem atot4533 : totK PA10K2 A10K2.u4533 = [299996936876, 1766687482917, 3806634840529, 3004952707523, 639167503202, 31768748853, 0, 0, 0, 0] := by
  rw [show A10K2.u4533 = KTree.node A10K2.t4540 (nat_lit 72431959) (nat_lit 5589189278) (nat_lit 0) A10K2.t4541 from rfl, totK_node, tot4540, tot4541]
  decide +kernel

theorem arows4534 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4534 = true := by
  rw [show A10K2.u4534 = KTree.node A10K2.t4542 (nat_lit 72436507) (nat_lit 8679776884) (nat_lit 0) A10K2.t4543 from rfl, allE_node, rows4542, irow4534, rows4543]
  all_goals rfl

theorem atot4534 : totK PA10K2 A10K2.u4534 = [470692171148, 2662188901394, 4311268946026, 1938747267534, 175378113633, 0, 0, 0, 0, 0] := by
  rw [show A10K2.u4534 = KTree.node A10K2.t4542 (nat_lit 72436507) (nat_lit 8679776884) (nat_lit 0) A10K2.t4543 from rfl, totK_node, tot4542, tot4543]
  decide +kernel

theorem arows4540 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4540 = true := by
  rw [show A10K2.u4540 = KTree.node A10K2.t4544 (nat_lit 72445431) (nat_lit 15000730224) (nat_lit 0) A10K2.t4545 from rfl, allE_node, rows4544, irow4540, rows4545]
  all_goals rfl

theorem atot4540 : totK PA10K2 A10K2.u4540 = [554803763168, 2511703377175, 3961246047060, 2425611271388, 449017046973, 13317224979, 0, 0, 0, 0] := by
  rw [show A10K2.u4540 = KTree.node A10K2.t4544 (nat_lit 72445431) (nat_lit 15000730224) (nat_lit 0) A10K2.t4545 from rfl, totK_node, tot4544, tot4545]
  decide +kernel

theorem arows4541 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4541 = true := by
  rw [show A10K2.u4541 = KTree.node A10K2.t4546 (nat_lit 72460186) (nat_lit 14931092400) (nat_lit 0) A10K2.t4547 from rfl, allE_node, rows4546, irow4541, rows4547]
  all_goals rfl

theorem atot4541 : totK PA10K2 A10K2.u4541 = [0, 916405558426, 3505299158589, 3932144370378, 1232078037034, 82086433447, 0, 0, 0, 0] := by
  rw [show A10K2.u4541 = KTree.node A10K2.t4546 (nat_lit 72460186) (nat_lit 14931092400) (nat_lit 0) A10K2.t4547 from rfl, totK_node, tot4546, tot4547]
  decide +kernel

theorem arows4543 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4543 = true := by
  rw [show A10K2.u4543 = KTree.node A10K2.t4548 (nat_lit 72464748) (nat_lit 12343120072) (nat_lit 0) A10K2.t4549 from rfl, allE_node, rows4548, irow4543, rows4549]
  all_goals rfl

theorem atot4543 : totK PA10K2 A10K2.u4543 = [0, 400871179982, 2017381202476, 3774523609666, 2672304706857, 570387575348, 31082886609, 0, 0, 0] := by
  rw [show A10K2.u4543 = KTree.node A10K2.t4548 (nat_lit 72464748) (nat_lit 12343120072) (nat_lit 0) A10K2.t4549 from rfl, totK_node, tot4548, tot4549]
  decide +kernel

theorem arows4544 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4544 = true := by
  rw [show A10K2.u4544 = KTree.node A10K2.t4550 (nat_lit 72470573) (nat_lit 5999642436) (nat_lit 0) A10K2.t4551 from rfl, allE_node, rows4550, irow4544, rows4551]
  all_goals rfl

theorem atot4544 : totK PA10K2 A10K2.u4544 = [0, 412100876061, 2440418604844, 4215128274444, 2063902918620, 245885793701, 6121173289, 0, 0, 0] := by
  rw [show A10K2.u4544 = KTree.node A10K2.t4550 (nat_lit 72470573) (nat_lit 5999642436) (nat_lit 0) A10K2.t4551 from rfl, totK_node, tot4550, tot4551]
  decide +kernel

theorem arows4547 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4547 = true := by
  rw [show A10K2.u4547 = KTree.node A10K2.t4552 (nat_lit 72478437) (nat_lit 4821907243) (nat_lit 0) A10K2.t4553 from rfl, allE_node, rows4552, irow4547, rows4553]
  all_goals rfl

theorem atot4547 : totK PA10K2 A10K2.u4547 = [557742759892, 2176097650268, 3436034058944, 2701022301690, 863617970002, 69768510777, 0, 0, 0, 0] := by
  rw [show A10K2.u4547 = KTree.node A10K2.t4552 (nat_lit 72478437) (nat_lit 4821907243) (nat_lit 0) A10K2.t4553 from rfl, totK_node, tot4552, tot4553]
  decide +kernel

theorem arows4548 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4548 = true := by
  rw [show A10K2.u4548 = KTree.node A10K2.t4554 (nat_lit 72487863) (nat_lit 11004859784) (nat_lit 0) A10K2.t4555 from rfl, allE_node, rows4554, irow4548, rows4555]
  all_goals rfl

theorem atot4548 : totK PA10K2 A10K2.u4548 = [393585523161, 2239532190305, 3927816239199, 2467580645264, 522173947078, 30831673886, 0, 0, 0, 0] := by
  rw [show A10K2.u4548 = KTree.node A10K2.t4554 (nat_lit 72487863) (nat_lit 11004859784) (nat_lit 0) A10K2.t4555 from rfl, totK_node, tot4554, tot4555]
  decide +kernel

theorem arows4550 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4550 = true := by
  rw [show A10K2.u4550 = KTree.node A10K2.t4556 (nat_lit 72494764) (nat_lit 11391364243) (nat_lit 0) A10K2.t4557 from rfl, allE_node, rows4556, irow4550, rows4557]
  all_goals rfl

theorem atot4550 : totK PA10K2 A10K2.u4550 = [465631835236, 2423159657509, 4016150337309, 2286607375412, 443186293961, 25734533292, 0, 0, 0, 0] := by
  rw [show A10K2.u4550 = KTree.node A10K2.t4556 (nat_lit 72494764) (nat_lit 11391364243) (nat_lit 0) A10K2.t4557 from rfl, totK_node, tot4556, tot4557]
  decide +kernel

theorem arows4551 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4551 = true := by
  rw [show A10K2.u4551 = KTree.node A10K2.t4558 (nat_lit 72500074) (nat_lit 5621894008) (nat_lit 0) A10K2.t4559 from rfl, allE_node, rows4558, irow4551, rows4559]
  all_goals rfl

theorem atot4551 : totK PA10K2 A10K2.u4551 = [837613071177, 3047898175560, 3666342138889, 1738233584990, 251197297366, 6034215561, 0, 0, 0, 0] := by
  rw [show A10K2.u4551 = KTree.node A10K2.t4558 (nat_lit 72500074) (nat_lit 5621894008) (nat_lit 0) A10K2.t4559 from rfl, totK_node, tot4558, tot4559]
  decide +kernel

theorem arows4555 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4555 = true := by
  rw [show A10K2.u4555 = KTree.node A10K2.t4560 (nat_lit 72505605) (nat_lit 7040787894) (nat_lit 0) A10K2.t4561 from rfl, allE_node, rows4560, irow4555, rows4561]
  all_goals rfl

theorem atot4555 : totK PA10K2 A10K2.u4555 = [0, 1418539244143, 4216365929281, 3161683973329, 644447339353, 31987755669, 0, 0, 0, 0] := by
  rw [show A10K2.u4555 = KTree.node A10K2.t4560 (nat_lit 72505605) (nat_lit 7040787894) (nat_lit 0) A10K2.t4561 from rfl, totK_node, tot4560, tot4561]
  decide +kernel

theorem arows4556 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4556 = true := by
  rw [show A10K2.u4556 = KTree.node A10K2.t4562 (nat_lit 72525490) (nat_lit 15220691742) (nat_lit 0) A10K2.t4563 from rfl, allE_node, rows4562, irow4556, rows4563]
  all_goals rfl

theorem atot4556 : totK PA10K2 A10K2.u4556 = [0, 1037481917250, 3758147357921, 3838676860088, 992537893881, 45620856191, 0, 0, 0, 0] := by
  rw [show A10K2.u4556 = KTree.node A10K2.t4562 (nat_lit 72525490) (nat_lit 15220691742) (nat_lit 0) A10K2.t4563 from rfl, totK_node, tot4562, tot4563]
  decide +kernel

theorem arows4558 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4558 = true := by
  rw [show A10K2.u4558 = KTree.node A10K2.t4564 (nat_lit 72533676) (nat_lit 11831981296) (nat_lit 0) A10K2.t4565 from rfl, allE_node, rows4564, irow4558, rows4565]
  all_goals rfl

theorem atot4558 : totK PA10K2 A10K2.u4558 = [0, 833370606894, 3338156578640, 3944794785351, 1197836605668, 83009222198, 0, 0, 0, 0] := by
  rw [show A10K2.u4558 = KTree.node A10K2.t4564 (nat_lit 72533676) (nat_lit 11831981296) (nat_lit 0) A10K2.t4565 from rfl, totK_node, tot4564, tot4565]
  decide +kernel

theorem arows4559 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4559 = true := by
  rw [show A10K2.u4559 = KTree.node A10K2.t4566 (nat_lit 72614164) (nat_lit 12245859697) (nat_lit 0) A10K2.t4567 from rfl, allE_node, rows4566, irow4559, rows4567]
  all_goals rfl

theorem atot4559 : totK PA10K2 A10K2.u4559 = [0, 639151322607, 2780503493861, 3943786350970, 1811817512850, 271945432682, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u4559 = KTree.node A10K2.t4566 (nat_lit 72614164) (nat_lit 12245859697) (nat_lit 0) A10K2.t4567 from rfl, totK_node, tot4566, tot4567]
  decide +kernel

theorem arows4562 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4562 = true := by
  rw [show A10K2.u4562 = KTree.node A10K2.t4568 (nat_lit 72620046) (nat_lit 12434362717) (nat_lit 0) A10K2.t4569 from rfl, allE_node, rows4568, irow4562, rows4569]
  all_goals rfl

theorem atot4562 : totK PA10K2 A10K2.u4562 = [0, 396699628773, 2118026779777, 3883767741218, 2699550160135, 567897508156, 30818366867, 0, 0, 0] := by
  rw [show A10K2.u4562 = KTree.node A10K2.t4568 (nat_lit 72620046) (nat_lit 12434362717) (nat_lit 0) A10K2.t4569 from rfl, totK_node, tot4568, tot4569]
  decide +kernel

theorem arows4563 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4563 = true := by
  rw [show A10K2.u4563 = KTree.node A10K2.t4570 (nat_lit 72632836) (nat_lit 12683970786) (nat_lit 0) A10K2.t4571 from rfl, allE_node, rows4570, irow4563, rows4571]
  all_goals rfl

theorem atot4563 : totK PA10K2 A10K2.u4563 = [0, 500180958923, 2773058192032, 4295649018301, 1806257031755, 157744888523, 0, 0, 0, 0] := by
  rw [show A10K2.u4563 = KTree.node A10K2.t4570 (nat_lit 72632836) (nat_lit 12683970786) (nat_lit 0) A10K2.t4571 from rfl, totK_node, tot4570, tot4571]
  decide +kernel

theorem arows4565 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4565 = true := by
  rw [show A10K2.u4565 = KTree.node A10K2.t4572 (nat_lit 72689813) (nat_lit 6806383869) (nat_lit 0) A10K2.t4573 from rfl, allE_node, rows4572, irow4565, rows4573]
  all_goals rfl

theorem atot4565 : totK PA10K2 A10K2.u4565 = [0, 836243354860, 3089128702129, 3772197079600, 1656706186729, 236742677573, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u4565 = KTree.node A10K2.t4572 (nat_lit 72689813) (nat_lit 6806383869) (nat_lit 0) A10K2.t4573 from rfl, totK_node, tot4572, tot4573]
  decide +kernel

theorem arows4566 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4566 = true := by
  rw [show A10K2.u4566 = KTree.node A10K2.t4574 (nat_lit 72694462) (nat_lit 11045900006) (nat_lit 0) A10K2.t4575 from rfl, allE_node, rows4574, irow4566, rows4575]
  all_goals rfl

theorem atot4566 : totK PA10K2 A10K2.u4566 = [0, 400965813043, 1993032861117, 3740233016027, 2751979798944, 581198791127, 31452573850, 0, 0, 0] := by
  rw [show A10K2.u4566 = KTree.node A10K2.t4574 (nat_lit 72694462) (nat_lit 11045900006) (nat_lit 0) A10K2.t4575 from rfl, totK_node, tot4574, tot4575]
  decide +kernel

theorem arows4571 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4571 = true := by
  rw [show A10K2.u4571 = KTree.node A10K2.t4576 (nat_lit 72699960) (nat_lit 13395788131) (nat_lit 0) A10K2.t4577 from rfl, allE_node, rows4576, irow4571, rows4577]
  all_goals rfl

theorem atot4571 : totK PA10K2 A10K2.u4571 = [0, 369723294981, 2387297737783, 4243661095590, 2208403179347, 270707439789, 0, 0, 0, 0] := by
  rw [show A10K2.u4571 = KTree.node A10K2.t4576 (nat_lit 72699960) (nat_lit 13395788131) (nat_lit 0) A10K2.t4577 from rfl, totK_node, tot4576, tot4577]
  decide +kernel

theorem arows4572 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4572 = true := by
  rw [show A10K2.u4572 = KTree.node A10K2.t4578 (nat_lit 72707796) (nat_lit 9035748410) (nat_lit 0) A10K2.t4579 from rfl, allE_node, rows4578, irow4572, rows4579]
  all_goals rfl

theorem atot4572 : totK PA10K2 A10K2.u4572 = [0, 597452797716, 2648587659380, 4084300714023, 2288492526413, 356901099523, 13317224979, 0, 0, 0] := by
  rw [show A10K2.u4572 = KTree.node A10K2.t4578 (nat_lit 72707796) (nat_lit 9035748410) (nat_lit 0) A10K2.t4579 from rfl, totK_node, tot4578, tot4579]
  decide +kernel

theorem arows4574 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4574 = true := by
  rw [show A10K2.u4574 = KTree.node A10K2.t4580 (nat_lit 72747798) (nat_lit 4813382656) (nat_lit 0) A10K2.t4581 from rfl, allE_node, rows4580, irow4574, rows4581]
  all_goals rfl

theorem atot4574 : totK PA10K2 A10K2.u4574 = [0, 608430609364, 2755553733890, 3909501126150, 1891394885288, 330383417997, 24614390653, 0, 0, 0] := by
  rw [show A10K2.u4574 = KTree.node A10K2.t4580 (nat_lit 72747798) (nat_lit 4813382656) (nat_lit 0) A10K2.t4581 from rfl, totK_node, tot4580, tot4581]
  decide +kernel

theorem arows4575 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4575 = true := by
  rw [show A10K2.u4575 = KTree.node A10K2.t4582 (nat_lit 72755100) (nat_lit 8864228820) (nat_lit 0) A10K2.t4583 from rfl, allE_node, rows4582, irow4575, rows4583]
  all_goals rfl

theorem atot4575 : totK PA10K2 A10K2.u4575 = [0, 764881778263, 3101873106524, 3915224085477, 1657201491459, 195593411641, 5460492893, 0, 0, 0] := by
  rw [show A10K2.u4575 = KTree.node A10K2.t4582 (nat_lit 72755100) (nat_lit 8864228820) (nat_lit 0) A10K2.t4583 from rfl, totK_node, tot4582, tot4583]
  decide +kernel

theorem arows4578 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4578 = true := by
  rw [show A10K2.u4578 = KTree.node A10K2.t4584 (nat_lit 72760147) (nat_lit 8866068140) (nat_lit 0) A10K2.t4585 from rfl, allE_node, rows4584, irow4578, rows4585]
  all_goals rfl

theorem atot4578 : totK PA10K2 A10K2.u4578 = [0, 489656864186, 2141042437265, 3714696560442, 2494337284334, 500776078232, 31003444686, 0, 0, 0] := by
  rw [show A10K2.u4578 = KTree.node A10K2.t4584 (nat_lit 72760147) (nat_lit 8866068140) (nat_lit 0) A10K2.t4585 from rfl, totK_node, tot4584, tot4585]
  decide +kernel

theorem arows4579 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4579 = true := by
  rw [show A10K2.u4579 = KTree.node A10K2.t4586 (nat_lit 72765537) (nat_lit 9986550304) (nat_lit 0) A10K2.t4587 from rfl, allE_node, rows4586, irow4579, rows4587]
  all_goals rfl

theorem atot4579 : totK PA10K2 A10K2.u4579 = [0, 334120399620, 2368849321660, 4313145968816, 2129696022452, 215254261228, 0, 0, 0, 0] := by
  rw [show A10K2.u4579 = KTree.node A10K2.t4586 (nat_lit 72765537) (nat_lit 9986550304) (nat_lit 0) A10K2.t4587 from rfl, totK_node, tot4586, tot4587]
  decide +kernel

theorem arows4581 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4581 = true := by
  rw [show A10K2.u4581 = KTree.node A10K2.t4588 (nat_lit 72780448) (nat_lit 8723241862) (nat_lit 0) A10K2.t4589 from rfl, allE_node, rows4588, irow4581, rows4589]
  all_goals rfl

theorem atot4581 : totK PA10K2 A10K2.u4581 = [0, 0, 1117268067019, 3747188878322, 3568002906300, 934839465623, 62884008615, 0, 0, 0] := by
  rw [show A10K2.u4581 = KTree.node A10K2.t4588 (nat_lit 72780448) (nat_lit 8723241862) (nat_lit 0) A10K2.t4589 from rfl, totK_node, tot4588, tot4589]
  decide +kernel

theorem arows4582 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4582 = true := by
  rw [show A10K2.u4582 = KTree.node A10K2.t4590 (nat_lit 72794925) (nat_lit 6564919360) (nat_lit 0) A10K2.t4591 from rfl, allE_node, rows4590, irow4582, rows4591]
  all_goals rfl

theorem atot4582 : totK PA10K2 A10K2.u4582 = [0, 0, 1112645353415, 3786494717960, 3469386168937, 833596297245, 56464005069, 0, 0, 0] := by
  rw [show A10K2.u4582 = KTree.node A10K2.t4590 (nat_lit 72794925) (nat_lit 6564919360) (nat_lit 0) A10K2.t4591 from rfl, totK_node, tot4590, tot4591]
  decide +kernel

theorem arows4586 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4586 = true := by
  rw [show A10K2.u4586 = KTree.node A10K2.t4592 (nat_lit 72800620) (nat_lit 12782193965) (nat_lit 0) A10K2.t4593 from rfl, allE_node, rows4592, irow4586, rows4593]
  all_goals rfl

theorem atot4586 : totK PA10K2 A10K2.u4586 = [454243131009, 1499791343207, 1447034571903, 1422869785749, 2645824062190, 1583180770802, 265614550179, 6354482628, 0, 0] := by
  rw [show A10K2.u4586 = KTree.node A10K2.t4592 (nat_lit 72800620) (nat_lit 12782193965) (nat_lit 0) A10K2.t4593 from rfl, totK_node, tot4592, tot4593]
  decide +kernel

theorem arows4587 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4587 = true := by
  rw [show A10K2.u4587 = KTree.node A10K2.t4594 (nat_lit 72955059) (nat_lit 10369284172) (nat_lit 0) A10K2.t4595 from rfl, allE_node, rows4594, irow4587, rows4595]
  all_goals rfl

theorem atot4587 : totK PA10K2 A10K2.u4587 = [391328567830, 2151740666563, 3938409380335, 2646213534812, 510557941088, 25734533292, 0, 0, 0, 0] := by
  rw [show A10K2.u4587 = KTree.node A10K2.t4594 (nat_lit 72955059) (nat_lit 10369284172) (nat_lit 0) A10K2.t4595 from rfl, totK_node, tot4594, tot4595]
  decide +kernel

theorem arows4589 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4589 = true := by
  rw [show A10K2.u4589 = KTree.node A10K2.t4596 (nat_lit 72960076) (nat_lit 10973051743) (nat_lit 0) A10K2.t4597 from rfl, allE_node, rows4596, irow4589, rows4597]
  all_goals rfl

theorem atot4589 : totK PA10K2 A10K2.u4589 = [561453450670, 2860958910169, 4221167671879, 1905308115071, 226655868318, 6034215561, 0, 0, 0, 0] := by
  rw [show A10K2.u4589 = KTree.node A10K2.t4596 (nat_lit 72960076) (nat_lit 10973051743) (nat_lit 0) A10K2.t4597 from rfl, totK_node, tot4596, tot4597]
  decide +kernel

theorem arows4590 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4590 = true := by
  rw [show A10K2.u4590 = KTree.node A10K2.t4598 (nat_lit 72967856) (nat_lit 9921287792) (nat_lit 0) A10K2.t4599 from rfl, allE_node, rows4598, irow4590, rows4599]
  all_goals rfl

theorem atot4590 : totK PA10K2 A10K2.u4590 = [804002626082, 3100952784333, 4018639003832, 1857918370479, 273529537043, 6354482628, 0, 0, 0, 0] := by
  rw [show A10K2.u4590 = KTree.node A10K2.t4598 (nat_lit 72967856) (nat_lit 9921287792) (nat_lit 0) A10K2.t4599 from rfl, totK_node, tot4598, tot4599]
  decide +kernel

theorem arows4593 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4593 = true := by
  rw [show A10K2.u4593 = KTree.node A10K2.t4600 (nat_lit 72973697) (nat_lit 9632541362) (nat_lit 0) A10K2.t4601 from rfl, allE_node, rows4600, irow4593, rows4601]
  all_goals rfl

theorem atot4593 : totK PA10K2 A10K2.u4593 = [0, 1001793757863, 3760258293025, 4011303581992, 1216460564859, 83568030839, 0, 0, 0, 0] := by
  rw [show A10K2.u4593 = KTree.node A10K2.t4600 (nat_lit 72973697) (nat_lit 9632541362) (nat_lit 0) A10K2.t4601 from rfl, totK_node, tot4600, tot4601]
  decide +kernel

theorem arows4594 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4594 = true := by
  rw [show A10K2.u4594 = KTree.node A10K2.t4602 (nat_lit 72986297) (nat_lit 4589250929) (nat_lit 0) A10K2.t4603 from rfl, allE_node, rows4602, irow4594, rows4603]
  all_goals rfl

theorem atot4594 : totK PA10K2 A10K2.u4594 = [0, 528087305681, 2548158939457, 3950836479907, 2137760163599, 409965240202, 25565504801, 0, 0, 0] := by
  rw [show A10K2.u4594 = KTree.node A10K2.t4602 (nat_lit 72986297) (nat_lit 4589250929) (nat_lit 0) A10K2.t4603 from rfl, totK_node, tot4602, tot4603]
  decide +kernel

theorem arows4596 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4596 = true := by
  rw [show A10K2.u4596 = KTree.node A10K2.t4604 (nat_lit 72992540) (nat_lit 12033639553) (nat_lit 0) A10K2.t4605 from rfl, allE_node, rows4604, irow4596, rows4605]
  all_goals rfl

theorem atot4596 : totK PA10K2 A10K2.u4596 = [0, 560660701500, 2711318835938, 4102461958999, 1978463177896, 240185366330, 5517381808, 0, 0, 0] := by
  rw [show A10K2.u4596 = KTree.node A10K2.t4604 (nat_lit 72992540) (nat_lit 12033639553) (nat_lit 0) A10K2.t4605 from rfl, totK_node, tot4604, tot4605]
  decide +kernel

theorem arows4597 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4597 = true := by
  rw [show A10K2.u4597 = KTree.node A10K2.t4606 (nat_lit 73000339) (nat_lit 10655606973) (nat_lit 0) A10K2.t4607 from rfl, allE_node, rows4606, irow4597, rows4607]
  all_goals rfl

theorem atot4597 : totK PA10K2 A10K2.u4597 = [0, 803468627007, 3159028306821, 4021615671818, 1716714794088, 213216272182, 6121173289, 0, 0, 0] := by
  rw [show A10K2.u4597 = KTree.node A10K2.t4606 (nat_lit 73000339) (nat_lit 10655606973) (nat_lit 0) A10K2.t4607 from rfl, totK_node, tot4606, tot4607]
  decide +kernel

theorem arows4606 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4606 = true := by
  rw [show A10K2.u4606 = KTree.node A10K2.t4608 (nat_lit 73076273) (nat_lit 9774660780) (nat_lit 0) A10K2.t4609 from rfl, allE_node, rows4608, irow4606, rows4609]
  all_goals rfl

theorem atot4606 : totK PA10K2 A10K2.u4606 = [593238721492, 2651039768333, 3994292300956, 2241187227285, 573882391500, 62896129269, 0, 0, 0, 0] := by
  rw [show A10K2.u4606 = KTree.node A10K2.t4608 (nat_lit 73076273) (nat_lit 9774660780) (nat_lit 0) A10K2.t4609 from rfl, totK_node, tot4608, tot4609]
  decide +kernel

theorem arows4607 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4607 = true := by
  rw [show A10K2.u4607 = KTree.node A10K2.t4610 (nat_lit 73083553) (nat_lit 3298756341) (nat_lit 0) A10K2.t4611 from rfl, allE_node, rows4610, irow4607, rows4611]
  all_goals rfl

theorem atot4607 : totK PA10K2 A10K2.u4607 = [783895901686, 3216861315502, 4101634059625, 1677392418001, 156766664653, 0, 0, 0, 0, 0] := by
  rw [show A10K2.u4607 = KTree.node A10K2.t4610 (nat_lit 73083553) (nat_lit 3298756341) (nat_lit 0) A10K2.t4611 from rfl, totK_node, tot4610, tot4611]
  decide +kernel

theorem arows4609 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4609 = true := by
  rw [show A10K2.u4609 = KTree.node A10K2.t4612 (nat_lit 73088471) (nat_lit 14388399796) (nat_lit 0) A10K2.t4613 from rfl, allE_node, rows4612, irow4609, rows4613]
  all_goals rfl

theorem atot4609 : totK PA10K2 A10K2.u4609 = [538725919627, 2410901689042, 3844071944389, 2525950373460, 559195272214, 31677228370, 0, 0, 0, 0] := by
  rw [show A10K2.u4609 = KTree.node A10K2.t4612 (nat_lit 73088471) (nat_lit 14388399796) (nat_lit 0) A10K2.t4613 from rfl, totK_node, tot4612, tot4613]
  decide +kernel

theorem arows4610 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4610 = true := by
  rw [show A10K2.u4610 = KTree.node A10K2.t4614 (nat_lit 73101703) (nat_lit 14471687564) (nat_lit 0) A10K2.t4615 from rfl, allE_node, rows4614, irow4610, rows4615]
  all_goals rfl

theorem atot4610 : totK PA10K2 A10K2.u4610 = [329616625233, 2090748668674, 4193835320499, 2890560334949, 540866962900, 13816090359, 0, 0, 0, 0] := by
  rw [show A10K2.u4610 = KTree.node A10K2.t4614 (nat_lit 73101703) (nat_lit 14471687564) (nat_lit 0) A10K2.t4615 from rfl, totK_node, tot4614, tot4615]
  decide +kernel

theorem arows4613 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4613 = true := by
  rw [show A10K2.u4613 = KTree.node A10K2.t4616 (nat_lit 73106245) (nat_lit 5947742521) (nat_lit 0) A10K2.t4617 from rfl, allE_node, rows4616, irow4613, rows4617]
  all_goals rfl

theorem atot4613 : totK PA10K2 A10K2.u4613 = [0, 714030428206, 3184659880259, 4323512634310, 1721858196099, 150733428714, 0, 0, 0, 0] := by
  rw [show A10K2.u4613 = KTree.node A10K2.t4616 (nat_lit 73106245) (nat_lit 5947742521) (nat_lit 0) A10K2.t4617 from rfl, totK_node, tot4616, tot4617]
  decide +kernel

theorem arows4614 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4614 = true := by
  rw [show A10K2.u4614 = KTree.node A10K2.t4618 (nat_lit 73115349) (nat_lit 6120383010) (nat_lit 0) A10K2.t4619 from rfl, allE_node, rows4618, irow4614, rows4619]
  all_goals rfl

theorem atot4614 : totK PA10K2 A10K2.u4614 = [0, 782886069660, 3060599705344, 3918014802795, 1888808396660, 286164311099, 6904928264, 0, 0, 0] := by
  rw [show A10K2.u4614 = KTree.node A10K2.t4618 (nat_lit 73115349) (nat_lit 6120383010) (nat_lit 0) A10K2.t4619 from rfl, totK_node, tot4618, tot4619]
  decide +kernel

theorem arows4616 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4616 = true := by
  rw [show A10K2.u4616 = KTree.node A10K2.t4620 (nat_lit 73120951) (nat_lit 14808797364) (nat_lit 0) A10K2.t4621 from rfl, allE_node, rows4620, irow4616, rows4621]
  all_goals rfl

theorem atot4616 : totK PA10K2 A10K2.u4616 = [0, 538280721098, 2578071258648, 4114120553837, 2356714381616, 339682217265, 7047025452, 0, 0, 0] := by
  rw [show A10K2.u4616 = KTree.node A10K2.t4620 (nat_lit 73120951) (nat_lit 14808797364) (nat_lit 0) A10K2.t4621 from rfl, totK_node, tot4620, tot4621]
  decide +kernel

theorem arows4617 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4617 = true := by
  rw [show A10K2.u4617 = KTree.node A10K2.t4622 (nat_lit 73134112) (nat_lit 14074751939) (nat_lit 0) A10K2.t4623 from rfl, allE_node, rows4622, irow4617, rows4623]
  all_goals rfl

theorem atot4617 : totK PA10K2 A10K2.u4617 = [0, 328772566221, 2121256546802, 4225898206319, 2792102457633, 458647460984, 12224107035, 0, 0, 0] := by
  rw [show A10K2.u4617 = KTree.node A10K2.t4622 (nat_lit 73134112) (nat_lit 14074751939) (nat_lit 0) A10K2.t4623 from rfl, totK_node, tot4622, tot4623]
  decide +kernel

theorem arows4621 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4621 = true := by
  rw [show A10K2.u4621 = KTree.node A10K2.t4624 (nat_lit 73213596) (nat_lit 11253491165) (nat_lit 0) A10K2.t4625 from rfl, allE_node, rows4624, irow4621, rows4625]
  all_goals rfl

theorem atot4621 : totK PA10K2 A10K2.u4621 = [0, 845571698839, 2947958082557, 3443176457993, 1904407147273, 554648791192, 48886019071, 0, 0, 0] := by
  rw [show A10K2.u4621 = KTree.node A10K2.t4624 (nat_lit 73213596) (nat_lit 11253491165) (nat_lit 0) A10K2.t4625 from rfl, totK_node, tot4624, tot4625]
  decide +kernel

theorem arows4622 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4622 = true := by
  rw [show A10K2.u4622 = KTree.node A10K2.t4626 (nat_lit 73218093) (nat_lit 6481320594) (nat_lit 0) A10K2.t4627 from rfl, allE_node, rows4626, irow4622, rows4627]
  all_goals rfl

theorem atot4622 : totK PA10K2 A10K2.u4622 = [0, 251280892394, 1822477733295, 4007992074864, 3023366625263, 623232760029, 31306924438, 0, 0, 0] := by
  rw [show A10K2.u4622 = KTree.node A10K2.t4626 (nat_lit 73218093) (nat_lit 6481320594) (nat_lit 0) A10K2.t4627 from rfl, totK_node, tot4626, tot4627]
  decide +kernel

theorem arows4624 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4624 = true := by
  rw [show A10K2.u4624 = KTree.node A10K2.t4628 (nat_lit 73225484) (nat_lit 11558615054) (nat_lit 0) A10K2.t4629 from rfl, allE_node, rows4628, irow4624, rows4629]
  all_goals rfl

theorem atot4624 : totK PA10K2 A10K2.u4624 = [0, 501934543418, 2707369976074, 4227120586306, 1999494565208, 246512957262, 6239673734, 0, 0, 0] := by
  rw [show A10K2.u4624 = KTree.node A10K2.t4628 (nat_lit 73225484) (nat_lit 11558615054) (nat_lit 0) A10K2.t4629 from rfl, totK_node, tot4628, tot4629]
  decide +kernel

theorem arows4625 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4625 = true := by
  rw [show A10K2.u4625 = KTree.node A10K2.t4630 (nat_lit 73231927) (nat_lit 14895522512) (nat_lit 0) A10K2.t4631 from rfl, allE_node, rows4630, irow4625, rows4631]
  all_goals rfl

theorem atot4625 : totK PA10K2 A10K2.u4625 = [0, 612240640940, 2736484628047, 4170511358293, 2295590616108, 346713360156, 6279851884, 0, 0, 0] := by
  rw [show A10K2.u4625 = KTree.node A10K2.t4630 (nat_lit 73231927) (nat_lit 14895522512) (nat_lit 0) A10K2.t4631 from rfl, totK_node, tot4630, tot4631]
  decide +kernel

theorem arows4628 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4628 = true := by
  rw [show A10K2.u4628 = KTree.node A10K2.t4632 (nat_lit 73245973) (nat_lit 6901166278) (nat_lit 0) A10K2.t4633 from rfl, allE_node, rows4632, irow4628, rows4633]
  all_goals rfl

theorem atot4628 : totK PA10K2 A10K2.u4628 = [0, 0, 972735455438, 3572271869959, 3917788857060, 1233184360965, 87826231206, 0, 0, 0] := by
  rw [show A10K2.u4628 = KTree.node A10K2.t4632 (nat_lit 73245973) (nat_lit 6901166278) (nat_lit 0) A10K2.t4633 from rfl, totK_node, tot4632, tot4633]
  decide +kernel

theorem arows4629 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4629 = true := by
  rw [show A10K2.u4629 = KTree.node A10K2.t4634 (nat_lit 73250587) (nat_lit 6208686633) (nat_lit 0) A10K2.t4635 from rfl, allE_node, rows4634, irow4629, rows4635]
  all_goals rfl

theorem atot4629 : totK PA10K2 A10K2.u4629 = [0, 0, 612984138080, 2684001775878, 4085184349020, 2102443908994, 303927538966, 7151180950, 0, 0] := by
  rw [show A10K2.u4629 = KTree.node A10K2.t4634 (nat_lit 73250587) (nat_lit 6208686633) (nat_lit 0) A10K2.t4635 from rfl, totK_node, tot4634, tot4635]
  decide +kernel

theorem arows4631 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4631 = true := by
  rw [show A10K2.u4631 = KTree.node A10K2.t4636 (nat_lit 73262523) (nat_lit 7035925206) (nat_lit 0) A10K2.t4637 from rfl, allE_node, rows4636, irow4631, rows4637]
  all_goals rfl

theorem atot4631 : totK PA10K2 A10K2.u4631 = [0, 0, 931191100433, 3652520199844, 4064658007315, 1234489727096, 61220271750, 0, 0, 0] := by
  rw [show A10K2.u4631 = KTree.node A10K2.t4636 (nat_lit 73262523) (nat_lit 7035925206) (nat_lit 0) A10K2.t4637 from rfl, totK_node, tot4636, tot4637]
  decide +kernel

theorem arows4632 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4632 = true := by
  rw [show A10K2.u4632 = KTree.node A10K2.t4638 (nat_lit 73338480) (nat_lit 14750590265) (nat_lit 0) A10K2.t4639 from rfl, allE_node, rows4638, irow4632, rows4639]
  all_goals rfl

theorem atot4632 : totK PA10K2 A10K2.u4632 = [0, 592737332747, 2721838248518, 4132328208419, 2234559777804, 380267891195, 25960700956, 0, 0, 0] := by
  rw [show A10K2.u4632 = KTree.node A10K2.t4638 (nat_lit 73338480) (nat_lit 14750590265) (nat_lit 0) A10K2.t4639 from rfl, totK_node, tot4638, tot4639]
  decide +kernel

theorem arows4637 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4637 = true := by
  rw [show A10K2.u4637 = KTree.node A10K2.t4640 (nat_lit 73345827) (nat_lit 9877892970) (nat_lit 0) A10K2.t4641 from rfl, allE_node, rows4640, irow4637, rows4641]
  all_goals rfl

theorem atot4637 : totK PA10K2 A10K2.u4637 = [0, 783895901686, 3222148466451, 4134134284034, 1682373127148, 149678045403, 0, 0, 0, 0] := by
  rw [show A10K2.u4637 = KTree.node A10K2.t4640 (nat_lit 73345827) (nat_lit 9877892970) (nat_lit 0) A10K2.t4641 from rfl, totK_node, tot4640, tot4641]
  decide +kernel

theorem arows4638 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4638 = true := by
  rw [show A10K2.u4638 = KTree.node A10K2.t4642 (nat_lit 73359469) (nat_lit 4025492021) (nat_lit 0) A10K2.t4643 from rfl, allE_node, rows4642, irow4638, rows4643]
  all_goals rfl

theorem atot4638 : totK PA10K2 A10K2.u4638 = [0, 623275930811, 2566312937565, 3882019202674, 2366382466569, 426714889515, 12219140272, 0, 0, 0] := by
  rw [show A10K2.u4638 = KTree.node A10K2.t4642 (nat_lit 73359469) (nat_lit 4025492021) (nat_lit 0) A10K2.t4643 from rfl, totK_node, tot4642, tot4643]
  decide +kernel

theorem arows4640 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4640 = true := by
  rw [show A10K2.u4640 = KTree.node A10K2.t4644 (nat_lit 73364013) (nat_lit 2615459306) (nat_lit 0) A10K2.t4645 from rfl, allE_node, rows4644, irow4640, rows4645]
  all_goals rfl

theorem atot4640 : totK PA10K2 A10K2.u4640 = [0, 244073525254, 1960113093803, 4253221921446, 3052675099914, 528906421753, 13653259670, 0, 0, 0] := by
  rw [show A10K2.u4640 = KTree.node A10K2.t4644 (nat_lit 73364013) (nat_lit 2615459306) (nat_lit 0) A10K2.t4645 from rfl, totK_node, tot4644, tot4645]
  decide +kernel

theorem arows4641 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4641 = true := by
  rw [show A10K2.u4641 = KTree.node A10K2.t4646 (nat_lit 73370721) (nat_lit 9657420337) (nat_lit 0) A10K2.t4647 from rfl, allE_node, rows4646, irow4641, rows4647]
  all_goals rfl

theorem atot4641 : totK PA10K2 A10K2.u4641 = [0, 0, 590821798409, 2784358419710, 4247462893182, 2098078023517, 254243489683, 6318667960, 0, 0] := by
  rw [show A10K2.u4641 = KTree.node A10K2.t4646 (nat_lit 73370721) (nat_lit 9657420337) (nat_lit 0) A10K2.t4647 from rfl, totK_node, tot4646, tot4647]
  decide +kernel

theorem arows4644 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4644 = true := by
  rw [show A10K2.u4644 = KTree.node A10K2.t4648 (nat_lit 73377949) (nat_lit 5872359564) (nat_lit 0) A10K2.t4649 from rfl, allE_node, rows4648, irow4644, rows4649]
  all_goals rfl

theorem atot4644 : totK PA10K2 A10K2.u4644 = [0, 0, 780957663984, 3182193470221, 4132661507199, 1727502463298, 154508276184, 0, 0, 0] := by
  rw [show A10K2.u4644 = KTree.node A10K2.t4648 (nat_lit 73377949) (nat_lit 5872359564) (nat_lit 0) A10K2.t4649 from rfl, totK_node, tot4648, tot4649]
  decide +kernel

theorem arows4645 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4645 = true := by
  rw [show A10K2.u4645 = KTree.node A10K2.t4650 (nat_lit 73392525) (nat_lit 4122576226) (nat_lit 0) A10K2.t4651 from rfl, allE_node, rows4650, irow4645, rows4651]
  all_goals rfl

theorem atot4645 : totK PA10K2 A10K2.u4645 = [0, 0, 676344653540, 2936467685337, 4053672575868, 1901966771279, 236558521444, 6439430839, 0, 0] := by
  rw [show A10K2.u4645 = KTree.node A10K2.t4650 (nat_lit 73392525) (nat_lit 4122576226) (nat_lit 0) A10K2.t4651 from rfl, totK_node, tot4650, tot4651]
  decide +kernel

theorem arows4647 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4647 = true := by
  rw [show A10K2.u4647 = KTree.node A10K2.t4652 (nat_lit 73397127) (nat_lit 14425336065) (nat_lit 0) A10K2.t4653 from rfl, allE_node, rows4652, irow4647, rows4653]
  all_goals rfl

theorem atot4647 : totK PA10K2 A10K2.u4647 = [0, 0, 185950034399, 1713291019546, 4121555021509, 3164820677602, 616560395692, 17885676543, 0, 0] := by
  rw [show A10K2.u4647 = KTree.node A10K2.t4652 (nat_lit 73397127) (nat_lit 14425336065) (nat_lit 0) A10K2.t4653 from rfl, totK_node, tot4652, tot4653]
  decide +kernel

theorem arows4648 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4648 = true := by
  rw [show A10K2.u4648 = KTree.node A10K2.t4654 (nat_lit 74000571) (nat_lit 7164624692) (nat_lit 0) A10K2.t4655 from rfl, allE_node, rows4654, irow4648, rows4655]
  all_goals rfl

theorem atot4648 : totK PA10K2 A10K2.u4648 = [0, 871367436928, 3190651794265, 3480330146321, 1264285596399, 584018750367, 344628932980, 43132710386, 0, 0] := by
  rw [show A10K2.u4648 = KTree.node A10K2.t4654 (nat_lit 74000571) (nat_lit 7164624692) (nat_lit 0) A10K2.t4655 from rfl, totK_node, tot4654, tot4655]
  decide +kernel

theorem arows4652 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4652 = true := by
  rw [show A10K2.u4652 = KTree.node A10K2.t4656 (nat_lit 74005160) (nat_lit 6888168045) (nat_lit 0) A10K2.t4657 from rfl, allE_node, rows4656, irow4652, rows4657]
  all_goals rfl

theorem atot4652 : totK PA10K2 A10K2.u4652 = [0, 365166370945, 1963517950449, 3726192772124, 2804417454353, 615652147099, 31768748853, 0, 0, 0] := by
  rw [show A10K2.u4652 = KTree.node A10K2.t4656 (nat_lit 74005160) (nat_lit 6888168045) (nat_lit 0) A10K2.t4657 from rfl, totK_node, tot4656, tot4657]
  decide +kernel

theorem arows4653 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4653 = true := by
  rw [show A10K2.u4653 = KTree.node A10K2.t4658 (nat_lit 74010880) (nat_lit 11513996007) (nat_lit 0) A10K2.t4659 from rfl, allE_node, rows4658, irow4653, rows4659]
  all_goals rfl

theorem atot4653 : totK PA10K2 A10K2.u4653 = [0, 426704211574, 2372890914566, 4114453985539, 2118294892231, 261695862060, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u4653 = KTree.node A10K2.t4658 (nat_lit 74010880) (nat_lit 11513996007) (nat_lit 0) A10K2.t4659 from rfl, totK_node, tot4658, tot4659]
  decide +kernel

theorem arows4655 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4655 = true := by
  rw [show A10K2.u4655 = KTree.node A10K2.t4660 (nat_lit 74018029) (nat_lit 4784105087) (nat_lit 0) A10K2.t4661 from rfl, allE_node, rows4660, irow4655, rows4661]
  all_goals rfl

theorem atot4655 : totK PA10K2 A10K2.u4655 = [0, 676882298558, 3052508179046, 4175609724094, 1872701927640, 212409665077, 0, 0, 0, 0] := by
  rw [show A10K2.u4655 = KTree.node A10K2.t4660 (nat_lit 74018029) (nat_lit 4784105087) (nat_lit 0) A10K2.t4661 from rfl, totK_node, tot4660, tot4661]
  decide +kernel

theorem arows4656 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4656 = true := by
  rw [show A10K2.u4656 = KTree.node A10K2.t4662 (nat_lit 74032304) (nat_lit 9411121301) (nat_lit 0) A10K2.t4663 from rfl, allE_node, rows4662, irow4656, rows4663]
  all_goals rfl

theorem atot4656 : totK PA10K2 A10K2.u4656 = [0, 0, 881674981724, 3586802324685, 3974488473199, 1183650320767, 74019108011, 0, 0, 0] := by
  rw [show A10K2.u4656 = KTree.node A10K2.t4662 (nat_lit 74032304) (nat_lit 9411121301) (nat_lit 0) A10K2.t4663 from rfl, totK_node, tot4662, tot4663]
  decide +kernel

theorem arows4659 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4659 = true := by
  rw [show A10K2.u4659 = KTree.node A10K2.t4664 (nat_lit 74036671) (nat_lit 13812168227) (nat_lit 0) A10K2.t4665 from rfl, allE_node, rows4664, irow4659, rows4665]
  all_goals rfl

theorem atot4659 : totK PA10K2 A10K2.u4659 = [0, 0, 286959139418, 1939949317686, 3997035263090, 2704265140175, 553969696094, 31082886609, 0, 0] := by
  rw [show A10K2.u4659 = KTree.node A10K2.t4664 (nat_lit 74036671) (nat_lit 13812168227) (nat_lit 0) A10K2.t4665 from rfl, totK_node, tot4664, tot4665]
  decide +kernel

theorem arows4660 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4660 = true := by
  rw [show A10K2.u4660 = KTree.node A10K2.t4666 (nat_lit 74041376) (nat_lit 12323799992) (nat_lit 0) A10K2.t4667 from rfl, allE_node, rows4666, irow4660, rows4667]
  all_goals rfl

theorem atot4660 : totK PA10K2 A10K2.u4660 = [0, 0, 724716917172, 3100764880125, 4000988479542, 1423035077616, 107506101055, 0, 0, 0] := by
  rw [show A10K2.u4660 = KTree.node A10K2.t4666 (nat_lit 74041376) (nat_lit 12323799992) (nat_lit 0) A10K2.t4667 from rfl, totK_node, tot4666, tot4667]
  decide +kernel

theorem arows4662 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4662 = true := by
  rw [show A10K2.u4662 = KTree.node A10K2.t4668 (nat_lit 74048910) (nat_lit 14981585276) (nat_lit 0) A10K2.t4669 from rfl, allE_node, rows4668, irow4662, rows4669]
  all_goals rfl

theorem atot4662 : totK PA10K2 A10K2.u4662 = [0, 0, 741189484195, 2989868981363, 3944756671849, 1673369790601, 200428504197, 6121173289, 0, 0] := by
  rw [show A10K2.u4662 = KTree.node A10K2.t4668 (nat_lit 74048910) (nat_lit 14981585276) (nat_lit 0) A10K2.t4669 from rfl, totK_node, tot4668, tot4669]
  decide +kernel

theorem arows4663 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4663 = true := by
  rw [show A10K2.u4663 = KTree.node A10K2.t4670 (nat_lit 74059838) (nat_lit 11681164697) (nat_lit 0) A10K2.t4671 from rfl, allE_node, rows4670, irow4663, rows4671]
  all_goals rfl

theorem atot4663 : totK PA10K2 A10K2.u4663 = [0, 777954947991, 3031212544365, 3717189462834, 1623418685656, 364748578415, 40377713189, 0, 0, 0] := by
  rw [show A10K2.u4663 = KTree.node A10K2.t4670 (nat_lit 74059838) (nat_lit 11681164697) (nat_lit 0) A10K2.t4671 from rfl, totK_node, tot4670, tot4671]
  decide +kernel

theorem arows4669 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4669 = true := by
  rw [show A10K2.u4669 = KTree.node A10K2.t4672 (nat_lit 74067441) (nat_lit 7112293509) (nat_lit 0) A10K2.t4673 from rfl, allE_node, rows4672, irow4669, rows4673]
  all_goals rfl

theorem atot4669 : totK PA10K2 A10K2.u4669 = [0, 489539926130, 2522159319980, 4066343279874, 2242433202591, 427527392002, 25734533292, 0, 0, 0] := by
  rw [show A10K2.u4669 = KTree.node A10K2.t4672 (nat_lit 74067441) (nat_lit 7112293509) (nat_lit 0) A10K2.t4673 from rfl, totK_node, tot4672, tot4673]
  decide +kernel

theorem arows4670 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4670 = true := by
  rw [show A10K2.u4670 = KTree.node A10K2.t4674 (nat_lit 74072861) (nat_lit 6017451388) (nat_lit 0) A10K2.t4675 from rfl, allE_node, rows4674, irow4670, rows4675]
  all_goals rfl

theorem atot4670 : totK PA10K2 A10K2.u4670 = [0, 789072095305, 2916853178651, 3627210366437, 1867338444146, 276980652401, 6034215561, 0, 0, 0] := by
  rw [show A10K2.u4670 = KTree.node A10K2.t4674 (nat_lit 74072861) (nat_lit 6017451388) (nat_lit 0) A10K2.t4675 from rfl, totK_node, tot4674, tot4675]
  decide +kernel

theorem arows4672 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4672 = true := by
  rw [show A10K2.u4672 = KTree.node A10K2.t4676 (nat_lit 74078472) (nat_lit 13021666916) (nat_lit 0) A10K2.t4677 from rfl, allE_node, rows4676, irow4672, rows4677]
  all_goals rfl

theorem atot4672 : totK PA10K2 A10K2.u4672 = [0, 0, 1509644274148, 4359381906401, 2947647974223, 473089310265, 11740475125, 0, 0, 0] := by
  rw [show A10K2.u4672 = KTree.node A10K2.t4676 (nat_lit 74078472) (nat_lit 13021666916) (nat_lit 0) A10K2.t4677 from rfl, totK_node, tot4676, tot4677]
  decide +kernel

theorem arows4673 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4673 = true := by
  rw [show A10K2.u4673 = KTree.node A10K2.t4678 (nat_lit 74098925) (nat_lit 5971045383) (nat_lit 0) A10K2.t4679 from rfl, allE_node, rows4678, irow4673, rows4679]
  all_goals rfl

theorem atot4673 : totK PA10K2 A10K2.u4673 = [0, 0, 1007556199646, 3722581624597, 3892317875089, 983061648280, 45698881016, 0, 0, 0] := by
  rw [show A10K2.u4673 = KTree.node A10K2.t4678 (nat_lit 74098925) (nat_lit 5971045383) (nat_lit 0) A10K2.t4679 from rfl, totK_node, tot4678, tot4679]
  decide +kernel

theorem arows4676 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4676 = true := by
  rw [show A10K2.u4676 = KTree.node A10K2.t4680 (nat_lit 74107180) (nat_lit 13552313479) (nat_lit 0) A10K2.t4681 from rfl, allE_node, rows4680, irow4676, rows4681]
  all_goals rfl

theorem atot4676 : totK PA10K2 A10K2.u4676 = [0, 0, 574736170080, 2990930713879, 4195023660188, 1395158036598, 100964071084, 0, 0, 0] := by
  rw [show A10K2.u4676 = KTree.node A10K2.t4680 (nat_lit 74107180) (nat_lit 13552313479) (nat_lit 0) A10K2.t4681 from rfl, totK_node, tot4680, tot4681]
  decide +kernel

theorem arows4677 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4677 = true := by
  rw [show A10K2.u4677 = KTree.node A10K2.t4682 (nat_lit 74128560) (nat_lit 11746170455) (nat_lit 0) A10K2.t4683 from rfl, allE_node, rows4682, irow4677, rows4683]
  all_goals rfl

theorem atot4677 : totK PA10K2 A10K2.u4677 = [0, 794672530841, 2921855871132, 3507156368949, 1898301714762, 712021907050, 144586921448, 6354482628, 0, 0] := by
  rw [show A10K2.u4677 = KTree.node A10K2.t4682 (nat_lit 74128560) (nat_lit 11746170455) (nat_lit 0) A10K2.t4683 from rfl, totK_node, tot4682, tot4683]
  decide +kernel

theorem arows4679 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4679 = true := by
  rw [show A10K2.u4679 = KTree.node A10K2.t4684 (nat_lit 74134805) (nat_lit 6819334536) (nat_lit 0) A10K2.t4685 from rfl, allE_node, rows4684, irow4679, rows4685]
  all_goals rfl

theorem atot4679 : totK PA10K2 A10K2.u4679 = [0, 297267720674, 2062056370578, 4081965264282, 2757627193505, 576333645948, 31747192500, 0, 0, 0] := by
  rw [show A10K2.u4679 = KTree.node A10K2.t4684 (nat_lit 74134805) (nat_lit 6819334536) (nat_lit 0) A10K2.t4685 from rfl, totK_node, tot4684, tot4685]
  decide +kernel

theorem arows4680 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4680 = true := by
  rw [show A10K2.u4680 = KTree.node A10K2.t4686 (nat_lit 74147667) (nat_lit 10298754506) (nat_lit 0) A10K2.t4687 from rfl, allE_node, rows4686, irow4680, rows4687]
  all_goals rfl

theorem atot4680 : totK PA10K2 A10K2.u4680 = [0, 799422805651, 3253053534775, 4218433805061, 1751200051133, 158281599664, 0, 0, 0, 0] := by
  rw [show A10K2.u4680 = KTree.node A10K2.t4686 (nat_lit 74147667) (nat_lit 10298754506) (nat_lit 0) A10K2.t4687 from rfl, totK_node, tot4686, tot4687]
  decide +kernel

theorem arows4684 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4684 = true := by
  rw [show A10K2.u4684 = KTree.node A10K2.t4688 (nat_lit 74153438) (nat_lit 15093312645) (nat_lit 0) A10K2.t4689 from rfl, allE_node, rows4688, irow4684, rows4689]
  all_goals rfl

theorem atot4684 : totK PA10K2 A10K2.u4684 = [0, 0, 885332055791, 3491516050292, 4122840556405, 1485597902290, 113014806151, 0, 0, 0] := by
  rw [show A10K2.u4684 = KTree.node A10K2.t4688 (nat_lit 74153438) (nat_lit 15093312645) (nat_lit 0) A10K2.t4689 from rfl, totK_node, tot4688, tot4689]
  decide +kernel

theorem arows4685 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4685 = true := by
  rw [show A10K2.u4685 = KTree.node A10K2.t4690 (nat_lit 74164460) (nat_lit 11708221741) (nat_lit 0) A10K2.t4691 from rfl, allE_node, rows4690, irow4685, rows4691]
  all_goals rfl

theorem atot4685 : totK PA10K2 A10K2.u4685 = [0, 0, 811249549804, 3309632109510, 4091081660904, 1571158089181, 125165231140, 0, 0, 0] := by
  rw [show A10K2.u4685 = KTree.node A10K2.t4690 (nat_lit 74164460) (nat_lit 11708221741) (nat_lit 0) A10K2.t4691 from rfl, totK_node, tot4690, tot4691]
  decide +kernel

theorem arows4687 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4687 = true := by
  rw [show A10K2.u4687 = KTree.node A10K2.t4692 (nat_lit 74178614) (nat_lit 16097883093) (nat_lit 0) A10K2.t4693 from rfl, allE_node, rows4692, irow4687, rows4693]
  all_goals rfl

theorem atot4687 : totK PA10K2 A10K2.u4687 = [0, 0, 611492816791, 2745459052604, 4123300659443, 2198068291142, 293645902773, 7047025452, 0, 0] := by
  rw [show A10K2.u4687 = KTree.node A10K2.t4692 (nat_lit 74178614) (nat_lit 16097883093) (nat_lit 0) A10K2.t4693 from rfl, totK_node, tot4692, tot4693]
  decide +kernel

theorem arows4688 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4688 = true := by
  rw [show A10K2.u4688 = KTree.node A10K2.t4694 (nat_lit 74183921) (nat_lit 5225980963) (nat_lit 0) A10K2.t4695 from rfl, allE_node, rows4694, irow4688, rows4695]
  all_goals rfl

theorem atot4688 : totK PA10K2 A10K2.u4688 = [0, 0, 187219251666, 1669669552210, 4061224935307, 3322264992213, 679182567416, 11979448558, 0, 0] := by
  rw [show A10K2.u4688 = KTree.node A10K2.t4694 (nat_lit 74183921) (nat_lit 5225980963) (nat_lit 0) A10K2.t4695 from rfl, totK_node, tot4694, tot4695]
  decide +kernel

theorem arows4691 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4691 = true := by
  rw [show A10K2.u4691 = KTree.node A10K2.t4696 (nat_lit 74263072) (nat_lit 9624174109) (nat_lit 0) A10K2.t4697 from rfl, allE_node, rows4696, irow4691, rows4697]
  all_goals rfl

theorem atot4691 : totK PA10K2 A10K2.u4691 = [0, 0, 866406072129, 3371159666030, 3919631876855, 1361198309117, 210849670455, 29150846468, 0, 0] := by
  rw [show A10K2.u4691 = KTree.node A10K2.t4696 (nat_lit 74263072) (nat_lit 9624174109) (nat_lit 0) A10K2.t4697 from rfl, totK_node, tot4696, tot4697]
  decide +kernel

theorem arows4692 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4692 = true := by
  rw [show A10K2.u4692 = KTree.node A10K2.t4698 (nat_lit 74267810) (nat_lit 14335448007) (nat_lit 0) A10K2.t4699 from rfl, allE_node, rows4698, irow4692, rows4699]
  all_goals rfl

theorem atot4692 : totK PA10K2 A10K2.u4692 = [0, 0, 444976671088, 2146965941290, 3667956620314, 2595289480694, 580497295312, 31768748853, 0, 0] := by
  rw [show A10K2.u4692 = KTree.node A10K2.t4698 (nat_lit 74267810) (nat_lit 14335448007) (nat_lit 0) A10K2.t4699 from rfl, totK_node, tot4698, tot4699]
  decide +kernel

theorem arows4694 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4694 = true := by
  rw [show A10K2.u4694 = KTree.node A10K2.t4700 (nat_lit 74274080) (nat_lit 9992429299) (nat_lit 0) A10K2.t4701 from rfl, allE_node, rows4700, irow4694, rows4701]
  all_goals rfl

theorem atot4694 : totK PA10K2 A10K2.u4694 = [0, 0, 534398744578, 2593004865826, 4037073626213, 1869295247447, 226584541499, 6239673734, 0, 0] := by
  rw [show A10K2.u4694 = KTree.node A10K2.t4700 (nat_lit 74274080) (nat_lit 9992429299) (nat_lit 0) A10K2.t4701 from rfl, totK_node, tot4700, tot4701]
  decide +kernel

theorem arows4695 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4695 = true := by
  rw [show A10K2.u4695 = KTree.node A10K2.t4702 (nat_lit 74280674) (nat_lit 13125878397) (nat_lit 0) A10K2.t4703 from rfl, allE_node, rows4702, irow4695, rows4703]
  all_goals rfl

theorem atot4695 : totK PA10K2 A10K2.u4695 = [0, 0, 486262743125, 2558111196274, 4236336578701, 2338291391362, 336617369081, 6962742351, 0, 0] := by
  rw [show A10K2.u4695 = KTree.node A10K2.t4702 (nat_lit 74280674) (nat_lit 13125878397) (nat_lit 0) A10K2.t4703 from rfl, totK_node, tot4702, tot4703]
  decide +kernel

theorem arows4700 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4700 = true := by
  rw [show A10K2.u4700 = KTree.node A10K2.t4704 (nat_lit 74295197) (nat_lit 5046377985) (nat_lit 0) A10K2.t4705 from rfl, allE_node, rows4704, irow4700, rows4705]
  all_goals rfl

theorem atot4700 : totK PA10K2 A10K2.u4700 = [0, 0, 0, 971927109484, 3639199962029, 3856472346335, 1083519258415, 68021021530, 0, 0] := by
  rw [show A10K2.u4700 = KTree.node A10K2.t4704 (nat_lit 74295197) (nat_lit 5046377985) (nat_lit 0) A10K2.t4705 from rfl, totK_node, tot4704, tot4705]
  decide +kernel

theorem arows4701 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4701 = true := by
  rw [show A10K2.u4701 = KTree.node A10K2.t4706 (nat_lit 74299949) (nat_lit 5294512823) (nat_lit 0) A10K2.t4707 from rfl, allE_node, rows4706, irow4701, rows4707]
  all_goals rfl

theorem atot4701 : totK PA10K2 A10K2.u4701 = [0, 0, 0, 440341764664, 2119926628372, 3629543176668, 2466799264805, 551680168681, 31018567651, 0] := by
  rw [show A10K2.u4701 = KTree.node A10K2.t4706 (nat_lit 74299949) (nat_lit 5294512823) (nat_lit 0) A10K2.t4707 from rfl, totK_node, tot4706, tot4707]
  decide +kernel

theorem arows4703 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4703 = true := by
  rw [show A10K2.u4703 = KTree.node A10K2.t4708 (nat_lit 74306721) (nat_lit 5841381104) (nat_lit 0) A10K2.t4709 from rfl, allE_node, rows4708, irow4703, rows4709]
  all_goals rfl

theorem atot4703 : totK PA10K2 A10K2.u4703 = [0, 0, 0, 532791286167, 2612124366645, 3936605996158, 1794143333311, 223954464666, 5685526223, 0] := by
  rw [show A10K2.u4703 = KTree.node A10K2.t4708 (nat_lit 74306721) (nat_lit 5841381104) (nat_lit 0) A10K2.t4709 from rfl, totK_node, tot4708, tot4709]
  decide +kernel

theorem arows4704 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4704 = true := by
  rw [show A10K2.u4704 = KTree.node A10K2.t4710 (nat_lit 74313715) (nat_lit 8243696247) (nat_lit 0) A10K2.t4711 from rfl, allE_node, rows4710, irow4704, rows4711]
  all_goals rfl

theorem atot4704 : totK PA10K2 A10K2.u4704 = [0, 0, 468537272203, 2275764306661, 3789662183111, 2525030217247, 597167500296, 44919408541, 0, 0] := by
  rw [show A10K2.u4704 = KTree.node A10K2.t4710 (nat_lit 74313715) (nat_lit 8243696247) (nat_lit 0) A10K2.t4711 from rfl, totK_node, tot4710, tot4711]
  decide +kernel

theorem arows4707 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4707 = true := by
  rw [show A10K2.u4707 = KTree.node A10K2.t4712 (nat_lit 74327777) (nat_lit 3878696756) (nat_lit 0) A10K2.t4713 from rfl, allE_node, rows4712, irow4707, rows4713]
  all_goals rfl

theorem atot4707 : totK PA10K2 A10K2.u4707 = [0, 0, 795831278858, 3142005099335, 3931562321151, 1521327446870, 153340336549, 5460492893, 0, 0] := by
  rw [show A10K2.u4707 = KTree.node A10K2.t4712 (nat_lit 74327777) (nat_lit 3878696756) (nat_lit 0) A10K2.t4713 from rfl, totK_node, tot4712, tot4713]
  decide +kernel

theorem arows4708 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4708 = true := by
  rw [show A10K2.u4708 = KTree.node A10K2.t4714 (nat_lit 74332456) (nat_lit 11138555531) (nat_lit 0) A10K2.t4715 from rfl, allE_node, rows4714, irow4708, rows4715]
  all_goals rfl

theorem atot4708 : totK PA10K2 A10K2.u4708 = [0, 0, 321041346309, 1807913433366, 3839521734858, 2853129566407, 605300862765, 31768748853, 0, 0] := by
  rw [show A10K2.u4708 = KTree.node A10K2.t4714 (nat_lit 74332456) (nat_lit 11138555531) (nat_lit 0) A10K2.t4715 from rfl, totK_node, tot4714, tot4715]
  decide +kernel

theorem arows4710 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4710 = true := by
  rw [show A10K2.u4710 = KTree.node A10K2.t4716 (nat_lit 74337044) (nat_lit 13293080596) (nat_lit 0) A10K2.t4717 from rfl, allE_node, rows4716, irow4710, rows4717]
  all_goals rfl

theorem atot4710 : totK PA10K2 A10K2.u4710 = [0, 0, 467092711113, 2712178156198, 4272145273049, 1778011894424, 128321079507, 0, 0, 0] := by
  rw [show A10K2.u4710 = KTree.node A10K2.t4716 (nat_lit 74337044) (nat_lit 13293080596) (nat_lit 0) A10K2.t4717 from rfl, totK_node, tot4716, tot4717]
  decide +kernel

theorem arows4711 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4711 = true := by
  rw [show A10K2.u4711 = KTree.node A10K2.t4718 (nat_lit 74360065) (nat_lit 6661038492) (nat_lit 0) A10K2.t4719 from rfl, allE_node, rows4718, irow4711, rows4719]
  all_goals rfl

theorem atot4711 : totK PA10K2 A10K2.u4711 = [0, 0, 0, 1043018618108, 3772012078618, 3651943378755, 826336352513, 38593611784, 0, 0] := by
  rw [show A10K2.u4711 = KTree.node A10K2.t4718 (nat_lit 74360065) (nat_lit 6661038492) (nat_lit 0) A10K2.t4719 from rfl, totK_node, tot4718, tot4719]
  decide +kernel

theorem arows4715 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4715 = true := by
  rw [show A10K2.u4715 = KTree.node A10K2.t4720 (nat_lit 74368411) (nat_lit 9832932674) (nat_lit 0) A10K2.t4721 from rfl, allE_node, rows4720, irow4715, rows4721]
  all_goals rfl

theorem atot4715 : totK PA10K2 A10K2.u4715 = [0, 0, 0, 996660963934, 3749884423119, 3759547284575, 890182423658, 50422943179, 0, 0] := by
  rw [show A10K2.u4715 = KTree.node A10K2.t4720 (nat_lit 74368411) (nat_lit 9832932674) (nat_lit 0) A10K2.t4721 from rfl, totK_node, tot4720, tot4721]
  decide +kernel

theorem arows4716 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4716 = true := by
  rw [show A10K2.u4716 = KTree.node A10K2.t4722 (nat_lit 74386837) (nat_lit 1694174419) (nat_lit 0) A10K2.t4723 from rfl, allE_node, rows4722, irow4716, rows4723]
  all_goals rfl

theorem atot4716 : totK PA10K2 A10K2.u4716 = [0, 0, 590805433127, 2128670060125, 2939228337797, 2569938614983, 1198760169261, 187919439061, 5982052406, 0] := by
  rw [show A10K2.u4716 = KTree.node A10K2.t4722 (nat_lit 74386837) (nat_lit 1694174419) (nat_lit 0) A10K2.t4723 from rfl, totK_node, tot4722, tot4723]
  decide +kernel

theorem arows4718 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4718 = true := by
  rw [show A10K2.u4718 = KTree.node A10K2.t4724 (nat_lit 74395588) (nat_lit 2971632101) (nat_lit 0) A10K2.t4725 from rfl, allE_node, rows4724, irow4718, rows4725]
  all_goals rfl

theorem atot4718 : totK PA10K2 A10K2.u4718 = [0, 0, 498031759301, 2550896266839, 4094967158307, 2232744987837, 415073742480, 25660650750, 0, 0] := by
  rw [show A10K2.u4718 = KTree.node A10K2.t4724 (nat_lit 74395588) (nat_lit 2971632101) (nat_lit 0) A10K2.t4725 from rfl, totK_node, tot4724, tot4725]
  decide +kernel

theorem arows4719 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4719 = true := by
  rw [show A10K2.u4719 = KTree.node A10K2.t4726 (nat_lit 74409757) (nat_lit 5708356387) (nat_lit 0) A10K2.t4727 from rfl, allE_node, rows4726, irow4719, rows4727]
  all_goals rfl

theorem atot4719 : totK PA10K2 A10K2.u4719 = [0, 0, 798499989054, 3289144641496, 4204850233961, 1724690344690, 173165888604, 0, 0, 0] := by
  rw [show A10K2.u4719 = KTree.node A10K2.t4726 (nat_lit 74409757) (nat_lit 5708356387) (nat_lit 0) A10K2.t4727 from rfl, totK_node, tot4726, tot4727]
  decide +kernel

theorem arows4722 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4722 = true := by
  rw [show A10K2.u4722 = KTree.node A10K2.t4728 (nat_lit 74416020) (nat_lit 6338674110) (nat_lit 0) A10K2.t4729 from rfl, allE_node, rows4728, irow4722, rows4729]
  all_goals rfl

theorem atot4722 : totK PA10K2 A10K2.u4722 = [0, 571579400012, 1797635149501, 2126340211059, 2517552214932, 2199282199162, 614920932579, 41590655314, 0, 0] := by
  rw [show A10K2.u4722 = KTree.node A10K2.t4728 (nat_lit 74416020) (nat_lit 6338674110) (nat_lit 0) A10K2.t4729 from rfl, totK_node, tot4728, tot4729]
  decide +kernel

theorem arows4723 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4723 = true := by
  rw [show A10K2.u4723 = KTree.node A10K2.t4730 (nat_lit 74453549) (nat_lit 5469799525) (nat_lit 0) A10K2.t4731 from rfl, allE_node, rows4730, irow4723, rows4731]
  all_goals rfl

theorem atot4723 : totK PA10K2 A10K2.u4723 = [0, 299011857882, 1951250952100, 4025513723473, 2813882512036, 571431068006, 30831673886, 0, 0, 0] := by
  rw [show A10K2.u4723 = KTree.node A10K2.t4730 (nat_lit 74453549) (nat_lit 5469799525) (nat_lit 0) A10K2.t4731 from rfl, totK_node, tot4730, tot4731]
  decide +kernel

theorem arows4725 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4725 = true := by
  rw [show A10K2.u4725 = KTree.node A10K2.t4732 (nat_lit 74467424) (nat_lit 13543058683) (nat_lit 0) A10K2.t4733 from rfl, allE_node, rows4732, irow4725, rows4733]
  all_goals rfl

theorem atot4725 : totK PA10K2 A10K2.u4725 = [0, 668069535895, 3123748263597, 4205520221108, 1572476394549, 118703503788, 0, 0, 0, 0] := by
  rw [show A10K2.u4725 = KTree.node A10K2.t4732 (nat_lit 74467424) (nat_lit 13543058683) (nat_lit 0) A10K2.t4733 from rfl, totK_node, tot4732, tot4733]
  decide +kernel

theorem arows4726 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4726 = true := by
  rw [show A10K2.u4726 = KTree.node A10K2.t4734 (nat_lit 74482444) (nat_lit 11756669132) (nat_lit 0) A10K2.t4735 from rfl, allE_node, rows4734, irow4726, rows4735]
  all_goals rfl

theorem atot4726 : totK PA10K2 A10K2.u4726 = [0, 0, 1054575114725, 3807840689649, 3759824353255, 934084941130, 44372202425, 0, 0, 0] := by
  rw [show A10K2.u4726 = KTree.node A10K2.t4734 (nat_lit 74482444) (nat_lit 11756669132) (nat_lit 0) A10K2.t4735 from rfl, totK_node, tot4734, tot4735]
  decide +kernel

theorem arows4733 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4733 = true := by
  rw [show A10K2.u4733 = KTree.node A10K2.t4736 (nat_lit 74500194) (nat_lit 8869746447) (nat_lit 0) A10K2.t4737 from rfl, allE_node, rows4736, irow4733, rows4737]
  all_goals rfl

theorem atot4733 : totK PA10K2 A10K2.u4733 = [0, 0, 733401951610, 3347703131854, 4106085687451, 1245558610360, 89300328360, 0, 0, 0] := by
  rw [show A10K2.u4733 = KTree.node A10K2.t4736 (nat_lit 74500194) (nat_lit 8869746447) (nat_lit 0) A10K2.t4737 from rfl, totK_node, tot4736, tot4737]
  decide +kernel

theorem arows4734 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4734 = true := by
  rw [show A10K2.u4734 = KTree.node A10K2.t4738 (nat_lit 74524592) (nat_lit 10389994271) (nat_lit 0) A10K2.t4739 from rfl, allE_node, rows4738, irow4734, rows4739]
  all_goals rfl

theorem atot4734 : totK PA10K2 A10K2.u4734 = [0, 836243354860, 3000348951211, 3263542759481, 1596248300131, 687997464088, 133756988527, 5546304973, 0, 0] := by
  rw [show A10K2.u4734 = KTree.node A10K2.t4738 (nat_lit 74524592) (nat_lit 10389994271) (nat_lit 0) A10K2.t4739 from rfl, totK_node, tot4738, tot4739]
  decide +kernel

theorem arows4736 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4736 = true := by
  rw [show A10K2.u4736 = KTree.node A10K2.t4740 (nat_lit 74529110) (nat_lit 10018042833) (nat_lit 0) A10K2.t4741 from rfl, allE_node, rows4740, irow4736, rows4741]
  all_goals rfl

theorem atot4736 : totK PA10K2 A10K2.u4736 = [0, 299996936876, 1766687482917, 3808284456640, 2995377964135, 637629282636, 31768748853, 0, 0, 0] := by
  rw [show A10K2.u4736 = KTree.node A10K2.t4740 (nat_lit 74529110) (nat_lit 10018042833) (nat_lit 0) A10K2.t4741 from rfl, totK_node, tot4740, tot4741]
  decide +kernel

theorem arows4737 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4737 = true := by
  rw [show A10K2.u4737 = KTree.node A10K2.t4742 (nat_lit 74533658) (nat_lit 12655625857) (nat_lit 0) A10K2.t4743 from rfl, allE_node, rows4742, irow4737, rows4743]
  all_goals rfl

theorem atot4737 : totK PA10K2 A10K2.u4737 = [0, 470692171148, 2676244543029, 4297626634229, 1930642091538, 174947059283, 0, 0, 0, 0] := by
  rw [show A10K2.u4737 = KTree.node A10K2.t4742 (nat_lit 74533658) (nat_lit 12655625857) (nat_lit 0) A10K2.t4743 from rfl, totK_node, tot4742, tot4743]
  decide +kernel

theorem arows4740 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4740 = true := by
  rw [show A10K2.u4740 = KTree.node A10K2.t4744 (nat_lit 74542582) (nat_lit 16892777961) (nat_lit 0) A10K2.t4745 from rfl, allE_node, rows4744, irow4740, rows4745]
  all_goals rfl

theorem atot4740 : totK PA10K2 A10K2.u4740 = [0, 554803763168, 2510854191421, 3954586979941, 2424239436297, 439701648986, 13317224979, 0, 0, 0] := by
  rw [show A10K2.u4740 = KTree.node A10K2.t4744 (nat_lit 74542582) (nat_lit 16892777961) (nat_lit 0) A10K2.t4745 from rfl, totK_node, tot4744, tot4745]
  decide +kernel

theorem arows4741 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4741 = true := by
  rw [show A10K2.u4741 = KTree.node A10K2.t4746 (nat_lit 74557339) (nat_lit 9807141556) (nat_lit 0) A10K2.t4747 from rfl, allE_node, rows4746, irow4741, rows4747]
  all_goals rfl

theorem atot4741 : totK PA10K2 A10K2.u4741 = [0, 0, 916405558426, 3504625774657, 3944938281266, 1226232493797, 74012375501, 0, 0, 0] := by
  rw [show A10K2.u4741 = KTree.node A10K2.t4746 (nat_lit 74557339) (nat_lit 9807141556) (nat_lit 0) A10K2.t4747 from rfl, totK_node, tot4746, tot4747]
  decide +kernel

theorem arows4743 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4743 = true := by
  rw [show A10K2.u4743 = KTree.node A10K2.t4748 (nat_lit 74562081) (nat_lit 7443692976) (nat_lit 0) A10K2.t4749 from rfl, allE_node, rows4748, irow4743, rows4749]
  all_goals rfl

theorem atot4743 : totK PA10K2 A10K2.u4743 = [0, 0, 400871179982, 2076426960445, 3782234786653, 2603667620853, 565174223828, 31082886609, 0, 0] := by
  rw [show A10K2.u4743 = KTree.node A10K2.t4748 (nat_lit 74562081) (nat_lit 7443692976) (nat_lit 0) A10K2.t4749 from rfl, totK_node, tot4748, tot4749]
  decide +kernel

theorem arows4744 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4744 = true := by
  rw [show A10K2.u4744 = KTree.node A10K2.t4750 (nat_lit 74567776) (nat_lit 12235671676) (nat_lit 0) A10K2.t4751 from rfl, allE_node, rows4750, irow4744, rows4751]
  all_goals rfl

theorem atot4744 : totK PA10K2 A10K2.u4744 = [0, 0, 442075663827, 2443092792113, 4181846294267, 2035705198703, 245885793701, 6121173289, 0, 0] := by
  rw [show A10K2.u4744 = KTree.node A10K2.t4750 (nat_lit 74567776) (nat_lit 12235671676) (nat_lit 0) A10K2.t4751 from rfl, totK_node, tot4750, tot4751]
  decide +kernel

theorem arows4748 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4748 = true := by
  rw [show A10K2.u4748 = KTree.node A10K2.t4752 (nat_lit 74575752) (nat_lit 10937060849) (nat_lit 0) A10K2.t4753 from rfl, allE_node, rows4752, irow4748, rows4753]
  all_goals rfl

theorem atot4748 : totK PA10K2 A10K2.u4748 = [0, 557742759892, 2224825392544, 3422397962786, 2682595801486, 850966677907, 61620499419, 0, 0, 0] := by
  rw [show A10K2.u4748 = KTree.node A10K2.t4752 (nat_lit 74575752) (nat_lit 10937060849) (nat_lit 0) A10K2.t4753 from rfl, totK_node, tot4752, tot4753]
  decide +kernel

theorem arows4749 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4749 = true := by
  rw [show A10K2.u4749 = KTree.node A10K2.t4754 (nat_lit 74586156) (nat_lit 13025083326) (nat_lit 0) A10K2.t4755 from rfl, allE_node, rows4754, irow4749, rows4755]
  all_goals rfl

theorem atot4749 : totK PA10K2 A10K2.u4749 = [0, 393585523161, 2183963324430, 3978192939128, 2476752832131, 478194061095, 30402056026, 0, 0, 0] := by
  rw [show A10K2.u4749 = KTree.node A10K2.t4754 (nat_lit 74586156) (nat_lit 13025083326) (nat_lit 0) A10K2.t4755 from rfl, totK_node, tot4754, tot4755]
  decide +kernel

theorem arows4751 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4751 = true := by
  rw [show A10K2.u4751 = KTree.node A10K2.t4756 (nat_lit 74591970) (nat_lit 13375564878) (nat_lit 0) A10K2.t4757 from rfl, allE_node, rows4756, irow4751, rows4757]
  all_goals rfl

theorem atot4751 : totK PA10K2 A10K2.u4751 = [0, 465631835236, 2462348144388, 4037692164632, 2238632776199, 425656124273, 25734533292, 0, 0, 0] := by
  rw [show A10K2.u4751 = KTree.node A10K2.t4756 (nat_lit 74591970) (nat_lit 13375564878) (nat_lit 0) A10K2.t4757 from rfl, totK_node, tot4756, tot4757]
  decide +kernel

theorem arows4752 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4752 = true := by
  rw [show A10K2.u4752 = KTree.node A10K2.t4758 (nat_lit 74597531) (nat_lit 10063092638) (nat_lit 0) A10K2.t4759 from rfl, allE_node, rows4758, irow4752, rows4759]
  all_goals rfl

theorem atot4752 : totK PA10K2 A10K2.u4752 = [0, 837613071177, 3091349460981, 3650390017015, 1704084641114, 250658867991, 6034215561, 0, 0, 0] := by
  rw [show A10K2.u4752 = KTree.node A10K2.t4758 (nat_lit 74597531) (nat_lit 10063092638) (nat_lit 0) A10K2.t4759 from rfl, totK_node, tot4758, tot4759]
  decide +kernel

theorem arows4755 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4755 = true := by
  rw [show A10K2.u4755 = KTree.node A10K2.t4760 (nat_lit 74602789) (nat_lit 7509440298) (nat_lit 0) A10K2.t4761 from rfl, allE_node, rows4760, irow4755, rows4761]
  all_goals rfl

theorem atot4755 : totK PA10K2 A10K2.u4755 = [0, 0, 1414855175371, 4223536087364, 3155454269485, 594716166312, 31558137809, 0, 0, 0] := by
  rw [show A10K2.u4755 = KTree.node A10K2.t4760 (nat_lit 74602789) (nat_lit 7509440298) (nat_lit 0) A10K2.t4761 from rfl, totK_node, tot4760, tot4761]
  decide +kernel

theorem arows4756 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4756 = true := by
  rw [show A10K2.u4756 = KTree.node A10K2.t4762 (nat_lit 74622742) (nat_lit 11063181166) (nat_lit 0) A10K2.t4763 from rfl, allE_node, rows4762, irow4756, rows4763]
  all_goals rfl

theorem atot4756 : totK PA10K2 A10K2.u4756 = [0, 0, 964776073439, 3699965950767, 3936712244834, 1013493592521, 45698881016, 0, 0, 0] := by
  rw [show A10K2.u4756 = KTree.node A10K2.t4762 (nat_lit 74622742) (nat_lit 11063181166) (nat_lit 0) A10K2.t4763 from rfl, totK_node, tot4762, tot4763]
  decide +kernel

theorem arows4758 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4758 = true := by
  rw [show A10K2.u4758 = KTree.node A10K2.t4764 (nat_lit 74630938) (nat_lit 13823193451) (nat_lit 0) A10K2.t4765 from rfl, allE_node, rows4764, irow4758, rows4765]
  all_goals rfl

theorem atot4758 : totK PA10K2 A10K2.u4758 = [0, 0, 832156739090, 3384088904944, 3904170910876, 1135181685692, 82512268637, 0, 0, 0] := by
  rw [show A10K2.u4758 = KTree.node A10K2.t4764 (nat_lit 74630938) (nat_lit 13823193451) (nat_lit 0) A10K2.t4765 from rfl, totK_node, tot4764, tot4765]
  decide +kernel

theorem arows4759 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4759 = true := by
  rw [show A10K2.u4759 = KTree.node A10K2.t4766 (nat_lit 74711474) (nat_lit 6739631973) (nat_lit 0) A10K2.t4767 from rfl, allE_node, rows4766, irow4759, rows4767]
  all_goals rfl

theorem atot4759 : totK PA10K2 A10K2.u4759 = [0, 0, 759359939940, 2923566819759, 3808494687024, 1701237467879, 265190992281, 6354482628, 0, 0] := by
  rw [show A10K2.u4759 = KTree.node A10K2.t4766 (nat_lit 74711474) (nat_lit 6739631973) (nat_lit 0) A10K2.t4767 from rfl, totK_node, tot4766, tot4767]
  decide +kernel

theorem arows4764 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4764 = true := by
  rw [show A10K2.u4764 = KTree.node A10K2.t4768 (nat_lit 74718020) (nat_lit 12221605977) (nat_lit 0) A10K2.t4769 from rfl, allE_node, rows4768, irow4764, rows4769]
  all_goals rfl

theorem atot4764 : totK PA10K2 A10K2.u4764 = [0, 0, 480663153280, 2636508126583, 4231505961269, 1994814360061, 232346790218, 5447185874, 0, 0] := by
  rw [show A10K2.u4764 = KTree.node A10K2.t4768 (nat_lit 74718020) (nat_lit 12221605977) (nat_lit 0) A10K2.t4769 from rfl, totK_node, tot4768, tot4769]
  decide +kernel

theorem arows4765 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4765 = true := by
  rw [show A10K2.u4765 = KTree.node A10K2.t4770 (nat_lit 74731973) (nat_lit 5079387408) (nat_lit 0) A10K2.t4771 from rfl, allE_node, rows4770, irow4765, rows4771]
  all_goals rfl

theorem atot4765 : totK PA10K2 A10K2.u4765 = [0, 0, 571006147511, 2605576668190, 4092550168910, 1912035670563, 225099385115, 6354482628, 0, 0] := by
  rw [show A10K2.u4765 = KTree.node A10K2.t4770 (nat_lit 74731973) (nat_lit 5079387408) (nat_lit 0) A10K2.t4771 from rfl, totK_node, tot4770, tot4771]
  decide +kernel

theorem arows4767 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4767 = true := by
  rw [show A10K2.u4767 = KTree.node A10K2.t4772 (nat_lit 74788051) (nat_lit 10776653335) (nat_lit 0) A10K2.t4773 from rfl, allE_node, rows4772, irow4767, rows4773]
  all_goals rfl

theorem atot4767 : totK PA10K2 A10K2.u4767 = [0, 0, 561246024432, 2738043174321, 4023045033180, 1928072117500, 310770829983, 20340910120, 0, 0] := by
  rw [show A10K2.u4767 = KTree.node A10K2.t4772 (nat_lit 74788051) (nat_lit 10776653335) (nat_lit 0) A10K2.t4773 from rfl, totK_node, tot4772, tot4773]
  decide +kernel

theorem arows4768 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4768 = true := by
  rw [show A10K2.u4768 = KTree.node A10K2.t4774 (nat_lit 74793261) (nat_lit 6613758113) (nat_lit 0) A10K2.t4775 from rfl, allE_node, rows4774, irow4768, rows4775]
  all_goals rfl

theorem atot4768 : totK PA10K2 A10K2.u4768 = [0, 0, 660489524108, 2654623417585, 3762675068667, 2043486328095, 340308191320, 11111663730, 0, 0] := by
  rw [show A10K2.u4768 = KTree.node A10K2.t4774 (nat_lit 74793261) (nat_lit 6613758113) (nat_lit 0) A10K2.t4775 from rfl, totK_node, tot4774, tot4775]
  decide +kernel

theorem arows4771 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4771 = true := by
  rw [show A10K2.u4771 = KTree.node A10K2.t4776 (nat_lit 74799259) (nat_lit 10005476535) (nat_lit 0) A10K2.t4777 from rfl, allE_node, rows4776, irow4771, rows4777]
  all_goals rfl

theorem atot4771 : totK PA10K2 A10K2.u4771 = [0, 0, 405068075292, 2471879520377, 4235298112187, 2094410856376, 261256223164, 6354482628, 0, 0] := by
  rw [show A10K2.u4771 = KTree.node A10K2.t4776 (nat_lit 74799259) (nat_lit 10005476535) (nat_lit 0) A10K2.t4777 from rfl, totK_node, tot4776, tot4777]
  decide +kernel

theorem arows4772 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4772 = true := by
  rw [show A10K2.u4772 = KTree.node A10K2.t4778 (nat_lit 74807026) (nat_lit 14659720466) (nat_lit 0) A10K2.t4779 from rfl, allE_node, rows4778, irow4772, rows4779]
  all_goals rfl

theorem atot4772 : totK PA10K2 A10K2.u4772 = [0, 0, 636223379725, 2730858337302, 4089322138856, 2132405977792, 306183489565, 6962742351, 0, 0] := by
  rw [show A10K2.u4772 = KTree.node A10K2.t4778 (nat_lit 74807026) (nat_lit 14659720466) (nat_lit 0) A10K2.t4779 from rfl, totK_node, tot4778, tot4779]
  decide +kernel

theorem arows4774 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4774 = true := by
  rw [show A10K2.u4774 = KTree.node A10K2.t4780 (nat_lit 74848362) (nat_lit 5180462267) (nat_lit 0) A10K2.t4781 from rfl, allE_node, rows4780, irow4774, rows4781]
  all_goals rfl

theorem atot4774 : totK PA10K2 A10K2.u4774 = [0, 0, 574237096426, 2793945413614, 4141579720373, 1758768851658, 207267071500, 5460492893, 0, 0] := by
  rw [show A10K2.u4774 = KTree.node A10K2.t4780 (nat_lit 74848362) (nat_lit 5180462267) (nat_lit 0) A10K2.t4781 from rfl, totK_node, tot4780, tot4781]
  decide +kernel

theorem arows4775 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4775 = true := by
  rw [show A10K2.u4775 = KTree.node A10K2.t4782 (nat_lit 74854387) (nat_lit 7586581760) (nat_lit 0) A10K2.t4783 from rfl, allE_node, rows4782, irow4775, rows4783]
  all_goals rfl

theorem atot4775 : totK PA10K2 A10K2.u4775 = [0, 0, 465436217816, 2361049618389, 3999864263720, 2276479763306, 375230317523, 24969229125, 0, 0] := by
  rw [show A10K2.u4775 = KTree.node A10K2.t4782 (nat_lit 74854387) (nat_lit 7586581760) (nat_lit 0) A10K2.t4783 from rfl, totK_node, tot4782, tot4783]
  decide +kernel

theorem arows4779 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4779 = true := by
  rw [show A10K2.u4779 = KTree.node A10K2.t4784 (nat_lit 74859816) (nat_lit 10765362436) (nat_lit 0) A10K2.t4785 from rfl, allE_node, rows4784, irow4779, rows4785]
  all_goals rfl

theorem atot4779 : totK PA10K2 A10K2.u4779 = [0, 0, 836002267270, 3286221468488, 3794494994881, 1350384546684, 183019956574, 6034215561, 0, 0] := by
  rw [show A10K2.u4779 = KTree.node A10K2.t4784 (nat_lit 74859816) (nat_lit 10765362436) (nat_lit 0) A10K2.t4785 from rfl, totK_node, tot4784, tot4785]
  decide +kernel

theorem arows4780 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4780 = true := by
  rw [show A10K2.u4780 = KTree.node A10K2.t4786 (nat_lit 74865415) (nat_lit 4701807413) (nat_lit 0) A10K2.t4787 from rfl, allE_node, rows4786, irow4780, rows4787]
  all_goals rfl

theorem atot4780 : totK PA10K2 A10K2.u4780 = [0, 0, 0, 1304826045031, 4273084786949, 3118693692394, 503840995940, 11740475125, 0, 0] := by
  rw [show A10K2.u4780 = KTree.node A10K2.t4786 (nat_lit 74865415) (nat_lit 4701807413) (nat_lit 0) A10K2.t4787 from rfl, totK_node, tot4786, tot4787]
  decide +kernel

theorem arows4782 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4782 = true := by
  rw [show A10K2.u4782 = KTree.node A10K2.t4788 (nat_lit 74885406) (nat_lit 9778753158) (nat_lit 0) A10K2.t4789 from rfl, allE_node, rows4788, irow4782, rows4789]
  all_goals rfl

theorem atot4782 : totK PA10K2 A10K2.u4782 = [0, 0, 0, 1208236132862, 3912854656960, 3388990593468, 751121939898, 43465415927, 0, 0] := by
  rw [show A10K2.u4782 = KTree.node A10K2.t4788 (nat_lit 74885406) (nat_lit 9778753158) (nat_lit 0) A10K2.t4789 from rfl, totK_node, tot4788, tot4789]
  decide +kernel

theorem arows4783 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4783 = true := by
  rw [show A10K2.u4783 = KTree.node A10K2.t4790 (nat_lit 74894125) (nat_lit 6630724235) (nat_lit 0) A10K2.t4791 from rfl, allE_node, rows4790, irow4783, rows4791]
  all_goals rfl

theorem atot4783 : totK PA10K2 A10K2.u4783 = [0, 0, 0, 465281826316, 2666379533756, 4061269803846, 1682539263962, 160108385923, 0, 0] := by
  rw [show A10K2.u4783 = KTree.node A10K2.t4790 (nat_lit 74894125) (nat_lit 6630724235) (nat_lit 0) A10K2.t4791 from rfl, totK_node, tot4790, tot4791]
  decide +kernel

theorem arows4786 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4786 = true := by
  rw [show A10K2.u4786 = KTree.node A10K2.t4792 (nat_lit 75049627) (nat_lit 9948771239) (nat_lit 0) A10K2.t4793 from rfl, allE_node, rows4792, irow4786, rows4793]
  all_goals rfl

theorem atot4786 : totK PA10K2 A10K2.u4786 = [0, 843699735084, 3298343614154, 3918570057023, 1377330492160, 104020221355, 117388024790, 86874954689, 6354482628, 0] := by
  rw [show A10K2.u4786 = KTree.node A10K2.t4792 (nat_lit 75049627) (nat_lit 9948771239) (nat_lit 0) A10K2.t4793 from rfl, totK_node, tot4792, tot4793]
  decide +kernel

theorem arows4787 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4787 = true := by
  rw [show A10K2.u4787 = KTree.node A10K2.t4794 (nat_lit 75054293) (nat_lit 5626692054) (nat_lit 0) A10K2.t4795 from rfl, allE_node, rows4794, irow4787, rows4795]
  all_goals rfl

theorem atot4787 : totK PA10K2 A10K2.u4787 = [0, 520167364468, 2216540164539, 3659832643961, 2640910614653, 581305027309, 31768748853, 0, 0, 0] := by
  rw [show A10K2.u4787 = KTree.node A10K2.t4794 (nat_lit 75054293) (nat_lit 5626692054) (nat_lit 0) A10K2.t4795 from rfl, totK_node, tot4794, tot4795]
  decide +kernel

theorem arows4789 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4789 = true := by
  rw [show A10K2.u4789 = KTree.node A10K2.t4796 (nat_lit 75062042) (nat_lit 11757977360) (nat_lit 0) A10K2.t4797 from rfl, allE_node, rows4796, irow4789, rows4797]
  all_goals rfl

theorem atot4789 : totK PA10K2 A10K2.u4789 = [0, 526655018994, 2788979668574, 4247702403966, 1938993411191, 234812641313, 5982052406, 0, 0, 0] := by
  rw [show A10K2.u4789 = KTree.node A10K2.t4796 (nat_lit 75062042) (nat_lit 11757977360) (nat_lit 0) A10K2.t4797 from rfl, totK_node, tot4796, tot4797]
  decide +kernel

theorem arows4790 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4790 = true := by
  rw [show A10K2.u4790 = KTree.node A10K2.t4798 (nat_lit 75068295) (nat_lit 14425336065) (nat_lit 0) A10K2.t4799 from rfl, allE_node, rows4798, irow4790, rows4799]
  all_goals rfl

theorem atot4790 : totK PA10K2 A10K2.u4790 = [0, 316779408161, 1966744930118, 4172904076421, 3136273366574, 610792692382, 13548089516, 0, 0, 0] := by
  rw [show A10K2.u4790 = KTree.node A10K2.t4798 (nat_lit 75068295) (nat_lit 14425336065) (nat_lit 0) A10K2.t4799 from rfl, totK_node, tot4798, tot4799]
  decide +kernel

end QECKChecks.A10K2
