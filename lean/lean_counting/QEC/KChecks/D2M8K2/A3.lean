import QEC.Count.ChunksK3
import QEC.KChecks.D2M8K2.A2

namespace QECKChecks.D2M8K2

open QEC QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem arows3596 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3596 = true := by
  rw [show D2M8K2.u3596 = KTree.node D2M8K2.t3600 (nat_lit 8257212) (nat_lit 2475791380) (nat_lit 0) D2M8K2.t3601 from rfl, allE_node, rows3600, irow3596, rows3601]
  all_goals rfl

theorem atot3596 : totK PD2M8K2 D2M8K2.u3596 = [0, 369670017935, 925052738673, 506435465937, 48903344763, 1726220677, 0, 0] := by
  rw [show D2M8K2.u3596 = KTree.node D2M8K2.t3600 (nat_lit 8257212) (nat_lit 2475791380) (nat_lit 0) D2M8K2.t3601 from rfl, totK_node, tot3600, tot3601]
  decide +kernel

theorem arows3597 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3597 = true := by
  rw [show D2M8K2.u3597 = KTree.node D2M8K2.t3602 (nat_lit 8258674) (nat_lit 4103825510) (nat_lit 0) D2M8K2.t3603 from rfl, allE_node, rows3602, irow3597, rows3603]
  all_goals rfl

theorem atot3597 : totK PD2M8K2 D2M8K2.u3597 = [0, 74713786392, 512524558642, 842492781715, 369359096953, 29394892645, 0, 0] := by
  rw [show D2M8K2.u3597 = KTree.node D2M8K2.t3602 (nat_lit 8258674) (nat_lit 4103825510) (nat_lit 0) D2M8K2.t3603 from rfl, totK_node, tot3602, tot3603]
  decide +kernel

theorem arows3599 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3599 = true := by
  rw [show D2M8K2.u3599 = KTree.node D2M8K2.t3604 (nat_lit 8259965) (nat_lit 2292634458) (nat_lit 0) D2M8K2.t3605 from rfl, allE_node, rows3604, irow3599, rows3605]
  all_goals rfl

theorem atot3599 : totK PD2M8K2 D2M8K2.u3599 = [0, 247175611026, 693535357625, 662081529663, 215231653115, 8104085798, 0, 0] := by
  rw [show D2M8K2.u3599 = KTree.node D2M8K2.t3604 (nat_lit 8259965) (nat_lit 2292634458) (nat_lit 0) D2M8K2.t3605 from rfl, totK_node, tot3604, tot3605]
  decide +kernel

theorem arows3600 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3600 = true := by
  rw [show D2M8K2.u3600 = KTree.node D2M8K2.t3606 (nat_lit 8261477) (nat_lit 2374331571) (nat_lit 0) D2M8K2.t3607 from rfl, allE_node, rows3606, irow3600, rows3607]
  all_goals rfl

theorem atot3600 : totK PD2M8K2 D2M8K2.u3600 = [0, 166433636818, 754817543251, 748192974376, 134091567106, 5998727602, 0, 0] := by
  rw [show D2M8K2.u3600 = KTree.node D2M8K2.t3606 (nat_lit 8261477) (nat_lit 2374331571) (nat_lit 0) D2M8K2.t3607 from rfl, totK_node, tot3606, tot3607]
  decide +kernel

theorem arows3603 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3603 = true := by
  rw [show D2M8K2.u3603 = KTree.node D2M8K2.t3608 (nat_lit 8263462) (nat_lit 2156372415) (nat_lit 0) D2M8K2.t3609 from rfl, allE_node, rows3608, irow3603, rows3609]
  all_goals rfl

theorem atot3603 : totK PD2M8K2 D2M8K2.u3603 = [0, 247334276193, 753854605144, 658934239344, 145927789509, 5874298072, 0, 0] := by
  rw [show D2M8K2.u3603 = KTree.node D2M8K2.t3608 (nat_lit 8263462) (nat_lit 2156372415) (nat_lit 0) D2M8K2.t3609 from rfl, totK_node, tot3608, tot3609]
  decide +kernel

theorem arows3604 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3604 = true := by
  rw [show D2M8K2.u3604 = KTree.node D2M8K2.t3610 (nat_lit 8265002) (nat_lit 4051237869) (nat_lit 0) D2M8K2.t3611 from rfl, allE_node, rows3610, irow3604, rows3611]
  all_goals rfl

theorem atot3604 : totK PD2M8K2 D2M8K2.u3604 = [0, 166518054515, 722491055396, 741762087710, 163832777930, 8464368736, 0, 0] := by
  rw [show D2M8K2.u3604 = KTree.node D2M8K2.t3610 (nat_lit 8265002) (nat_lit 4051237869) (nat_lit 0) D2M8K2.t3611 from rfl, totK_node, tot3610, tot3611]
  decide +kernel

theorem arows3606 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3606 = true := by
  rw [show D2M8K2.u3606 = KTree.node D2M8K2.t3612 (nat_lit 8266974) (nat_lit 3930773242) (nat_lit 0) D2M8K2.t3613 from rfl, allE_node, rows3612, irow3606, rows3613]
  all_goals rfl

theorem atot3606 : totK PD2M8K2 D2M8K2.u3606 = [0, 245571422645, 766269766979, 664477963881, 130145463811, 3575904516, 0, 0] := by
  rw [show D2M8K2.u3606 = KTree.node D2M8K2.t3612 (nat_lit 8266974) (nat_lit 3930773242) (nat_lit 0) D2M8K2.t3613 from rfl, totK_node, tot3612, tot3613]
  decide +kernel

theorem arows3607 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3607 = true := by
  rw [show D2M8K2.u3607 = KTree.node D2M8K2.t3614 (nat_lit 8268152) (nat_lit 3930769992) (nat_lit 0) D2M8K2.t3615 from rfl, allE_node, rows3614, irow3607, rows3615]
  all_goals rfl

theorem atot3607 : totK PD2M8K2 D2M8K2.u3607 = [0, 177697891872, 807445538549, 747480886527, 83820682951, 0, 0, 0] := by
  rw [show D2M8K2.u3607 = KTree.node D2M8K2.t3614 (nat_lit 8268152) (nat_lit 3930769992) (nat_lit 0) D2M8K2.t3615 from rfl, totK_node, tot3614, tot3615]
  decide +kernel

theorem arows3612 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3612 = true := by
  rw [show D2M8K2.u3612 = KTree.node D2M8K2.t3616 (nat_lit 8270778) (nat_lit 3555237503) (nat_lit 0) D2M8K2.t3617 from rfl, allE_node, rows3616, irow3612, rows3617]
  all_goals rfl

theorem atot3612 : totK PD2M8K2 D2M8K2.u3612 = [0, 291844356512, 790577830510, 630060017300, 125787730415, 3880716147, 0, 0] := by
  rw [show D2M8K2.u3612 = KTree.node D2M8K2.t3616 (nat_lit 8270778) (nat_lit 3555237503) (nat_lit 0) D2M8K2.t3617 from rfl, totK_node, tot3616, tot3617]
  decide +kernel

theorem arows3613 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3613 = true := by
  rw [show D2M8K2.u3613 = KTree.node D2M8K2.t3618 (nat_lit 8272684) (nat_lit 3854928651) (nat_lit 0) D2M8K2.t3619 from rfl, allE_node, rows3618, irow3613, rows3619]
  all_goals rfl

theorem atot3613 : totK PD2M8K2 D2M8K2.u3613 = [0, 59572946477, 537718339221, 917153973004, 285136280424, 9730542555, 0, 0] := by
  rw [show D2M8K2.u3613 = KTree.node D2M8K2.t3618 (nat_lit 8272684) (nat_lit 3854928651) (nat_lit 0) D2M8K2.t3619 from rfl, totK_node, tot3618, tot3619]
  decide +kernel

theorem arows3615 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3615 = true := by
  rw [show D2M8K2.u3615 = KTree.node D2M8K2.t3620 (nat_lit 8295346) (nat_lit 3186978000) (nat_lit 0) D2M8K2.t3621 from rfl, allE_node, rows3620, irow3615, rows3621]
  all_goals rfl

theorem atot3615 : totK PD2M8K2 D2M8K2.u3615 = [0, 372835746706, 938770566961, 440620269937, 23577818935, 0, 0, 0] := by
  rw [show D2M8K2.u3615 = KTree.node D2M8K2.t3620 (nat_lit 8295346) (nat_lit 3186978000) (nat_lit 0) D2M8K2.t3621 from rfl, totK_node, tot3620, tot3621]
  decide +kernel

theorem arows3616 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3616 = true := by
  rw [show D2M8K2.u3616 = KTree.node D2M8K2.t3622 (nat_lit 8297320) (nat_lit 3315498951) (nat_lit 0) D2M8K2.t3623 from rfl, allE_node, rows3622, irow3616, rows3623]
  all_goals rfl

theorem atot3616 : totK PD2M8K2 D2M8K2.u3616 = [0, 126711120793, 664447537694, 860317970275, 148498473973, 1310166938, 0, 0] := by
  rw [show D2M8K2.u3616 = KTree.node D2M8K2.t3622 (nat_lit 8297320) (nat_lit 3315498951) (nat_lit 0) D2M8K2.t3623 from rfl, totK_node, tot3622, tot3623]
  decide +kernel

theorem arows3619 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3619 = true := by
  rw [show D2M8K2.u3619 = KTree.node D2M8K2.t3624 (nat_lit 8299106) (nat_lit 4086183302) (nat_lit 0) D2M8K2.t3625 from rfl, allE_node, rows3624, irow3619, rows3625]
  all_goals rfl

theorem atot3619 : totK PD2M8K2 D2M8K2.u3619 = [0, 292766267214, 895910954564, 589901753885, 62507556389, 0, 0, 0] := by
  rw [show D2M8K2.u3619 = KTree.node D2M8K2.t3624 (nat_lit 8299106) (nat_lit 4086183302) (nat_lit 0) D2M8K2.t3625 from rfl, totK_node, tot3624, tot3625]
  decide +kernel

theorem arows3620 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3620 = true := by
  rw [show D2M8K2.u3620 = KTree.node D2M8K2.t3626 (nat_lit 8300798) (nat_lit 3850045680) (nat_lit 0) D2M8K2.t3627 from rfl, allE_node, rows3626, irow3620, rows3627]
  all_goals rfl

theorem atot3620 : totK PD2M8K2 D2M8K2.u3620 = [0, 99785162053, 548377703040, 835698808207, 312771675570, 15013989272, 0, 0] := by
  rw [show D2M8K2.u3620 = KTree.node D2M8K2.t3626 (nat_lit 8300798) (nat_lit 3850045680) (nat_lit 0) D2M8K2.t3627 from rfl, totK_node, tot3626, tot3627]
  decide +kernel

theorem arows3622 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3622 = true := by
  rw [show D2M8K2.u3622 = KTree.node D2M8K2.t3628 (nat_lit 8302158) (nat_lit 2878608119) (nat_lit 0) D2M8K2.t3629 from rfl, allE_node, rows3628, irow3622, rows3629]
  all_goals rfl

theorem atot3622 : totK PD2M8K2 D2M8K2.u3622 = [0, 333708267323, 915404808231, 539334937041, 46329844770, 0, 0, 0] := by
  rw [show D2M8K2.u3622 = KTree.node D2M8K2.t3628 (nat_lit 8302158) (nat_lit 2878608119) (nat_lit 0) D2M8K2.t3629 from rfl, totK_node, tot3628, tot3629]
  decide +kernel

theorem arows3623 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3623 = true := by
  rw [show D2M8K2.u3623 = KTree.node D2M8K2.t3630 (nat_lit 8303817) (nat_lit 1745220646) (nat_lit 0) D2M8K2.t3631 from rfl, allE_node, rows3630, irow3623, rows3631]
  all_goals rfl

theorem atot3623 : totK PD2M8K2 D2M8K2.u3623 = [0, 70024821055, 507403715370, 898415224209, 282668072156, 13049727234, 0, 0] := by
  rw [show D2M8K2.u3623 = KTree.node D2M8K2.t3630 (nat_lit 8303817) (nat_lit 1745220646) (nat_lit 0) D2M8K2.t3631 from rfl, totK_node, tot3630, tot3631]
  decide +kernel

theorem arows3627 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3627 = true := by
  rw [show D2M8K2.u3627 = KTree.node D2M8K2.t3632 (nat_lit 8308923) (nat_lit 3566954735) (nat_lit 0) D2M8K2.t3633 from rfl, allE_node, rows3632, irow3627, rows3633]
  all_goals rfl

theorem atot3627 : totK PD2M8K2 D2M8K2.u3627 = [0, 351165171699, 912267626542, 498668807696, 40831220425, 0, 0, 0] := by
  rw [show D2M8K2.u3627 = KTree.node D2M8K2.t3632 (nat_lit 8308923) (nat_lit 3566954735) (nat_lit 0) D2M8K2.t3633 from rfl, totK_node, tot3632, tot3633]
  decide +kernel

theorem arows3628 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3628 = true := by
  rw [show D2M8K2.u3628 = KTree.node D2M8K2.t3634 (nat_lit 8310642) (nat_lit 2752898601) (nat_lit 0) D2M8K2.t3635 from rfl, allE_node, rows3634, irow3628, rows3635]
  all_goals rfl

theorem atot3628 : totK PD2M8K2 D2M8K2.u3628 = [0, 66937727143, 605519975046, 896105305414, 202671958809, 4980514959, 0, 0] := by
  rw [show D2M8K2.u3628 = KTree.node D2M8K2.t3634 (nat_lit 8310642) (nat_lit 2752898601) (nat_lit 0) D2M8K2.t3635 from rfl, totK_node, tot3634, tot3635]
  decide +kernel

theorem arows3630 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3630 = true := by
  rw [show D2M8K2.u3630 = KTree.node D2M8K2.t3636 (nat_lit 8312498) (nat_lit 3782710151) (nat_lit 0) D2M8K2.t3637 from rfl, allE_node, rows3636, irow3630, rows3637]
  all_goals rfl

theorem atot3630 : totK PD2M8K2 D2M8K2.u3630 = [0, 262778048708, 818073223350, 645226646159, 100956785348, 1181638453, 0, 0] := by
  rw [show D2M8K2.u3630 = KTree.node D2M8K2.t3636 (nat_lit 8312498) (nat_lit 3782710151) (nat_lit 0) D2M8K2.t3637 from rfl, totK_node, tot3636, tot3637]
  decide +kernel

theorem arows3631 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3631 = true := by
  rw [show D2M8K2.u3631 = KTree.node D2M8K2.t3638 (nat_lit 8335952) (nat_lit 3673627529) (nat_lit 0) D2M8K2.t3639 from rfl, allE_node, rows3638, irow3631, rows3639]
  all_goals rfl

theorem atot3631 : totK PD2M8K2 D2M8K2.u3631 = [0, 226606111080, 755935861865, 667954824231, 131419426651, 3699256714, 0, 0] := by
  rw [show D2M8K2.u3631 = KTree.node D2M8K2.t3638 (nat_lit 8335952) (nat_lit 3673627529) (nat_lit 0) D2M8K2.t3639 from rfl, totK_node, tot3638, tot3639]
  decide +kernel

theorem arows3634 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3634 = true := by
  rw [show D2M8K2.u3634 = KTree.node D2M8K2.t3640 (nat_lit 8337620) (nat_lit 3216646021) (nat_lit 0) D2M8K2.t3641 from rfl, allE_node, rows3640, irow3634, rows3641]
  all_goals rfl

theorem atot3634 : totK PD2M8K2 D2M8K2.u3634 = [0, 150083988337, 715370077398, 775527889926, 125608608938, 1310517177, 0, 0] := by
  rw [show D2M8K2.u3634 = KTree.node D2M8K2.t3640 (nat_lit 8337620) (nat_lit 3216646021) (nat_lit 0) D2M8K2.t3641 from rfl, totK_node, tot3640, tot3641]
  decide +kernel

theorem arows3635 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3635 = true := by
  rw [show D2M8K2.u3635 = KTree.node D2M8K2.t3642 (nat_lit 8340040) (nat_lit 3709425204) (nat_lit 0) D2M8K2.t3643 from rfl, allE_node, rows3642, irow3635, rows3643]
  all_goals rfl

theorem atot3635 : totK PD2M8K2 D2M8K2.u3635 = [0, 338562081873, 901907269941, 565989982703, 50175096652, 0, 0, 0] := by
  rw [show D2M8K2.u3635 = KTree.node D2M8K2.t3642 (nat_lit 8340040) (nat_lit 3709425204) (nat_lit 0) D2M8K2.t3643 from rfl, totK_node, tot3642, tot3643]
  decide +kernel

theorem arows3637 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3637 = true := by
  rw [show D2M8K2.u3637 = KTree.node D2M8K2.t3644 (nat_lit 8341584) (nat_lit 2188473030) (nat_lit 0) D2M8K2.t3645 from rfl, allE_node, rows3644, irow3637, rows3645]
  all_goals rfl

theorem atot3637 : totK PD2M8K2 D2M8K2.u3637 = [0, 80989279708, 598838288480, 870317390083, 276414755356, 13656771860, 0, 0] := by
  rw [show D2M8K2.u3637 = KTree.node D2M8K2.t3644 (nat_lit 8341584) (nat_lit 2188473030) (nat_lit 0) D2M8K2.t3645 from rfl, totK_node, tot3644, tot3645]
  decide +kernel

theorem arows3638 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3638 = true := by
  rw [show D2M8K2.u3638 = KTree.node D2M8K2.t3646 (nat_lit 8346614) (nat_lit 3999417673) (nat_lit 0) D2M8K2.t3647 from rfl, allE_node, rows3646, irow3638, rows3647]
  all_goals rfl

theorem atot3638 : totK PD2M8K2 D2M8K2.u3638 = [0, 302601104852, 817321828673, 590207808482, 116370630373, 1409560813, 0, 0] := by
  rw [show D2M8K2.u3638 = KTree.node D2M8K2.t3646 (nat_lit 8346614) (nat_lit 3999417673) (nat_lit 0) D2M8K2.t3647 from rfl, totK_node, tot3646, tot3647]
  decide +kernel

theorem arows3644 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3644 = true := by
  rw [show D2M8K2.u3644 = KTree.node D2M8K2.t3648 (nat_lit 8348070) (nat_lit 3749681023) (nat_lit 0) D2M8K2.t3649 from rfl, allE_node, rows3648, irow3644, rows3649]
  all_goals rfl

theorem atot3644 : totK PD2M8K2 D2M8K2.u3644 = [0, 135115210903, 649081968523, 789550690773, 207675486822, 9649412842, 0, 0] := by
  rw [show D2M8K2.u3644 = KTree.node D2M8K2.t3648 (nat_lit 8348070) (nat_lit 3749681023) (nat_lit 0) D2M8K2.t3649 from rfl, totK_node, tot3648, tot3649]
  decide +kernel

theorem arows3645 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3645 = true := by
  rw [show D2M8K2.u3645 = KTree.node D2M8K2.t3650 (nat_lit 8349852) (nat_lit 3509432056) (nat_lit 0) D2M8K2.t3651 from rfl, allE_node, rows3650, irow3645, rows3651]
  all_goals rfl

theorem atot3645 : totK PD2M8K2 D2M8K2.u3645 = [0, 240606606202, 763309794416, 647854092689, 124798860754, 3521263076, 0, 0] := by
  rw [show D2M8K2.u3645 = KTree.node D2M8K2.t3650 (nat_lit 8349852) (nat_lit 3509432056) (nat_lit 0) D2M8K2.t3651 from rfl, totK_node, tot3650, tot3651]
  decide +kernel

theorem arows3647 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3647 = true := by
  rw [show D2M8K2.u3647 = KTree.node D2M8K2.t3652 (nat_lit 8351093) (nat_lit 2211414021) (nat_lit 0) D2M8K2.t3653 from rfl, allE_node, rows3652, irow3647, rows3653]
  all_goals rfl

theorem atot3647 : totK PD2M8K2 D2M8K2.u3647 = [0, 180619357860, 751802937622, 747076040080, 114345526439, 1096505104, 0, 0] := by
  rw [show D2M8K2.u3647 = KTree.node D2M8K2.t3652 (nat_lit 8351093) (nat_lit 2211414021) (nat_lit 0) D2M8K2.t3653 from rfl, totK_node, tot3652, tot3653]
  decide +kernel

theorem arows3648 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3648 = true := by
  rw [show D2M8K2.u3648 = KTree.node D2M8K2.t3654 (nat_lit 8353473) (nat_lit 1665996983) (nat_lit 0) D2M8K2.t3655 from rfl, allE_node, rows3654, irow3648, rows3655]
  all_goals rfl

theorem atot3648 : totK PD2M8K2 D2M8K2.u3648 = [0, 254073651188, 769546360213, 660455103710, 133632966551, 3884009855, 0, 0] := by
  rw [show D2M8K2.u3648 = KTree.node D2M8K2.t3654 (nat_lit 8353473) (nat_lit 1665996983) (nat_lit 0) D2M8K2.t3655 from rfl, totK_node, tot3654, tot3655]
  decide +kernel

theorem arows3651 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3651 = true := by
  rw [show D2M8K2.u3651 = KTree.node D2M8K2.t3656 (nat_lit 8355280) (nat_lit 2625737066) (nat_lit 0) D2M8K2.t3657 from rfl, allE_node, rows3656, irow3651, rows3657]
  all_goals rfl

theorem atot3651 : totK PD2M8K2 D2M8K2.u3651 = [0, 145045871803, 660260106899, 807398765292, 197550546961, 4934554315, 0, 0] := by
  rw [show D2M8K2.u3651 = KTree.node D2M8K2.t3656 (nat_lit 8355280) (nat_lit 2625737066) (nat_lit 0) D2M8K2.t3657 from rfl, totK_node, tot3656, tot3657]
  decide +kernel

theorem arows3652 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3652 = true := by
  rw [show D2M8K2.u3652 = KTree.node D2M8K2.t3658 (nat_lit 8378358) (nat_lit 3818222609) (nat_lit 0) D2M8K2.t3659 from rfl, allE_node, rows3658, irow3652, rows3659]
  all_goals rfl

theorem atot3652 : totK PD2M8K2 D2M8K2.u3652 = [0, 321341735712, 906335151518, 483947362862, 28823725675, 0, 0, 0] := by
  rw [show D2M8K2.u3652 = KTree.node D2M8K2.t3658 (nat_lit 8378358) (nat_lit 3818222609) (nat_lit 0) D2M8K2.t3659 from rfl, totK_node, tot3658, tot3659]
  decide +kernel

theorem arows3654 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3654 = true := by
  rw [show D2M8K2.u3654 = KTree.node D2M8K2.t3660 (nat_lit 8380269) (nat_lit 1392942350) (nat_lit 0) D2M8K2.t3661 from rfl, allE_node, rows3660, irow3654, rows3661]
  all_goals rfl

theorem atot3654 : totK PD2M8K2 D2M8K2.u3654 = [0, 133377405113, 667521816206, 850498105636, 139989466544, 1326647619, 0, 0] := by
  rw [show D2M8K2.u3654 = KTree.node D2M8K2.t3660 (nat_lit 8380269) (nat_lit 1392942350) (nat_lit 0) D2M8K2.t3661 from rfl, totK_node, tot3660, tot3661]
  decide +kernel

theorem arows3655 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3655 = true := by
  rw [show D2M8K2.u3655 = KTree.node D2M8K2.t3662 (nat_lit 8382020) (nat_lit 3388110699) (nat_lit 0) D2M8K2.t3663 from rfl, allE_node, rows3662, irow3655, rows3663]
  all_goals rfl

theorem atot3655 : totK PD2M8K2 D2M8K2.u3655 = [0, 287535515355, 889148456696, 586947801163, 62018744257, 0, 0, 0] := by
  rw [show D2M8K2.u3655 = KTree.node D2M8K2.t3662 (nat_lit 8382020) (nat_lit 3388110699) (nat_lit 0) D2M8K2.t3663 from rfl, totK_node, tot3662, tot3663]
  decide +kernel

theorem arows3659 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3659 = true := by
  rw [show D2M8K2.u3659 = KTree.node D2M8K2.t3664 (nat_lit 8383616) (nat_lit 3558778235) (nat_lit 0) D2M8K2.t3665 from rfl, allE_node, rows3664, irow3659, rows3665]
  all_goals rfl

theorem atot3659 : totK PD2M8K2 D2M8K2.u3659 = [0, 82166277453, 448573844862, 855373949983, 380534727384, 23711123474, 0, 0] := by
  rw [show D2M8K2.u3659 = KTree.node D2M8K2.t3664 (nat_lit 8383616) (nat_lit 3558778235) (nat_lit 0) D2M8K2.t3665 from rfl, totK_node, tot3664, tot3665]
  decide +kernel

theorem arows3660 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3660 = true := by
  rw [show D2M8K2.u3660 = KTree.node D2M8K2.t3666 (nat_lit 8384974) (nat_lit 3776288054) (nat_lit 0) D2M8K2.t3667 from rfl, allE_node, rows3666, irow3660, rows3667]
  all_goals rfl

theorem atot3660 : totK PD2M8K2 D2M8K2.u3660 = [0, 334448667850, 929510971890, 503242948072, 36314616075, 0, 0, 0] := by
  rw [show D2M8K2.u3660 = KTree.node D2M8K2.t3666 (nat_lit 8384974) (nat_lit 3776288054) (nat_lit 0) D2M8K2.t3667 from rfl, totK_node, tot3666, tot3667]
  decide +kernel

theorem arows3662 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3662 = true := by
  rw [show D2M8K2.u3662 = KTree.node D2M8K2.t3668 (nat_lit 8386702) (nat_lit 3582593072) (nat_lit 0) D2M8K2.t3669 from rfl, allE_node, rows3668, irow3662, rows3669]
  all_goals rfl

theorem atot3662 : totK PD2M8K2 D2M8K2.u3662 = [0, 49782501411, 497593186188, 921232459177, 266421319820, 12909266092, 0, 0] := by
  rw [show D2M8K2.u3662 = KTree.node D2M8K2.t3668 (nat_lit 8386702) (nat_lit 3582593072) (nat_lit 0) D2M8K2.t3669 from rfl, totK_node, tot3668, tot3669]
  decide +kernel

theorem arows3663 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3663 = true := by
  rw [show D2M8K2.u3663 = KTree.node D2M8K2.t3670 (nat_lit 8388674) (nat_lit 4015663094) (nat_lit 0) D2M8K2.t3671 from rfl, allE_node, rows3670, irow3663, rows3671]
  all_goals rfl

theorem atot3663 : totK PD2M8K2 D2M8K2.u3663 = [0, 367044595387, 936153625019, 470781927825, 35255001582, 0, 0, 0] := by
  rw [show D2M8K2.u3663 = KTree.node D2M8K2.t3670 (nat_lit 8388674) (nat_lit 4015663094) (nat_lit 0) D2M8K2.t3671 from rfl, totK_node, tot3670, tot3671]
  decide +kernel

theorem arows3666 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3666 = true := by
  rw [show D2M8K2.u3666 = KTree.node D2M8K2.t3672 (nat_lit 8390397) (nat_lit 1557166096) (nat_lit 0) D2M8K2.t3673 from rfl, allE_node, rows3672, irow3666, rows3673]
  all_goals rfl

theorem atot3666 : totK PD2M8K2 D2M8K2.u3666 = [0, 18530029189, 485864499144, 957143873698, 276659705741, 13110073960, 0, 0] := by
  rw [show D2M8K2.u3666 = KTree.node D2M8K2.t3672 (nat_lit 8390397) (nat_lit 1557166096) (nat_lit 0) D2M8K2.t3673 from rfl, totK_node, tot3672, tot3673]
  decide +kernel

theorem arows3667 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3667 = true := by
  rw [show D2M8K2.u3667 = KTree.node D2M8K2.t3674 (nat_lit 8391774) (nat_lit 3240629805) (nat_lit 0) D2M8K2.t3675 from rfl, allE_node, rows3674, irow3667, rows3675]
  all_goals rfl

theorem atot3667 : totK PD2M8K2 D2M8K2.u3667 = [0, 368942318496, 933794110170, 486596952722, 39696982375, 0, 0, 0] := by
  rw [show D2M8K2.u3667 = KTree.node D2M8K2.t3674 (nat_lit 8391774) (nat_lit 3240629805) (nat_lit 0) D2M8K2.t3675 from rfl, totK_node, tot3674, tot3675]
  decide +kernel

theorem arows3669 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3669 = true := by
  rw [show D2M8K2.u3669 = KTree.node D2M8K2.t3676 (nat_lit 8393308) (nat_lit 3675606742) (nat_lit 0) D2M8K2.t3677 from rfl, allE_node, rows3676, irow3669, rows3677]
  all_goals rfl

theorem atot3669 : totK PD2M8K2 D2M8K2.u3669 = [0, 56111990362, 622880086266, 931398181295, 194277464847, 3254603437, 0, 0] := by
  rw [show D2M8K2.u3669 = KTree.node D2M8K2.t3676 (nat_lit 8393308) (nat_lit 3675606742) (nat_lit 0) D2M8K2.t3677 from rfl, totK_node, tot3676, tot3677]
  decide +kernel

theorem arows3670 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3670 = true := by
  rw [show D2M8K2.u3670 = KTree.node D2M8K2.t3678 (nat_lit 8398983) (nat_lit 2426488630) (nat_lit 0) D2M8K2.t3679 from rfl, allE_node, rows3678, irow3670, rows3679]
  all_goals rfl

theorem atot3670 : totK PD2M8K2 D2M8K2.u3670 = [0, 0, 389644345300, 933340938281, 378474234872, 23676525146, 0, 0] := by
  rw [show D2M8K2.u3670 = KTree.node D2M8K2.t3678 (nat_lit 8398983) (nat_lit 2426488630) (nat_lit 0) D2M8K2.t3679 from rfl, totK_node, tot3678, tot3679]
  decide +kernel

theorem arows3675 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3675 = true := by
  rw [show D2M8K2.u3675 = KTree.node D2M8K2.t3680 (nat_lit 8401000) (nat_lit 2825762577) (nat_lit 0) D2M8K2.t3681 from rfl, allE_node, rows3680, irow3675, rows3681]
  all_goals rfl

theorem atot3675 : totK PD2M8K2 D2M8K2.u3675 = [0, 0, 161520073018, 746193207852, 701442156304, 103246489098, 1138244013, 0] := by
  rw [show D2M8K2.u3675 = KTree.node D2M8K2.t3680 (nat_lit 8401000) (nat_lit 2825762577) (nat_lit 0) D2M8K2.t3681 from rfl, totK_node, tot3680, tot3681]
  decide +kernel

theorem arows3676 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3676 = true := by
  rw [show D2M8K2.u3676 = KTree.node D2M8K2.t3682 (nat_lit 8402864) (nat_lit 3810331381) (nat_lit 0) D2M8K2.t3683 from rfl, allE_node, rows3682, irow3676, rows3683]
  all_goals rfl

theorem atot3676 : totK PD2M8K2 D2M8K2.u3676 = [0, 0, 424805617417, 983736793667, 348838265182, 12989867179, 0, 0] := by
  rw [show D2M8K2.u3676 = KTree.node D2M8K2.t3682 (nat_lit 8402864) (nat_lit 3810331381) (nat_lit 0) D2M8K2.t3683 from rfl, totK_node, tot3682, tot3683]
  decide +kernel

theorem arows3678 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3678 = true := by
  rw [show D2M8K2.u3678 = KTree.node D2M8K2.t3684 (nat_lit 8406306) (nat_lit 2204190690) (nat_lit 0) D2M8K2.t3685 from rfl, allE_node, rows3684, irow3678, rows3685]
  all_goals rfl

theorem atot3678 : totK PD2M8K2 D2M8K2.u3678 = [0, 0, 400969717617, 947576126406, 391607598313, 23122100040, 0, 0] := by
  rw [show D2M8K2.u3678 = KTree.node D2M8K2.t3684 (nat_lit 8406306) (nat_lit 2204190690) (nat_lit 0) D2M8K2.t3685 from rfl, totK_node, tot3684, tot3685]
  decide +kernel

theorem arows3679 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3679 = true := by
  rw [show D2M8K2.u3679 = KTree.node D2M8K2.t3686 (nat_lit 8409716) (nat_lit 3702589852) (nat_lit 0) D2M8K2.t3687 from rfl, allE_node, rows3686, irow3679, rows3687]
  all_goals rfl

theorem atot3679 : totK PD2M8K2 D2M8K2.u3679 = [0, 0, 390387485684, 951795878827, 403724821567, 23257212353, 0, 0] := by
  rw [show D2M8K2.u3679 = KTree.node D2M8K2.t3686 (nat_lit 8409716) (nat_lit 3702589852) (nat_lit 0) D2M8K2.t3687 from rfl, totK_node, tot3686, tot3687]
  decide +kernel

theorem arows3682 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3682 = true := by
  rw [show D2M8K2.u3682 = KTree.node D2M8K2.t3688 (nat_lit 8412872) (nat_lit 3909129062) (nat_lit 0) D2M8K2.t3689 from rfl, allE_node, rows3688, irow3682, rows3689]
  all_goals rfl

theorem atot3682 : totK PD2M8K2 D2M8K2.u3682 = [0, 0, 297187059768, 887161274143, 538186181144, 49806853873, 0, 0] := by
  rw [show D2M8K2.u3682 = KTree.node D2M8K2.t3688 (nat_lit 8412872) (nat_lit 3909129062) (nat_lit 0) D2M8K2.t3689 from rfl, totK_node, tot3688, tot3689]
  decide +kernel

theorem arows3683 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3683 = true := by
  rw [show D2M8K2.u3683 = KTree.node D2M8K2.t3690 (nat_lit 8414842) (nat_lit 2249148548) (nat_lit 0) D2M8K2.t3691 from rfl, allE_node, rows3690, irow3683, rows3691]
  all_goals rfl

theorem atot3683 : totK PD2M8K2 D2M8K2.u3683 = [169749411087, 341393312455, 102244770237, 343366740377, 623655417614, 173220011144, 4977114383, 0] := by
  rw [show D2M8K2.u3683 = KTree.node D2M8K2.t3690 (nat_lit 8414842) (nat_lit 2249148548) (nat_lit 0) D2M8K2.t3691 from rfl, totK_node, tot3690, tot3691]
  decide +kernel

theorem arows3685 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3685 = true := by
  rw [show D2M8K2.u3685 = KTree.node D2M8K2.t3692 (nat_lit 8461606) (nat_lit 1260775280) (nat_lit 0) D2M8K2.t3693 from rfl, allE_node, rows3692, irow3685, rows3693]
  all_goals rfl

theorem atot3685 : totK PD2M8K2 D2M8K2.u3685 = [252369620453, 822597777447, 621182129351, 91164361814, 1369150432, 0, 0, 0] := by
  rw [show D2M8K2.u3685 = KTree.node D2M8K2.t3692 (nat_lit 8461606) (nat_lit 1260775280) (nat_lit 0) D2M8K2.t3693 from rfl, totK_node, tot3692, tot3693]
  decide +kernel

theorem arows3686 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3686 = true := by
  rw [show D2M8K2.u3686 = KTree.node D2M8K2.t3694 (nat_lit 8463576) (nat_lit 3603225515) (nat_lit 0) D2M8K2.t3695 from rfl, allE_node, rows3694, irow3686, rows3695]
  all_goals rfl

theorem atot3686 : totK PD2M8K2 D2M8K2.u3686 = [186800965232, 760690973685, 761788347750, 103553949241, 0, 0, 0, 0] := by
  rw [show D2M8K2.u3686 = KTree.node D2M8K2.t3694 (nat_lit 8463576) (nat_lit 3603225515) (nat_lit 0) D2M8K2.t3695 from rfl, totK_node, tot3694, tot3695]
  decide +kernel

theorem arows3690 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3690 = true := by
  rw [show D2M8K2.u3690 = KTree.node D2M8K2.t3696 (nat_lit 8468734) (nat_lit 3870575238) (nat_lit 0) D2M8K2.t3697 from rfl, allE_node, rows3696, irow3690, rows3697]
  all_goals rfl

theorem atot3690 : totK PD2M8K2 D2M8K2.u3690 = [210350327397, 779255473661, 692601828360, 110263137902, 1164319620, 0, 0, 0] := by
  rw [show D2M8K2.u3690 = KTree.node D2M8K2.t3696 (nat_lit 8468734) (nat_lit 3870575238) (nat_lit 0) D2M8K2.t3697 from rfl, totK_node, tot3696, tot3697]
  decide +kernel

theorem arows3691 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3691 = true := by
  rw [show D2M8K2.u3691 = KTree.node D2M8K2.t3698 (nat_lit 8470493) (nat_lit 2232995411) (nat_lit 0) D2M8K2.t3699 from rfl, allE_node, rows3698, irow3691, rows3699]
  all_goals rfl

theorem atot3691 : totK PD2M8K2 D2M8K2.u3691 = [190831994900, 651482395571, 714590848550, 219667118783, 11885407614, 0, 0, 0] := by
  rw [show D2M8K2.u3691 = KTree.node D2M8K2.t3698 (nat_lit 8470493) (nat_lit 2232995411) (nat_lit 0) D2M8K2.t3699 from rfl, totK_node, tot3698, tot3699]
  decide +kernel

theorem arows3693 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3693 = true := by
  rw [show D2M8K2.u3693 = KTree.node D2M8K2.t3700 (nat_lit 8472220) (nat_lit 3674163886) (nat_lit 0) D2M8K2.t3701 from rfl, allE_node, rows3700, irow3693, rows3701]
  all_goals rfl

theorem atot3693 : totK PD2M8K2 D2M8K2.u3693 = [210484822245, 775753596344, 699364517672, 113692014754, 1198073392, 0, 0, 0] := by
  rw [show D2M8K2.u3693 = KTree.node D2M8K2.t3700 (nat_lit 8472220) (nat_lit 3674163886) (nat_lit 0) D2M8K2.t3701 from rfl, totK_node, tot3700, tot3701]
  decide +kernel

theorem arows3694 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3694 = true := by
  rw [show D2M8K2.u3694 = KTree.node D2M8K2.t3702 (nat_lit 8473949) (nat_lit 2050466960) (nat_lit 0) D2M8K2.t3703 from rfl, allE_node, rows3702, irow3694, rows3703]
  all_goals rfl

theorem atot3694 : totK PD2M8K2 D2M8K2.u3694 = [189370845208, 655348174343, 715232069307, 224275763671, 12052611869, 0, 0, 0] := by
  rw [show D2M8K2.u3694 = KTree.node D2M8K2.t3702 (nat_lit 8473949) (nat_lit 2050466960) (nat_lit 0) D2M8K2.t3703 from rfl, totK_node, tot3702, tot3703]
  decide +kernel

theorem arows3697 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3697 = true := by
  rw [show D2M8K2.u3697 = KTree.node D2M8K2.t3704 (nat_lit 8479053) (nat_lit 739926946) (nat_lit 0) D2M8K2.t3705 from rfl, allE_node, rows3704, irow3697, rows3705]
  all_goals rfl

theorem atot3697 : totK PD2M8K2 D2M8K2.u3697 = [237319555436, 788985597675, 663789808569, 113984685793, 1268739303, 0, 0, 0] := by
  rw [show D2M8K2.u3697 = KTree.node D2M8K2.t3704 (nat_lit 8479053) (nat_lit 739926946) (nat_lit 0) D2M8K2.t3705 from rfl, totK_node, tot3704, tot3705]
  decide +kernel

theorem arows3698 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3698 = true := by
  rw [show D2M8K2.u3698 = KTree.node D2M8K2.t3706 (nat_lit 8480743) (nat_lit 2211002723) (nat_lit 0) D2M8K2.t3707 from rfl, allE_node, rows3706, irow3698, rows3707]
  all_goals rfl

theorem atot3698 : totK PD2M8K2 D2M8K2.u3698 = [0, 391960494497, 954001261088, 407099552279, 22149860293, 0, 0, 0] := by
  rw [show D2M8K2.u3698 = KTree.node D2M8K2.t3706 (nat_lit 8480743) (nat_lit 2211002723) (nat_lit 0) D2M8K2.t3707 from rfl, totK_node, tot3706, tot3707]
  decide +kernel

theorem arows3700 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3700 = true := by
  rw [show D2M8K2.u3700 = KTree.node D2M8K2.t3708 (nat_lit 8482234) (nat_lit 2995298552) (nat_lit 0) D2M8K2.t3709 from rfl, allE_node, rows3708, irow3700, rows3709]
  all_goals rfl

theorem atot3700 : totK PD2M8K2 D2M8K2.u3700 = [0, 311450414483, 880618423823, 504292635826, 44633952404, 0, 0, 0] := by
  rw [show D2M8K2.u3700 = KTree.node D2M8K2.t3708 (nat_lit 8482234) (nat_lit 2995298552) (nat_lit 0) D2M8K2.t3709 from rfl, totK_node, tot3708, tot3709]
  decide +kernel

theorem arows3701 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3701 = true := by
  rw [show D2M8K2.u3701 = KTree.node D2M8K2.t3710 (nat_lit 8484219) (nat_lit 2175065378) (nat_lit 0) D2M8K2.t3711 from rfl, allE_node, rows3710, irow3701, rows3711]
  all_goals rfl

theorem atot3701 : totK PD2M8K2 D2M8K2.u3701 = [0, 158177155286, 738892510634, 722366271033, 123928527460, 1369150432, 0, 0] := by
  rw [show D2M8K2.u3701 = KTree.node D2M8K2.t3710 (nat_lit 8484219) (nat_lit 2175065378) (nat_lit 0) D2M8K2.t3711 from rfl, totK_node, tot3710, tot3711]
  decide +kernel

theorem arows3708 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3708 = true := by
  rw [show D2M8K2.u3708 = KTree.node D2M8K2.t3712 (nat_lit 8489434) (nat_lit 4009346706) (nat_lit 0) D2M8K2.t3713 from rfl, allE_node, rows3712, irow3708, rows3713]
  all_goals rfl

theorem atot3708 : totK PD2M8K2 D2M8K2.u3708 = [0, 396847388856, 953999059467, 417932422258, 22421051990, 0, 0, 0] := by
  rw [show D2M8K2.u3708 = KTree.node D2M8K2.t3712 (nat_lit 8489434) (nat_lit 4009346706) (nat_lit 0) D2M8K2.t3713 from rfl, totK_node, tot3712, tot3713]
  decide +kernel

theorem arows3709 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3709 = true := by
  rw [show D2M8K2.u3709 = KTree.node D2M8K2.t3714 (nat_lit 8492792) (nat_lit 3924363918) (nat_lit 0) D2M8K2.t3715 from rfl, allE_node, rows3714, irow3709, rows3715]
  all_goals rfl

theorem atot3709 : totK PD2M8K2 D2M8K2.u3709 = [0, 352350053824, 944860525961, 475078704307, 26624754354, 0, 0, 0] := by
  rw [show D2M8K2.u3709 = KTree.node D2M8K2.t3714 (nat_lit 8492792) (nat_lit 3924363918) (nat_lit 0) D2M8K2.t3715 from rfl, totK_node, tot3714, tot3715]
  decide +kernel

theorem arows3711 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3711 = true := by
  rw [show D2M8K2.u3711 = KTree.node D2M8K2.t3716 (nat_lit 8499266) (nat_lit 3160869318) (nat_lit 0) D2M8K2.t3717 from rfl, allE_node, rows3716, irow3711, rows3717]
  all_goals rfl

theorem atot3711 : totK PD2M8K2 D2M8K2.u3711 = [63854606315, 412403330618, 860705207265, 447374913864, 28363432085, 0, 0, 0] := by
  rw [show D2M8K2.u3711 = KTree.node D2M8K2.t3716 (nat_lit 8499266) (nat_lit 3160869318) (nat_lit 0) D2M8K2.t3717 from rfl, totK_node, tot3716, tot3717]
  decide +kernel

theorem arows3712 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3712 = true := by
  rw [show D2M8K2.u3712 = KTree.node D2M8K2.t3718 (nat_lit 8506166) (nat_lit 3976950402) (nat_lit 0) D2M8K2.t3719 from rfl, allE_node, rows3718, irow3712, rows3719]
  all_goals rfl

theorem atot3712 : totK PD2M8K2 D2M8K2.u3712 = [369452079425, 933181056937, 501686233082, 41258660861, 0, 0, 0, 0] := by
  rw [show D2M8K2.u3712 = KTree.node D2M8K2.t3718 (nat_lit 8506166) (nat_lit 3976950402) (nat_lit 0) D2M8K2.t3719 from rfl, totK_node, tot3718, tot3719]
  decide +kernel

theorem arows3715 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3715 = true := by
  rw [show D2M8K2.u3715 = KTree.node D2M8K2.t3720 (nat_lit 8507616) (nat_lit 2905180541) (nat_lit 0) D2M8K2.t3721 from rfl, allE_node, rows3720, irow3715, rows3721]
  all_goals rfl

theorem atot3715 : totK PD2M8K2 D2M8K2.u3715 = [8103823521, 468852445844, 926167803665, 396221783904, 29394892645, 0, 0, 0] := by
  rw [show D2M8K2.u3715 = KTree.node D2M8K2.t3720 (nat_lit 8507616) (nat_lit 2905180541) (nat_lit 0) D2M8K2.t3721 from rfl, totK_node, tot3720, tot3721]
  decide +kernel

theorem arows3716 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3716 = true := by
  rw [show D2M8K2.u3716 = KTree.node D2M8K2.t3722 (nat_lit 8508988) (nat_lit 3937950544) (nat_lit 0) D2M8K2.t3723 from rfl, allE_node, rows3722, irow3716, rows3723]
  all_goals rfl

theorem atot3716 : totK PD2M8K2 D2M8K2.u3716 = [247908963270, 707237847421, 651967114151, 205566206651, 8214505460, 0, 0, 0] := by
  rw [show D2M8K2.u3716 = KTree.node D2M8K2.t3722 (nat_lit 8508988) (nat_lit 3937950544) (nat_lit 0) D2M8K2.t3723 from rfl, totK_node, tot3722, tot3723]
  decide +kernel

theorem arows3718 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3718 = true := by
  rw [show D2M8K2.u3718 = KTree.node D2M8K2.t3724 (nat_lit 8510418) (nat_lit 2111738662) (nat_lit 0) D2M8K2.t3725 from rfl, allE_node, rows3724, irow3718, rows3725]
  all_goals rfl

theorem atot3718 : totK PD2M8K2 D2M8K2.u3718 = [167248517720, 694710997861, 757359887595, 181190613188, 7162567726, 0, 0, 0] := by
  rw [show D2M8K2.u3718 = KTree.node D2M8K2.t3724 (nat_lit 8510418) (nat_lit 2111738662) (nat_lit 0) D2M8K2.t3725 from rfl, totK_node, tot3724, tot3725]
  decide +kernel

theorem arows3719 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3719 = true := by
  rw [show D2M8K2.u3719 = KTree.node D2M8K2.t3726 (nat_lit 8512353) (nat_lit 1687688116) (nat_lit 0) D2M8K2.t3727 from rfl, allE_node, rows3726, irow3719, rows3727]
  all_goals rfl

theorem atot3719 : totK PD2M8K2 D2M8K2.u3719 = [248072748598, 768120538272, 658565562017, 137885466440, 5737564422, 0, 0, 0] := by
  rw [show D2M8K2.u3719 = KTree.node D2M8K2.t3726 (nat_lit 8512353) (nat_lit 1687688116) (nat_lit 0) D2M8K2.t3727 from rfl, totK_node, tot3726, tot3727]
  decide +kernel

theorem arows3723 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3723 = true := by
  rw [show D2M8K2.u3723 = KTree.node D2M8K2.t3728 (nat_lit 8513843) (nat_lit 2975387243) (nat_lit 0) D2M8K2.t3729 from rfl, allE_node, rows3728, irow3723, rows3729]
  all_goals rfl

theorem atot3723 : totK PD2M8K2 D2M8K2.u3723 = [167333634553, 712984285685, 764080552637, 159198060809, 2345745033, 0, 0, 0] := by
  rw [show D2M8K2.u3723 = KTree.node D2M8K2.t3728 (nat_lit 8513843) (nat_lit 2975387243) (nat_lit 0) D2M8K2.t3729 from rfl, totK_node, tot3728, tot3729]
  decide +kernel

theorem arows3724 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3724 = true := by
  rw [show D2M8K2.u3724 = KTree.node D2M8K2.t3730 (nat_lit 8515974) (nat_lit 3797779054) (nat_lit 0) D2M8K2.t3731 from rfl, allE_node, rows3730, irow3724, rows3731]
  all_goals rfl

theorem atot3724 : totK PD2M8K2 D2M8K2.u3724 = [242986670114, 707829679591, 683145727036, 182154050501, 10734237504, 0, 0, 0] := by
  rw [show D2M8K2.u3724 = KTree.node D2M8K2.t3730 (nat_lit 8515974) (nat_lit 3797779054) (nat_lit 0) D2M8K2.t3731 from rfl, totK_node, tot3730, tot3731]
  decide +kernel

theorem arows3726 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3726 = true := by
  rw [show D2M8K2.u3726 = KTree.node D2M8K2.t3732 (nat_lit 8517893) (nat_lit 2325556726) (nat_lit 0) D2M8K2.t3733 from rfl, allE_node, rows3732, irow3726, rows3733]
  all_goals rfl

theorem atot3726 : totK PD2M8K2 D2M8K2.u3726 = [130612648711, 720583816128, 820042236867, 157858328138, 3785881357, 0, 0, 0] := by
  rw [show D2M8K2.u3726 = KTree.node D2M8K2.t3732 (nat_lit 8517893) (nat_lit 2325556726) (nat_lit 0) D2M8K2.t3733 from rfl, totK_node, tot3732, tot3733]
  decide +kernel

theorem arows3727 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3727 = true := by
  rw [show D2M8K2.u3727 = KTree.node D2M8K2.t3734 (nat_lit 8519686) (nat_lit 3816079831) (nat_lit 0) D2M8K2.t3735 from rfl, allE_node, rows3734, irow3727, rows3735]
  all_goals rfl

theorem atot3727 : totK PD2M8K2 D2M8K2.u3727 = [378641810366, 930706712511, 486395173930, 39818088858, 0, 0, 0, 0] := by
  rw [show D2M8K2.u3727 = KTree.node D2M8K2.t3734 (nat_lit 8519686) (nat_lit 3816079831) (nat_lit 0) D2M8K2.t3735 from rfl, totK_node, tot3734, tot3735]
  decide +kernel

theorem arows3730 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3730 = true := by
  rw [show D2M8K2.u3730 = KTree.node D2M8K2.t3736 (nat_lit 8521362) (nat_lit 2020193937) (nat_lit 0) D2M8K2.t3737 from rfl, allE_node, rows3736, irow3730, rows3737]
  all_goals rfl

theorem atot3730 : totK PD2M8K2 D2M8K2.u3730 = [19691318959, 526373601646, 948096876237, 289238351002, 8698671106, 0, 0, 0] := by
  rw [show D2M8K2.u3730 = KTree.node D2M8K2.t3736 (nat_lit 8521362) (nat_lit 2020193937) (nat_lit 0) D2M8K2.t3737 from rfl, totK_node, tot3736, tot3737]
  decide +kernel

theorem arows3731 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3731 = true := by
  rw [show D2M8K2.u3731 = KTree.node D2M8K2.t3738 (nat_lit 8526559) (nat_lit 1880718838) (nat_lit 0) D2M8K2.t3739 from rfl, allE_node, rows3738, irow3731, rows3739]
  all_goals rfl

theorem atot3731 : totK PD2M8K2 D2M8K2.u3731 = [0, 345383509266, 907507277002, 535234276493, 48298812621, 0, 0, 0] := by
  rw [show D2M8K2.u3731 = KTree.node D2M8K2.t3738 (nat_lit 8526559) (nat_lit 1880718838) (nat_lit 0) D2M8K2.t3739 from rfl, totK_node, tot3738, tot3739]
  decide +kernel

theorem arows3733 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3733 = true := by
  rw [show D2M8K2.u3733 = KTree.node D2M8K2.t3740 (nat_lit 8528061) (nat_lit 1432197053) (nat_lit 0) D2M8K2.t3741 from rfl, allE_node, rows3740, irow3733, rows3741]
  all_goals rfl

theorem atot3733 : totK PD2M8K2 D2M8K2.u3733 = [0, 136878919973, 627667180350, 752354270629, 283004800418, 25191558099, 0, 0] := by
  rw [show D2M8K2.u3733 = KTree.node D2M8K2.t3740 (nat_lit 8528061) (nat_lit 1432197053) (nat_lit 0) D2M8K2.t3741 from rfl, totK_node, tot3740, tot3741]
  decide +kernel

theorem arows3734 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3734 = true := by
  rw [show D2M8K2.u3734 = KTree.node D2M8K2.t3742 (nat_lit 8529295) (nat_lit 2081631633) (nat_lit 0) D2M8K2.t3743 from rfl, allE_node, rows3742, irow3734, rows3743]
  all_goals rfl

theorem atot3734 : totK PD2M8K2 D2M8K2.u3734 = [0, 155842267669, 583448725751, 760563075609, 278476725317, 11730315755, 0, 0] := by
  rw [show D2M8K2.u3734 = KTree.node D2M8K2.t3742 (nat_lit 8529295) (nat_lit 2081631633) (nat_lit 0) D2M8K2.t3743 from rfl, totK_node, tot3742, tot3743]
  decide +kernel

theorem arows3739 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3739 = true := by
  rw [show D2M8K2.u3739 = KTree.node D2M8K2.t3744 (nat_lit 8530859) (nat_lit 2915256126) (nat_lit 0) D2M8K2.t3745 from rfl, allE_node, rows3744, irow3739, rows3745]
  all_goals rfl

theorem atot3739 : totK PD2M8K2 D2M8K2.u3739 = [0, 258242059521, 864248573708, 630277445628, 60326045356, 0, 0, 0] := by
  rw [show D2M8K2.u3739 = KTree.node D2M8K2.t3744 (nat_lit 8530859) (nat_lit 2915256126) (nat_lit 0) D2M8K2.t3745 from rfl, totK_node, tot3744, tot3745]
  decide +kernel

theorem arows3740 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3740 = true := by
  rw [show D2M8K2.u3740 = KTree.node D2M8K2.t3746 (nat_lit 8532718) (nat_lit 4037612518) (nat_lit 0) D2M8K2.t3747 from rfl, allE_node, rows3746, irow3740, rows3747]
  all_goals rfl

theorem atot3740 : totK PD2M8K2 D2M8K2.u3740 = [0, 191757145846, 673337933747, 741449664155, 188026406597, 5159868635, 0, 0] := by
  rw [show D2M8K2.u3740 = KTree.node D2M8K2.t3746 (nat_lit 8532718) (nat_lit 4037612518) (nat_lit 0) D2M8K2.t3747 from rfl, totK_node, tot3746, tot3747]
  decide +kernel

theorem arows3742 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3742 = true := by
  rw [show D2M8K2.u3742 = KTree.node D2M8K2.t3748 (nat_lit 8534390) (nat_lit 3930760718) (nat_lit 0) D2M8K2.t3749 from rfl, allE_node, rows3748, irow3742, rows3749]
  all_goals rfl

theorem atot3742 : totK PD2M8K2 D2M8K2.u3742 = [0, 219050533954, 848695199267, 674606230311, 72113358288, 0, 0, 0] := by
  rw [show D2M8K2.u3742 = KTree.node D2M8K2.t3748 (nat_lit 8534390) (nat_lit 3930760718) (nat_lit 0) D2M8K2.t3749 from rfl, totK_node, tot3748, tot3749]
  decide +kernel

theorem arows3743 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3743 = true := by
  rw [show D2M8K2.u3743 = KTree.node D2M8K2.t3750 (nat_lit 8536700) (nat_lit 3364050675) (nat_lit 0) D2M8K2.t3751 from rfl, allE_node, rows3750, irow3743, rows3751]
  all_goals rfl

theorem atot3743 : totK PD2M8K2 D2M8K2.u3743 = [0, 227058617277, 688975388265, 707476068622, 183298505889, 5218872685, 0, 0] := by
  rw [show D2M8K2.u3743 = KTree.node D2M8K2.t3750 (nat_lit 8536700) (nat_lit 3364050675) (nat_lit 0) D2M8K2.t3751 from rfl, totK_node, tot3750, tot3751]
  decide +kernel

theorem arows3746 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3746 = true := by
  rw [show D2M8K2.u3746 = KTree.node D2M8K2.t3752 (nat_lit 8538472) (nat_lit 3509860699) (nat_lit 0) D2M8K2.t3753 from rfl, allE_node, rows3752, irow3746, rows3753]
  all_goals rfl

theorem atot3746 : totK PD2M8K2 D2M8K2.u3746 = [0, 145283061092, 725965439383, 812664753759, 143459862185, 1415142070, 0, 0] := by
  rw [show D2M8K2.u3746 = KTree.node D2M8K2.t3752 (nat_lit 8538472) (nat_lit 3509860699) (nat_lit 0) D2M8K2.t3753 from rfl, totK_node, tot3752, tot3753]
  decide +kernel

theorem arows3747 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3747 = true := by
  rw [show D2M8K2.u3747 = KTree.node D2M8K2.t3754 (nat_lit 8540448) (nat_lit 2578268996) (nat_lit 0) D2M8K2.t3755 from rfl, allE_node, rows3754, irow3747, rows3755]
  all_goals rfl

theorem atot3747 : totK PD2M8K2 D2M8K2.u3747 = [0, 379619499557, 935607643186, 480166795755, 36437685875, 0, 0, 0] := by
  rw [show D2M8K2.u3747 = KTree.node D2M8K2.t3754 (nat_lit 8540448) (nat_lit 2578268996) (nat_lit 0) D2M8K2.t3755 from rfl, totK_node, tot3754, tot3755]
  decide +kernel

theorem arows3749 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3749 = true := by
  rw [show D2M8K2.u3749 = KTree.node D2M8K2.t3756 (nat_lit 8542234) (nat_lit 3633435250) (nat_lit 0) D2M8K2.t3757 from rfl, allE_node, rows3756, irow3749, rows3757]
  all_goals rfl

theorem atot3749 : totK PD2M8K2 D2M8K2.u3749 = [0, 19691318959, 541181896988, 951602027321, 266582631498, 4763482009, 0, 0] := by
  rw [show D2M8K2.u3749 = KTree.node D2M8K2.t3756 (nat_lit 8542234) (nat_lit 3633435250) (nat_lit 0) D2M8K2.t3757 from rfl, totK_node, tot3756, tot3757]
  decide +kernel

theorem arows3750 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3750 = true := by
  rw [show D2M8K2.u3750 = KTree.node D2M8K2.t3758 (nat_lit 8544114) (nat_lit 3428356203) (nat_lit 0) D2M8K2.t3759 from rfl, allE_node, rows3758, irow3750, rows3759]
  all_goals rfl

theorem atot3750 : totK PD2M8K2 D2M8K2.u3750 = [378822834728, 933763070126, 434552480426, 22049816186, 16217060694, 4538888690, 0, 0] := by
  rw [show D2M8K2.u3750 = KTree.node D2M8K2.t3758 (nat_lit 8544114) (nat_lit 3428356203) (nat_lit 0) D2M8K2.t3759 from rfl, totK_node, tot3758, tot3759]
  decide +kernel

theorem arows3754 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3754 = true := by
  rw [show D2M8K2.u3754 = KTree.node D2M8K2.t3760 (nat_lit 8546122) (nat_lit 2924866921) (nat_lit 0) D2M8K2.t3761 from rfl, allE_node, rows3760, irow3754, rows3761]
  all_goals rfl

theorem atot3754 : totK PD2M8K2 D2M8K2.u3754 = [100428189712, 653941975489, 891017674314, 163572694093, 1369150432, 0, 0, 0] := by
  rw [show D2M8K2.u3754 = KTree.node D2M8K2.t3760 (nat_lit 8546122) (nat_lit 2924866921) (nat_lit 0) D2M8K2.t3761 from rfl, totK_node, tot3760, tot3761]
  decide +kernel

theorem arows3755 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3755 = true := by
  rw [show D2M8K2.u3755 = KTree.node D2M8K2.t3762 (nat_lit 8547915) (nat_lit 3636325432) (nat_lit 0) D2M8K2.t3763 from rfl, allE_node, rows3762, irow3755, rows3763]
  all_goals rfl

theorem atot3755 : totK PD2M8K2 D2M8K2.u3755 = [316974642585, 914111568828, 557782256028, 51492130540, 0, 0, 0, 0] := by
  rw [show D2M8K2.u3755 = KTree.node D2M8K2.t3762 (nat_lit 8547915) (nat_lit 3636325432) (nat_lit 0) D2M8K2.t3763 from rfl, totK_node, tot3762, tot3763]
  decide +kernel

theorem arows3757 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3757 = true := by
  rw [show D2M8K2.u3757 = KTree.node D2M8K2.t3764 (nat_lit 8549419) (nat_lit 1597554018) (nat_lit 0) D2M8K2.t3765 from rfl, allE_node, rows3764, irow3757, rows3765]
  all_goals rfl

theorem atot3757 : totK PD2M8K2 D2M8K2.u3757 = [0, 345553100973, 937543536630, 502719970182, 33131405778, 0, 0, 0] := by
  rw [show D2M8K2.u3757 = KTree.node D2M8K2.t3764 (nat_lit 8549419) (nat_lit 1597554018) (nat_lit 0) D2M8K2.t3765 from rfl, totK_node, tot3764, tot3765]
  decide +kernel

theorem arows3758 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3758 = true := by
  rw [show D2M8K2.u3758 = KTree.node D2M8K2.t3766 (nat_lit 8550713) (nat_lit 1190163074) (nat_lit 0) D2M8K2.t3767 from rfl, allE_node, rows3766, irow3758, rows3767]
  all_goals rfl

theorem atot3758 : totK PD2M8K2 D2M8K2.u3758 = [366548613667, 911862837729, 470194086296, 58188121370, 4429463114, 0, 0, 0] := by
  rw [show D2M8K2.u3758 = KTree.node D2M8K2.t3766 (nat_lit 8550713) (nat_lit 1190163074) (nat_lit 0) D2M8K2.t3767 from rfl, totK_node, tot3766, tot3767]
  decide +kernel

theorem arows3761 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3761 = true := by
  rw [show D2M8K2.u3761 = KTree.node D2M8K2.t3768 (nat_lit 8552240) (nat_lit 3327894545) (nat_lit 0) D2M8K2.t3769 from rfl, allE_node, rows3768, irow3761, rows3769]
  all_goals rfl

theorem atot3761 : totK PD2M8K2 D2M8K2.u3761 = [71577605977, 551951512513, 894700162780, 258989687254, 10568566766, 0, 0, 0] := by
  rw [show D2M8K2.u3761 = KTree.node D2M8K2.t3768 (nat_lit 8552240) (nat_lit 3327894545) (nat_lit 0) D2M8K2.t3769 from rfl, totK_node, tot3768, tot3769]
  decide +kernel

theorem arows3762 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3762 = true := by
  rw [show D2M8K2.u3762 = KTree.node D2M8K2.t3770 (nat_lit 8557539) (nat_lit 3683871573) (nat_lit 0) D2M8K2.t3771 from rfl, allE_node, rows3770, irow3762, rows3771]
  all_goals rfl

theorem atot3762 : totK PD2M8K2 D2M8K2.u3762 = [327208455381, 868270326136, 550609229460, 79039509397, 2481160468, 0, 0, 0] := by
  rw [show D2M8K2.u3762 = KTree.node D2M8K2.t3770 (nat_lit 8557539) (nat_lit 3683871573) (nat_lit 0) D2M8K2.t3771 from rfl, totK_node, tot3770, tot3771]
  decide +kernel

theorem arows3764 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3764 = true := by
  rw [show D2M8K2.u3764 = KTree.node D2M8K2.t3772 (nat_lit 8559954) (nat_lit 2511294667) (nat_lit 0) D2M8K2.t3773 from rfl, allE_node, rows3772, irow3764, rows3773]
  all_goals rfl

theorem atot3764 : totK PD2M8K2 D2M8K2.u3764 = [138695734110, 672731275912, 789316690942, 179869389572, 4980514959, 0, 0, 0] := by
  rw [show D2M8K2.u3764 = KTree.node D2M8K2.t3772 (nat_lit 8559954) (nat_lit 2511294667) (nat_lit 0) D2M8K2.t3773 from rfl, totK_node, tot3772, tot3773]
  decide +kernel

theorem arows3765 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3765 = true := by
  rw [show D2M8K2.u3765 = KTree.node D2M8K2.t3774 (nat_lit 8561458) (nat_lit 3971458393) (nat_lit 0) D2M8K2.t3775 from rfl, allE_node, rows3774, irow3765, rows3775]
  all_goals rfl

theorem atot3765 : totK PD2M8K2 D2M8K2.u3765 = [287681515002, 875918637532, 606223039630, 57895822187, 0, 0, 0, 0] := by
  rw [show D2M8K2.u3765 = KTree.node D2M8K2.t3774 (nat_lit 8561458) (nat_lit 3971458393) (nat_lit 0) D2M8K2.t3775 from rfl, totK_node, tot3774, tot3775]
  decide +kernel

theorem arows3771 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3771 = true := by
  rw [show D2M8K2.u3771 = KTree.node D2M8K2.t3776 (nat_lit 8563135) (nat_lit 2327275557) (nat_lit 0) D2M8K2.t3777 from rfl, allE_node, rows3776, irow3771, rows3777]
  all_goals rfl

theorem atot3771 : totK PD2M8K2 D2M8K2.u3771 = [0, 401699962666, 953353491121, 400311940621, 22042938820, 0, 0, 0] := by
  rw [show D2M8K2.u3771 = KTree.node D2M8K2.t3776 (nat_lit 8563135) (nat_lit 2327275557) (nat_lit 0) D2M8K2.t3777 from rfl, totK_node, tot3776, tot3777]
  decide +kernel

theorem arows3772 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3772 = true := by
  rw [show D2M8K2.u3772 = KTree.node D2M8K2.t3778 (nat_lit 8565051) (nat_lit 1703190415) (nat_lit 0) D2M8K2.t3779 from rfl, allE_node, rows3778, irow3772, rows3779]
  all_goals rfl

theorem atot3772 : totK PD2M8K2 D2M8K2.u3772 = [0, 325152186600, 924925054838, 487183568957, 29789442482, 0, 0, 0] := by
  rw [show D2M8K2.u3772 = KTree.node D2M8K2.t3778 (nat_lit 8565051) (nat_lit 1703190415) (nat_lit 0) D2M8K2.t3779 from rfl, totK_node, tot3778, tot3779]
  decide +kernel

theorem arows3774 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3774 = true := by
  rw [show D2M8K2.u3774 = KTree.node D2M8K2.t3780 (nat_lit 8567215) (nat_lit 2199523919) (nat_lit 0) D2M8K2.t3781 from rfl, allE_node, rows3780, irow3774, rows3781]
  all_goals rfl

theorem atot3774 : totK PD2M8K2 D2M8K2.u3774 = [0, 181896194215, 757724392923, 741986132779, 111212541189, 1206465782, 0, 0] := by
  rw [show D2M8K2.u3774 = KTree.node D2M8K2.t3780 (nat_lit 8567215) (nat_lit 2199523919) (nat_lit 0) D2M8K2.t3781 from rfl, totK_node, tot3780, tot3781]
  decide +kernel

theorem arows3775 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3775 = true := by
  rw [show D2M8K2.u3775 = KTree.node D2M8K2.t3782 (nat_lit 8568921) (nat_lit 1538739602) (nat_lit 0) D2M8K2.t3783 from rfl, allE_node, rows3782, irow3775, rows3783]
  all_goals rfl

theorem atot3775 : totK PD2M8K2 D2M8K2.u3775 = [0, 388567124248, 953156116866, 440776897518, 23587702908, 0, 0, 0] := by
  rw [show D2M8K2.u3775 = KTree.node D2M8K2.t3782 (nat_lit 8568921) (nat_lit 1538739602) (nat_lit 0) D2M8K2.t3783 from rfl, totK_node, tot3782, tot3783]
  decide +kernel

theorem arows3778 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3778 = true := by
  rw [show D2M8K2.u3778 = KTree.node D2M8K2.t3784 (nat_lit 8572106) (nat_lit 3747410589) (nat_lit 0) D2M8K2.t3785 from rfl, allE_node, rows3784, irow3778, rows3785]
  all_goals rfl

theorem atot3778 : totK PD2M8K2 D2M8K2.u3778 = [0, 282374922097, 889886023684, 576002303647, 48697890274, 0, 0, 0] := by
  rw [show D2M8K2.u3778 = KTree.node D2M8K2.t3784 (nat_lit 8572106) (nat_lit 3747410589) (nat_lit 0) D2M8K2.t3785 from rfl, totK_node, tot3784, tot3785]
  decide +kernel

theorem arows3779 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3779 = true := by
  rw [show D2M8K2.u3779 = KTree.node D2M8K2.t3786 (nat_lit 8573810) (nat_lit 3944557962) (nat_lit 0) D2M8K2.t3787 from rfl, allE_node, rows3786, irow3779, rows3787]
  all_goals rfl

theorem atot3779 : totK PD2M8K2 D2M8K2.u3779 = [0, 103967259011, 563437353902, 794984777013, 258599740406, 13016197374, 0, 0] := by
  rw [show D2M8K2.u3779 = KTree.node D2M8K2.t3786 (nat_lit 8573810) (nat_lit 3944557962) (nat_lit 0) D2M8K2.t3787 from rfl, totK_node, tot3786, tot3787]
  decide +kernel

theorem arows3781 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3781 = true := by
  rw [show D2M8K2.u3781 = KTree.node D2M8K2.t3788 (nat_lit 8579012) (nat_lit 3401468245) (nat_lit 0) D2M8K2.t3789 from rfl, allE_node, rows3788, irow3781, rows3789]
  all_goals rfl

theorem atot3781 : totK PD2M8K2 D2M8K2.u3781 = [0, 222141432392, 819916831487, 664245236178, 85453109662, 1021600638, 0, 0] := by
  rw [show D2M8K2.u3781 = KTree.node D2M8K2.t3788 (nat_lit 8579012) (nat_lit 3401468245) (nat_lit 0) D2M8K2.t3789 from rfl, totK_node, tot3788, tot3789]
  decide +kernel

theorem arows3782 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3782 = true := by
  rw [show D2M8K2.u3782 = KTree.node D2M8K2.t3790 (nat_lit 8581582) (nat_lit 3993191833) (nat_lit 0) D2M8K2.t3791 from rfl, allE_node, rows3790, irow3782, rows3791]
  all_goals rfl

theorem atot3782 : totK PD2M8K2 D2M8K2.u3782 = [0, 280555992479, 797427838350, 583745756557, 103918529367, 3552795014, 0, 0] := by
  rw [show D2M8K2.u3782 = KTree.node D2M8K2.t3790 (nat_lit 8581582) (nat_lit 3993191833) (nat_lit 0) D2M8K2.t3791 from rfl, totK_node, tot3790, tot3791]
  decide +kernel

theorem arows3786 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3786 = true := by
  rw [show D2M8K2.u3786 = KTree.node D2M8K2.t3792 (nat_lit 8584788) (nat_lit 3271375076) (nat_lit 0) D2M8K2.t3793 from rfl, allE_node, rows3792, irow3786, rows3793]
  all_goals rfl

theorem atot3786 : totK PD2M8K2 D2M8K2.u3786 = [228115287078, 688562196718, 628614344146, 241468611233, 17476474534, 0, 0, 0] := by
  rw [show D2M8K2.u3786 = KTree.node D2M8K2.t3792 (nat_lit 8584788) (nat_lit 3271375076) (nat_lit 0) D2M8K2.t3793 from rfl, totK_node, tot3792, tot3793]
  decide +kernel

theorem arows3787 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3787 = true := by
  rw [show D2M8K2.u3787 = KTree.node D2M8K2.t3794 (nat_lit 8586452) (nat_lit 3216646021) (nat_lit 0) D2M8K2.t3795 from rfl, allE_node, rows3794, irow3787, rows3795]
  all_goals rfl

theorem atot3787 : totK PD2M8K2 D2M8K2.u3787 = [150799174962, 711114160554, 785795027822, 133079095853, 1369150432, 0, 0, 0] := by
  rw [show D2M8K2.u3787 = KTree.node D2M8K2.t3794 (nat_lit 8586452) (nat_lit 3216646021) (nat_lit 0) D2M8K2.t3795 from rfl, totK_node, tot3794, tot3795]
  decide +kernel

theorem arows3789 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3789 = true := by
  rw [show D2M8K2.u3789 = KTree.node D2M8K2.t3796 (nat_lit 8588862) (nat_lit 3226168499) (nat_lit 0) D2M8K2.t3797 from rfl, allE_node, rows3796, irow3789, rows3797]
  all_goals rfl

theorem atot3789 : totK PD2M8K2 D2M8K2.u3789 = [332330514117, 900167235228, 568440141257, 56172042231, 0, 0, 0, 0] := by
  rw [show D2M8K2.u3789 = KTree.node D2M8K2.t3796 (nat_lit 8588862) (nat_lit 3226168499) (nat_lit 0) D2M8K2.t3797 from rfl, totK_node, tot3796, tot3797]
  decide +kernel

theorem arows3790 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3790 = true := by
  rw [show D2M8K2.u3790 = KTree.node D2M8K2.t3798 (nat_lit 8590385) (nat_lit 1640825245) (nat_lit 0) D2M8K2.t3799 from rfl, allE_node, rows3798, irow3790, rows3799]
  all_goals rfl

theorem atot3790 : totK PD2M8K2 D2M8K2.u3790 = [88459214294, 522141297578, 817453971451, 367270473232, 29349649617, 0, 0, 0] := by
  rw [show D2M8K2.u3790 = KTree.node D2M8K2.t3798 (nat_lit 8590385) (nat_lit 1640825245) (nat_lit 0) D2M8K2.t3799 from rfl, totK_node, tot3798, tot3799]
  decide +kernel

theorem arows3793 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3793 = true := by
  rw [show D2M8K2.u3793 = KTree.node D2M8K2.t3800 (nat_lit 8595155) (nat_lit 2858976552) (nat_lit 0) D2M8K2.t3801 from rfl, allE_node, rows3800, irow3793, rows3801]
  all_goals rfl

theorem atot3793 : totK PD2M8K2 D2M8K2.u3793 = [229943834262, 687994678146, 683657049760, 217303233264, 8209296672, 0, 0, 0] := by
  rw [show D2M8K2.u3793 = KTree.node D2M8K2.t3800 (nat_lit 8595155) (nat_lit 2858976552) (nat_lit 0) D2M8K2.t3801 from rfl, totK_node, tot3800, tot3801]
  decide +kernel

theorem arows3794 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3794 = true := by
  rw [show D2M8K2.u3794 = KTree.node D2M8K2.t3802 (nat_lit 8596632) (nat_lit 3571689769) (nat_lit 0) D2M8K2.t3803 from rfl, allE_node, rows3802, irow3794, rows3803]
  all_goals rfl

theorem atot3794 : totK PD2M8K2 D2M8K2.u3794 = [208376287442, 778389707694, 696581261524, 114528783899, 1198073392, 0, 0, 0] := by
  rw [show D2M8K2.u3794 = KTree.node D2M8K2.t3802 (nat_lit 8596632) (nat_lit 3571689769) (nat_lit 0) D2M8K2.t3803 from rfl, totK_node, tot3802, tot3803]
  decide +kernel

theorem arows3796 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3796 = true := by
  rw [show D2M8K2.u3796 = KTree.node D2M8K2.t3804 (nat_lit 8598285) (nat_lit 1177126063) (nat_lit 0) D2M8K2.t3805 from rfl, allE_node, rows3804, irow3796, rows3805]
  all_goals rfl

theorem atot3796 : totK PD2M8K2 D2M8K2.u3796 = [152574673325, 637995591303, 774807180801, 231546296060, 12052611869, 0, 0, 0] := by
  rw [show D2M8K2.u3796 = KTree.node D2M8K2.t3804 (nat_lit 8598285) (nat_lit 1177126063) (nat_lit 0) D2M8K2.t3805 from rfl, totK_node, tot3804, tot3805]
  decide +kernel

theorem arows3797 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3797 = true := by
  rw [show D2M8K2.u3797 = KTree.node D2M8K2.t3806 (nat_lit 8600267) (nat_lit 2735669354) (nat_lit 0) D2M8K2.t3807 from rfl, allE_node, rows3806, irow3797, rows3807]
  all_goals rfl

theorem atot3797 : totK PD2M8K2 D2M8K2.u3797 = [174773797690, 755490843797, 760889554035, 118258392811, 1096505104, 0, 0, 0] := by
  rw [show D2M8K2.u3797 = KTree.node D2M8K2.t3806 (nat_lit 8600267) (nat_lit 2735669354) (nat_lit 0) D2M8K2.t3807 from rfl, totK_node, tot3806, tot3807]
  decide +kernel

theorem arows3802 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3802 = true := by
  rw [show D2M8K2.u3802 = KTree.node D2M8K2.t3808 (nat_lit 8602457) (nat_lit 1682430146) (nat_lit 0) D2M8K2.t3809 from rfl, allE_node, rows3808, irow3802, rows3809]
  all_goals rfl

theorem atot3802 : totK PD2M8K2 D2M8K2.u3802 = [333489663746, 842830669211, 526102857896, 104457540129, 3884009855, 0, 0, 0] := by
  rw [show D2M8K2.u3802 = KTree.node D2M8K2.t3808 (nat_lit 8602457) (nat_lit 1682430146) (nat_lit 0) D2M8K2.t3809 from rfl, totK_node, tot3808, tot3809]
  decide +kernel

theorem arows3803 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3803 = true := by
  rw [show D2M8K2.u3803 = KTree.node D2M8K2.t3810 (nat_lit 8603952) (nat_lit 3425049145) (nat_lit 0) D2M8K2.t3811 from rfl, allE_node, rows3810, irow3803, rows3811]
  all_goals rfl

theorem atot3803 : totK PD2M8K2 D2M8K2.u3803 = [92934196222, 603464635654, 865796176603, 225505024945, 4965269624, 0, 0, 0] := by
  rw [show D2M8K2.u3803 = KTree.node D2M8K2.t3810 (nat_lit 8603952) (nat_lit 3425049145) (nat_lit 0) D2M8K2.t3811 from rfl, totK_node, tot3810, tot3811]
  decide +kernel

theorem arows3805 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3805 = true := by
  rw [show D2M8K2.u3805 = KTree.node D2M8K2.t3812 (nat_lit 8605600) (nat_lit 2794095531) (nat_lit 0) D2M8K2.t3813 from rfl, allE_node, rows3812, irow3805, rows3813]
  all_goals rfl

theorem atot3805 : totK PD2M8K2 D2M8K2.u3805 = [0, 359344303089, 934030758227, 451184086193, 28160378321, 0, 0, 0] := by
  rw [show D2M8K2.u3805 = KTree.node D2M8K2.t3812 (nat_lit 8605600) (nat_lit 2794095531) (nat_lit 0) D2M8K2.t3813 from rfl, totK_node, tot3812, tot3813]
  decide +kernel

theorem arows3806 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3806 = true := by
  rw [show D2M8K2.u3806 = KTree.node D2M8K2.t3814 (nat_lit 8607317) (nat_lit 1273619523) (nat_lit 0) D2M8K2.t3815 from rfl, allE_node, rows3814, irow3806, rows3815]
  all_goals rfl

theorem atot3806 : totK PD2M8K2 D2M8K2.u3806 = [0, 129320581223, 734546421417, 779729647217, 110002835027, 1239866073, 0, 0] := by
  rw [show D2M8K2.u3806 = KTree.node D2M8K2.t3814 (nat_lit 8607317) (nat_lit 1273619523) (nat_lit 0) D2M8K2.t3815 from rfl, totK_node, tot3814, tot3815]
  decide +kernel

theorem arows3809 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3809 = true := by
  rw [show D2M8K2.u3809 = KTree.node D2M8K2.t3816 (nat_lit 8609845) (nat_lit 1214151962) (nat_lit 0) D2M8K2.t3817 from rfl, allE_node, rows3816, irow3809, rows3817]
  all_goals rfl

theorem atot3809 : totK PD2M8K2 D2M8K2.u3809 = [0, 397843696008, 944867519408, 469024394632, 37245743060, 0, 0, 0] := by
  rw [show D2M8K2.u3809 = KTree.node D2M8K2.t3816 (nat_lit 8609845) (nat_lit 1214151962) (nat_lit 0) D2M8K2.t3817 from rfl, totK_node, tot3816, tot3817]
  decide +kernel

theorem arows3810 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3810 = true := by
  rw [show D2M8K2.u3810 = KTree.node D2M8K2.t3818 (nat_lit 8616280) (nat_lit 3420177357) (nat_lit 0) D2M8K2.t3819 from rfl, allE_node, rows3818, irow3810, rows3819]
  all_goals rfl

theorem atot3810 : totK PD2M8K2 D2M8K2.u3810 = [0, 348068502358, 917324342398, 501748946212, 40091399552, 0, 0, 0] := by
  rw [show D2M8K2.u3810 = KTree.node D2M8K2.t3818 (nat_lit 8616280) (nat_lit 3420177357) (nat_lit 0) D2M8K2.t3819 from rfl, totK_node, tot3818, tot3819]
  decide +kernel

theorem arows3812 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3812 = true := by
  rw [show D2M8K2.u3812 = KTree.node D2M8K2.t3820 (nat_lit 8617755) (nat_lit 1589181965) (nat_lit 0) D2M8K2.t3821 from rfl, allE_node, rows3820, irow3812, rows3821]
  all_goals rfl

theorem atot3812 : totK PD2M8K2 D2M8K2.u3812 = [0, 88698579362, 615096804763, 824695545159, 213338239196, 9633262574, 0, 0] := by
  rw [show D2M8K2.u3812 = KTree.node D2M8K2.t3820 (nat_lit 8617755) (nat_lit 1589181965) (nat_lit 0) D2M8K2.t3821 from rfl, totK_node, tot3820, tot3821]
  decide +kernel

theorem arows3813 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3813 = true := by
  rw [show D2M8K2.u3813 = KTree.node D2M8K2.t3822 (nat_lit 8619660) (nat_lit 2601742237) (nat_lit 0) D2M8K2.t3823 from rfl, allE_node, rows3822, irow3813, rows3823]
  all_goals rfl

theorem atot3813 : totK PD2M8K2 D2M8K2.u3813 = [0, 322483683499, 832393827663, 548595524984, 94085631580, 3472187823, 0, 0] := by
  rw [show D2M8K2.u3813 = KTree.node D2M8K2.t3822 (nat_lit 8619660) (nat_lit 2601742237) (nat_lit 0) D2M8K2.t3823 from rfl, totK_node, tot3822, tot3823]
  decide +kernel

theorem arows3817 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3817 = true := by
  rw [show D2M8K2.u3817 = KTree.node D2M8K2.t3824 (nat_lit 8622145) (nat_lit 1531312075) (nat_lit 0) D2M8K2.t3825 from rfl, allE_node, rows3824, irow3817, rows3825]
  all_goals rfl

theorem atot3817 : totK PD2M8K2 D2M8K2.u3817 = [0, 130657817851, 697534530114, 752044001032, 149028704737, 4720618446, 0, 0] := by
  rw [show D2M8K2.u3817 = KTree.node D2M8K2.t3824 (nat_lit 8622145) (nat_lit 1531312075) (nat_lit 0) D2M8K2.t3825 from rfl, totK_node, tot3824, tot3825]
  decide +kernel

theorem arows3818 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3818 = true := by
  rw [show D2M8K2.u3818 = KTree.node D2M8K2.t3826 (nat_lit 8623704) (nat_lit 3543820183) (nat_lit 0) D2M8K2.t3827 from rfl, allE_node, rows3826, irow3818, rows3827]
  all_goals rfl

theorem atot3818 : totK PD2M8K2 D2M8K2.u3818 = [70593750018, 387904209609, 822645836415, 496755174528, 45453807457, 0, 0, 0] := by
  rw [show D2M8K2.u3818 = KTree.node D2M8K2.t3826 (nat_lit 8623704) (nat_lit 3543820183) (nat_lit 0) D2M8K2.t3827 from rfl, totK_node, tot3826, tot3827]
  decide +kernel

theorem arows3820 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3820 = true := by
  rw [show D2M8K2.u3820 = KTree.node D2M8K2.t3828 (nat_lit 8668657) (nat_lit 1534913353) (nat_lit 0) D2M8K2.t3829 from rfl, allE_node, rows3828, irow3820, rows3829]
  all_goals rfl

theorem atot3820 : totK PD2M8K2 D2M8K2.u3820 = [328073724573, 926230270882, 495789532143, 32935246935, 0, 0, 0, 0] := by
  rw [show D2M8K2.u3820 = KTree.node D2M8K2.t3828 (nat_lit 8668657) (nat_lit 1534913353) (nat_lit 0) D2M8K2.t3829 from rfl, totK_node, tot3828, tot3829]
  decide +kernel

theorem arows3821 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3821 = true := by
  rw [show D2M8K2.u3821 = KTree.node D2M8K2.t3830 (nat_lit 8670576) (nat_lit 3527819012) (nat_lit 0) D2M8K2.t3831 from rfl, allE_node, rows3830, irow3821, rows3831]
  all_goals rfl

theorem atot3821 : totK PD2M8K2 D2M8K2.u3821 = [122528881355, 662331043411, 866200025153, 159356345015, 1369150432, 0, 0, 0] := by
  rw [show D2M8K2.u3821 = KTree.node D2M8K2.t3830 (nat_lit 8670576) (nat_lit 3527819012) (nat_lit 0) D2M8K2.t3831 from rfl, totK_node, tot3830, tot3831]
  decide +kernel

theorem arows3824 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3824 = true := by
  rw [show D2M8K2.u3824 = KTree.node D2M8K2.t3832 (nat_lit 8672320) (nat_lit 3720816941) (nat_lit 0) D2M8K2.t3833 from rfl, allE_node, rows3832, irow3824, rows3833]
  all_goals rfl

theorem atot3824 : totK PD2M8K2 D2M8K2.u3824 = [301058012645, 915211813902, 568858782132, 53191044959, 0, 0, 0, 0] := by
  rw [show D2M8K2.u3824 = KTree.node D2M8K2.t3832 (nat_lit 8672320) (nat_lit 3720816941) (nat_lit 0) D2M8K2.t3833 from rfl, totK_node, tot3832, tot3833]
  decide +kernel

theorem arows3825 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3825 = true := by
  rw [show D2M8K2.u3825 = KTree.node D2M8K2.t3834 (nat_lit 8673820) (nat_lit 3204345059) (nat_lit 0) D2M8K2.t3835 from rfl, allE_node, rows3834, irow3825, rows3835]
  all_goals rfl

theorem atot3825 : totK PD2M8K2 D2M8K2.u3825 = [0, 341137534348, 937009020737, 497011100634, 33085089180, 0, 0, 0] := by
  rw [show D2M8K2.u3825 = KTree.node D2M8K2.t3834 (nat_lit 8673820) (nat_lit 3204345059) (nat_lit 0) D2M8K2.t3835 from rfl, totK_node, tot3834, tot3835]
  decide +kernel

theorem arows3827 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3827 = true := by
  rw [show D2M8K2.u3827 = KTree.node D2M8K2.t3836 (nat_lit 8675123) (nat_lit 2944421794) (nat_lit 0) D2M8K2.t3837 from rfl, allE_node, rows3836, irow3827, rows3837]
  all_goals rfl

theorem atot3827 : totK PD2M8K2 D2M8K2.u3827 = [365766079577, 896938048722, 467244984060, 62842414999, 4431529051, 0, 0, 0] := by
  rw [show D2M8K2.u3827 = KTree.node D2M8K2.t3836 (nat_lit 8675123) (nat_lit 2944421794) (nat_lit 0) D2M8K2.t3837 from rfl, totK_node, tot3836, tot3837]
  decide +kernel

theorem arows3828 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3828 = true := by
  rw [show D2M8K2.u3828 = KTree.node D2M8K2.t3838 (nat_lit 8676680) (nat_lit 3607752652) (nat_lit 0) D2M8K2.t3839 from rfl, allE_node, rows3838, irow3828, rows3839]
  all_goals rfl

theorem atot3828 : totK PD2M8K2 D2M8K2.u3828 = [53428324476, 536721820801, 898133890783, 270307526404, 12916357485, 0, 0, 0] := by
  rw [show D2M8K2.u3828 = KTree.node D2M8K2.t3838 (nat_lit 8676680) (nat_lit 3607752652) (nat_lit 0) D2M8K2.t3839 from rfl, totK_node, tot3838, tot3839]
  decide +kernel

theorem arows3836 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3836 = true := by
  rw [show D2M8K2.u3836 = KTree.node D2M8K2.t3840 (nat_lit 8678517) (nat_lit 901381665) (nat_lit 0) D2M8K2.t3841 from rfl, allE_node, rows3840, irow3836, rows3841]
  all_goals rfl

theorem atot3836 : totK PD2M8K2 D2M8K2.u3836 = [329509998253, 894601381069, 532581412709, 55896439964, 0, 0, 0, 0] := by
  rw [show D2M8K2.u3836 = KTree.node D2M8K2.t3840 (nat_lit 8678517) (nat_lit 901381665) (nat_lit 0) D2M8K2.t3841 from rfl, totK_node, tot3840, tot3841]
  decide +kernel

theorem arows3837 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3837 = true := by
  rw [show D2M8K2.u3837 = KTree.node D2M8K2.t3842 (nat_lit 8680074) (nat_lit 3885565253) (nat_lit 0) D2M8K2.t3843 from rfl, allE_node, rows3842, irow3837, rows3843]
  all_goals rfl

theorem atot3837 : totK PD2M8K2 D2M8K2.u3837 = [89913192444, 566699360834, 859824388487, 252217411583, 10663791286, 0, 0, 0] := by
  rw [show D2M8K2.u3837 = KTree.node D2M8K2.t3842 (nat_lit 8680074) (nat_lit 3885565253) (nat_lit 0) D2M8K2.t3843 from rfl, totK_node, tot3842, tot3843]
  decide +kernel

theorem arows3839 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3839 = true := by
  rw [show D2M8K2.u3839 = KTree.node D2M8K2.t3844 (nat_lit 8685338) (nat_lit 4133817830) (nat_lit 0) D2M8K2.t3845 from rfl, allE_node, rows3844, irow3839, rows3845]
  all_goals rfl

theorem atot3839 : totK PD2M8K2 D2M8K2.u3839 = [334715602835, 868840811571, 554118007241, 84860155314, 2428283778, 0, 0, 0] := by
  rw [show D2M8K2.u3839 = KTree.node D2M8K2.t3844 (nat_lit 8685338) (nat_lit 4133817830) (nat_lit 0) D2M8K2.t3845 from rfl, totK_node, tot3844, tot3845]
  decide +kernel

theorem arows3840 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3840 = true := by
  rw [show D2M8K2.u3840 = KTree.node D2M8K2.t3846 (nat_lit 8686768) (nat_lit 3053583919) (nat_lit 0) D2M8K2.t3847 from rfl, allE_node, rows3846, irow3840, rows3847]
  all_goals rfl

theorem atot3840 : totK PD2M8K2 D2M8K2.u3840 = [112931552984, 645934626649, 836583621065, 208370448190, 4967996017, 0, 0, 0] := by
  rw [show D2M8K2.u3840 = KTree.node D2M8K2.t3846 (nat_lit 8686768) (nat_lit 3053583919) (nat_lit 0) D2M8K2.t3847 from rfl, totK_node, tot3846, tot3847]
  decide +kernel

theorem arows3843 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3843 = true := by
  rw [show D2M8K2.u3843 = KTree.node D2M8K2.t3848 (nat_lit 8688437) (nat_lit 2379771252) (nat_lit 0) D2M8K2.t3849 from rfl, allE_node, rows3848, irow3843, rows3849]
  all_goals rfl

theorem atot3843 : totK PD2M8K2 D2M8K2.u3843 = [0, 392312515424, 959399758552, 416958716014, 22416853141, 0, 0, 0] := by
  rw [show D2M8K2.u3843 = KTree.node D2M8K2.t3848 (nat_lit 8688437) (nat_lit 2379771252) (nat_lit 0) D2M8K2.t3849 from rfl, totK_node, tot3848, tot3849]
  decide +kernel

theorem arows3844 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3844 = true := by
  rw [show D2M8K2.u3844 = KTree.node D2M8K2.t3850 (nat_lit 8690051) (nat_lit 2886047953) (nat_lit 0) D2M8K2.t3851 from rfl, allE_node, rows3850, irow3844, rows3851]
  all_goals rfl

theorem atot3844 : totK PD2M8K2 D2M8K2.u3844 = [0, 168081169584, 740127750828, 730239535495, 100263725843, 1310285577, 0, 0] := by
  rw [show D2M8K2.u3844 = KTree.node D2M8K2.t3850 (nat_lit 8690051) (nat_lit 2886047953) (nat_lit 0) D2M8K2.t3851 from rfl, totK_node, tot3850, tot3851]
  decide +kernel

theorem arows3846 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3846 = true := by
  rw [show D2M8K2.u3846 = KTree.node D2M8K2.t3852 (nat_lit 8692427) (nat_lit 2842707927) (nat_lit 0) D2M8K2.t3853 from rfl, allE_node, rows3852, irow3846, rows3853]
  all_goals rfl

theorem atot3846 : totK PD2M8K2 D2M8K2.u3846 = [0, 288439493940, 853206869486, 621179627716, 59435197698, 0, 0, 0] := by
  rw [show D2M8K2.u3846 = KTree.node D2M8K2.t3852 (nat_lit 8692427) (nat_lit 2842707927) (nat_lit 0) D2M8K2.t3853 from rfl, totK_node, tot3852, tot3853]
  decide +kernel

theorem arows3847 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3847 = true := by
  rw [show D2M8K2.u3847 = KTree.node D2M8K2.t3854 (nat_lit 8695420) (nat_lit 3854718101) (nat_lit 0) D2M8K2.t3855 from rfl, allE_node, rows3854, irow3847, rows3855]
  all_goals rfl

theorem atot3847 : totK PD2M8K2 D2M8K2.u3847 = [0, 395472892380, 939771435708, 457540904531, 35701138369, 0, 0, 0] := by
  rw [show D2M8K2.u3847 = KTree.node D2M8K2.t3854 (nat_lit 8695420) (nat_lit 3854718101) (nat_lit 0) D2M8K2.t3855 from rfl, totK_node, tot3854, tot3855]
  decide +kernel

theorem arows3851 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3851 = true := by
  rw [show D2M8K2.u3851 = KTree.node D2M8K2.t3856 (nat_lit 8696944) (nat_lit 3512545649) (nat_lit 0) D2M8K2.t3857 from rfl, allE_node, rows3856, irow3851, rows3857]
  all_goals rfl

theorem atot3851 : totK PD2M8K2 D2M8K2.u3851 = [0, 155009944178, 754654306316, 747910706060, 107901998771, 1075657031, 0, 0] := by
  rw [show D2M8K2.u3851 = KTree.node D2M8K2.t3856 (nat_lit 8696944) (nat_lit 3512545649) (nat_lit 0) D2M8K2.t3857 from rfl, totK_node, tot3856, tot3857]
  decide +kernel

theorem arows3852 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3852 = true := by
  rw [show D2M8K2.u3852 = KTree.node D2M8K2.t3858 (nat_lit 8699016) (nat_lit 3574499845) (nat_lit 0) D2M8K2.t3859 from rfl, allE_node, rows3858, irow3852, rows3859]
  all_goals rfl

theorem atot3852 : totK PD2M8K2 D2M8K2.u3852 = [0, 262320543727, 793486831529, 606504815090, 110805252734, 3804183361, 0, 0] := by
  rw [show D2M8K2.u3852 = KTree.node D2M8K2.t3858 (nat_lit 8699016) (nat_lit 3574499845) (nat_lit 0) D2M8K2.t3859 from rfl, totK_node, tot3858, tot3859]
  decide +kernel

theorem arows3854 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3854 = true := by
  rw [show D2M8K2.u3854 = KTree.node D2M8K2.t3860 (nat_lit 8700538) (nat_lit 3732324220) (nat_lit 0) D2M8K2.t3861 from rfl, allE_node, rows3860, irow3854, rows3861]
  all_goals rfl

theorem atot3854 : totK PD2M8K2 D2M8K2.u3854 = [0, 155109350687, 677922261907, 750303222801, 162807794866, 4931404646, 0, 0] := by
  rw [show D2M8K2.u3854 = KTree.node D2M8K2.t3860 (nat_lit 8700538) (nat_lit 3732324220) (nat_lit 0) D2M8K2.t3861 from rfl, totK_node, tot3860, tot3861]
  decide +kernel

theorem arows3855 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3855 = true := by
  rw [show D2M8K2.u3855 = KTree.node D2M8K2.t3862 (nat_lit 8706045) (nat_lit 1345646580) (nat_lit 0) D2M8K2.t3863 from rfl, allE_node, rows3862, irow3855, rows3863]
  all_goals rfl

theorem atot3855 : totK PD2M8K2 D2M8K2.u3855 = [0, 319079121343, 894419994924, 553061336945, 51102092558, 0, 0, 0] := by
  rw [show D2M8K2.u3855 = KTree.node D2M8K2.t3862 (nat_lit 8706045) (nat_lit 1345646580) (nat_lit 0) D2M8K2.t3863 from rfl, totK_node, tot3862, tot3863]
  decide +kernel

theorem arows3858 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3858 = true := by
  rw [show D2M8K2.u3858 = KTree.node D2M8K2.t3864 (nat_lit 8707486) (nat_lit 3757582209) (nat_lit 0) D2M8K2.t3865 from rfl, allE_node, rows3864, irow3858, rows3865]
  all_goals rfl

theorem atot3858 : totK PD2M8K2 D2M8K2.u3858 = [0, 126419686420, 667653469970, 801438756953, 182342542488, 4811815119, 0, 0] := by
  rw [show D2M8K2.u3858 = KTree.node D2M8K2.t3864 (nat_lit 8707486) (nat_lit 3757582209) (nat_lit 0) D2M8K2.t3865 from rfl, totK_node, tot3864, tot3865]
  decide +kernel

theorem arows3859 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3859 = true := by
  rw [show D2M8K2.u3859 = KTree.node D2M8K2.t3866 (nat_lit 8709190) (nat_lit 3743199737) (nat_lit 0) D2M8K2.t3867 from rfl, allE_node, rows3866, irow3859, rows3867]
  all_goals rfl

theorem atot3859 : totK PD2M8K2 D2M8K2.u3859 = [0, 236367948574, 688513191438, 616804128358, 216285520823, 16939352947, 0, 0] := by
  rw [show D2M8K2.u3859 = KTree.node D2M8K2.t3866 (nat_lit 8709190) (nat_lit 3743199737) (nat_lit 0) D2M8K2.t3867 from rfl, totK_node, tot3866, tot3867]
  decide +kernel

theorem arows3861 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3861 = true := by
  rw [show D2M8K2.u3861 = KTree.node D2M8K2.t3868 (nat_lit 8710722) (nat_lit 3015955748) (nat_lit 0) D2M8K2.t3869 from rfl, allE_node, rows3868, irow3861, rows3869]
  all_goals rfl

theorem atot3861 : totK PD2M8K2 D2M8K2.u3861 = [0, 185751082966, 757414505840, 728697180264, 118989865469, 1369150432, 0, 0] := by
  rw [show D2M8K2.u3861 = KTree.node D2M8K2.t3868 (nat_lit 8710722) (nat_lit 3015955748) (nat_lit 0) D2M8K2.t3869 from rfl, totK_node, tot3868, tot3869]
  decide +kernel

theorem arows3862 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3862 = true := by
  rw [show D2M8K2.u3862 = KTree.node D2M8K2.t3870 (nat_lit 8716274) (nat_lit 2280405639) (nat_lit 0) D2M8K2.t3871 from rfl, allE_node, rows3870, irow3862, rows3871]
  all_goals rfl

theorem atot3862 : totK PD2M8K2 D2M8K2.u3862 = [0, 253279702540, 824701405689, 649485159047, 73343676613, 0, 0, 0] := by
  rw [show D2M8K2.u3862 = KTree.node D2M8K2.t3870 (nat_lit 8716274) (nat_lit 2280405639) (nat_lit 0) D2M8K2.t3871 from rfl, totK_node, tot3870, tot3871]
  decide +kernel

theorem arows3867 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3867 = true := by
  rw [show D2M8K2.u3867 = KTree.node D2M8K2.t3872 (nat_lit 8717850) (nat_lit 3346041471) (nat_lit 0) D2M8K2.t3873 from rfl, allE_node, rows3872, irow3867, rows3873]
  all_goals rfl

theorem atot3867 : totK PD2M8K2 D2M8K2.u3867 = [0, 147791837144, 660225884431, 782793483706, 185070141564, 5172807878, 0, 0] := by
  rw [show D2M8K2.u3867 = KTree.node D2M8K2.t3872 (nat_lit 8717850) (nat_lit 3346041471) (nat_lit 0) D2M8K2.t3873 from rfl, totK_node, tot3872, tot3873]
  decide +kernel

theorem arows3868 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3868 = true := by
  rw [show D2M8K2.u3868 = KTree.node D2M8K2.t3874 (nat_lit 8719892) (nat_lit 3415383461) (nat_lit 0) D2M8K2.t3875 from rfl, allE_node, rows3874, irow3868, rows3875]
  all_goals rfl

theorem atot3868 : totK PD2M8K2 D2M8K2.u3868 = [0, 313511907324, 869424296271, 562326525589, 62022714472, 0, 0, 0] := by
  rw [show D2M8K2.u3868 = KTree.node D2M8K2.t3874 (nat_lit 8719892) (nat_lit 3415383461) (nat_lit 0) D2M8K2.t3875 from rfl, totK_node, tot3874, tot3875]
  decide +kernel

theorem arows3870 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3870 = true := by
  rw [show D2M8K2.u3870 = KTree.node D2M8K2.t3876 (nat_lit 8721441) (nat_lit 1606784923) (nat_lit 0) D2M8K2.t3877 from rfl, allE_node, rows3876, irow3870, rows3877]
  all_goals rfl

theorem atot3870 : totK PD2M8K2 D2M8K2.u3870 = [0, 87804909821, 614998918971, 870265319213, 203730804823, 5228939780, 0, 0] := by
  rw [show D2M8K2.u3870 = KTree.node D2M8K2.t3876 (nat_lit 8721441) (nat_lit 1606784923) (nat_lit 0) D2M8K2.t3877 from rfl, totK_node, tot3876, tot3877]
  decide +kernel

theorem arows3871 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3871 = true := by
  rw [show D2M8K2.u3871 = KTree.node D2M8K2.t3878 (nat_lit 8726905) (nat_lit 1172543914) (nat_lit 0) D2M8K2.t3879 from rfl, allE_node, rows3878, irow3871, rows3879]
  all_goals rfl

theorem atot3871 : totK PD2M8K2 D2M8K2.u3871 = [0, 333752773292, 889429704890, 528966804327, 55060761797, 0, 0, 0] := by
  rw [show D2M8K2.u3871 = KTree.node D2M8K2.t3878 (nat_lit 8726905) (nat_lit 1172543914) (nat_lit 0) D2M8K2.t3879 from rfl, totK_node, tot3878, tot3879]
  decide +kernel

theorem arows3874 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3874 = true := by
  rw [show D2M8K2.u3874 = KTree.node D2M8K2.t3880 (nat_lit 8728397) (nat_lit 1762557174) (nat_lit 0) D2M8K2.t3881 from rfl, allE_node, rows3880, irow3874, rows3881]
  all_goals rfl

theorem atot3874 : totK PD2M8K2 D2M8K2.u3874 = [0, 92937627352, 595277979642, 867302836366, 223569090695, 5948204717, 0, 0] := by
  rw [show D2M8K2.u3874 = KTree.node D2M8K2.t3880 (nat_lit 8728397) (nat_lit 1762557174) (nat_lit 0) D2M8K2.t3881 from rfl, totK_node, tot3880, tot3881]
  decide +kernel

theorem arows3875 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3875 = true := by
  rw [show D2M8K2.u3875 = KTree.node D2M8K2.t3882 (nat_lit 8730052) (nat_lit 3912776888) (nat_lit 0) D2M8K2.t3883 from rfl, allE_node, rows3882, irow3875, rows3883]
  all_goals rfl

theorem atot3875 : totK PD2M8K2 D2M8K2.u3875 = [0, 0, 353889796980, 940083635910, 433647165646, 25336677746, 0, 0] := by
  rw [show D2M8K2.u3875 = KTree.node D2M8K2.t3882 (nat_lit 8730052) (nat_lit 3912776888) (nat_lit 0) D2M8K2.t3883 from rfl, totK_node, tot3882, tot3883]
  decide +kernel

theorem arows3877 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3877 = true := by
  rw [show D2M8K2.u3877 = KTree.node D2M8K2.t3884 (nat_lit 8731657) (nat_lit 1519732958) (nat_lit 0) D2M8K2.t3885 from rfl, allE_node, rows3884, irow3877, rows3885]
  all_goals rfl

theorem atot3877 : totK PD2M8K2 D2M8K2.u3877 = [0, 0, 158923014580, 744541111614, 702142600326, 103021625308, 1369150432, 0] := by
  rw [show D2M8K2.u3877 = KTree.node D2M8K2.t3884 (nat_lit 8731657) (nat_lit 1519732958) (nat_lit 0) D2M8K2.t3885 from rfl, totK_node, tot3884, tot3885]
  decide +kernel

theorem arows3878 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3878 = true := by
  rw [show D2M8K2.u3878 = KTree.node D2M8K2.t3886 (nat_lit 8737327) (nat_lit 1586107810) (nat_lit 0) D2M8K2.t3887 from rfl, allE_node, rows3886, irow3878, rows3887]
  all_goals rfl

theorem atot3878 : totK PD2M8K2 D2M8K2.u3878 = [0, 0, 369971761877, 949973650204, 423647328436, 21633615698, 0, 0] := by
  rw [show D2M8K2.u3878 = KTree.node D2M8K2.t3886 (nat_lit 8737327) (nat_lit 1586107810) (nat_lit 0) D2M8K2.t3887 from rfl, totK_node, tot3886, tot3887]
  decide +kernel

theorem arows3882 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3882 = true := by
  rw [show D2M8K2.u3882 = KTree.node D2M8K2.t3888 (nat_lit 8740731) (nat_lit 2684566571) (nat_lit 0) D2M8K2.t3889 from rfl, allE_node, rows3888, irow3882, rows3889]
  all_goals rfl

theorem atot3882 : totK PD2M8K2 D2M8K2.u3882 = [0, 0, 378693853762, 974843758726, 409789516763, 16674219220, 0, 0] := by
  rw [show D2M8K2.u3882 = KTree.node D2M8K2.t3888 (nat_lit 8740731) (nat_lit 2684566571) (nat_lit 0) D2M8K2.t3889 from rfl, totK_node, tot3888, tot3889]
  decide +kernel

theorem arows3883 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3883 = true := by
  rw [show D2M8K2.u3883 = KTree.node D2M8K2.t3890 (nat_lit 8747518) (nat_lit 3863403631) (nat_lit 0) D2M8K2.t3891 from rfl, allE_node, rows3890, irow3883, rows3891]
  all_goals rfl

theorem atot3883 : totK PD2M8K2 D2M8K2.u3883 = [0, 0, 385437899696, 948930684373, 417559944924, 20949309390, 0, 0] := by
  rw [show D2M8K2.u3883 = KTree.node D2M8K2.t3890 (nat_lit 8747518) (nat_lit 3863403631) (nat_lit 0) D2M8K2.t3891 from rfl, totK_node, tot3890, tot3891]
  decide +kernel

theorem arows3885 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3885 = true := by
  rw [show D2M8K2.u3885 = KTree.node D2M8K2.t3892 (nat_lit 8754512) (nat_lit 3725915661) (nat_lit 0) D2M8K2.t3893 from rfl, allE_node, rows3892, irow3885, rows3893]
  all_goals rfl

theorem atot3885 : totK PD2M8K2 D2M8K2.u3885 = [0, 270969029763, 698176948551, 618595216758, 235562150832, 17376665387, 0, 0] := by
  rw [show D2M8K2.u3885 = KTree.node D2M8K2.t3892 (nat_lit 8754512) (nat_lit 3725915661) (nat_lit 0) D2M8K2.t3893 from rfl, totK_node, tot3892, tot3893]
  decide +kernel

theorem arows3886 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3886 = true := by
  rw [show D2M8K2.u3886 = KTree.node D2M8K2.t3894 (nat_lit 8755681) (nat_lit 1331309861) (nat_lit 0) D2M8K2.t3895 from rfl, allE_node, rows3894, irow3886, rows3895]
  all_goals rfl

theorem atot3886 : totK PD2M8K2 D2M8K2.u3886 = [0, 174341421047, 719799590569, 705148243487, 214999105992, 21400436502, 0, 0] := by
  rw [show D2M8K2.u3886 = KTree.node D2M8K2.t3894 (nat_lit 8755681) (nat_lit 1331309861) (nat_lit 0) D2M8K2.t3895 from rfl, totK_node, tot3894, tot3895]
  decide +kernel

theorem arows3889 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3889 = true := by
  rw [show D2M8K2.u3889 = KTree.node D2M8K2.t3896 (nat_lit 8757168) (nat_lit 2940590812) (nat_lit 0) D2M8K2.t3897 from rfl, allE_node, rows3896, irow3889, rows3897]
  all_goals rfl

theorem atot3889 : totK PD2M8K2 D2M8K2.u3889 = [0, 112537107697, 494758105881, 815181039047, 362164663295, 16100220446, 0, 0] := by
  rw [show D2M8K2.u3889 = KTree.node D2M8K2.t3896 (nat_lit 8757168) (nat_lit 2940590812) (nat_lit 0) D2M8K2.t3897 from rfl, totK_node, tot3896, tot3897]
  decide +kernel

theorem arows3890 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3890 = true := by
  rw [show D2M8K2.u3890 = KTree.node D2M8K2.t3898 (nat_lit 8758699) (nat_lit 1711622125) (nat_lit 0) D2M8K2.t3899 from rfl, allE_node, rows3898, irow3890, rows3899]
  all_goals rfl

theorem atot3890 : totK PD2M8K2 D2M8K2.u3890 = [0, 302418411274, 889864529994, 569450896411, 55491482493, 0, 0, 0] := by
  rw [show D2M8K2.u3890 = KTree.node D2M8K2.t3898 (nat_lit 8758699) (nat_lit 1711622125) (nat_lit 0) D2M8K2.t3899 from rfl, totK_node, tot3898, tot3899]
  decide +kernel

theorem arows3892 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3892 = true := by
  rw [show D2M8K2.u3892 = KTree.node D2M8K2.t3900 (nat_lit 8760428) (nat_lit 3762351485) (nat_lit 0) D2M8K2.t3901 from rfl, allE_node, rows3900, irow3892, rows3901]
  all_goals rfl

theorem atot3892 : totK PD2M8K2 D2M8K2.u3892 = [0, 101251914141, 565033798741, 858771214613, 259043627775, 9067749566, 0, 0] := by
  rw [show D2M8K2.u3892 = KTree.node D2M8K2.t3900 (nat_lit 8760428) (nat_lit 3762351485) (nat_lit 0) D2M8K2.t3901 from rfl, totK_node, tot3900, tot3901]
  decide +kernel

theorem arows3893 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3893 = true := by
  rw [show D2M8K2.u3893 = KTree.node D2M8K2.t3902 (nat_lit 8762142) (nat_lit 3879699817) (nat_lit 0) D2M8K2.t3903 from rfl, allE_node, rows3902, irow3893, rows3903]
  all_goals rfl

theorem atot3893 : totK PD2M8K2 D2M8K2.u3893 = [0, 313953739193, 895170596536, 560341583421, 54068963204, 0, 0, 0] := by
  rw [show D2M8K2.u3893 = KTree.node D2M8K2.t3902 (nat_lit 8762142) (nat_lit 3879699817) (nat_lit 0) D2M8K2.t3903 from rfl, totK_node, tot3902, tot3903]
  decide +kernel

theorem arows3899 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3899 = true := by
  rw [show D2M8K2.u3899 = KTree.node D2M8K2.t3904 (nat_lit 8763867) (nat_lit 3745891234) (nat_lit 0) D2M8K2.t3905 from rfl, allE_node, rows3904, irow3899, rows3905]
  all_goals rfl

theorem atot3899 : totK PD2M8K2 D2M8K2.u3899 = [0, 90182705397, 547595547613, 884493542013, 282024648500, 9178989717, 0, 0] := by
  rw [show D2M8K2.u3899 = KTree.node D2M8K2.t3904 (nat_lit 8763867) (nat_lit 3745891234) (nat_lit 0) D2M8K2.t3905 from rfl, totK_node, tot3904, tot3905]
  decide +kernel

theorem arows3900 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3900 = true := by
  rw [show D2M8K2.u3900 = KTree.node D2M8K2.t3906 (nat_lit 8765532) (nat_lit 2258300413) (nat_lit 0) D2M8K2.t3907 from rfl, allE_node, rows3906, irow3900, rows3907]
  all_goals rfl

theorem atot3900 : totK PD2M8K2 D2M8K2.u3900 = [0, 255210323020, 871772077992, 643247343129, 67262068098, 0, 0, 0] := by
  rw [show D2M8K2.u3900 = KTree.node D2M8K2.t3906 (nat_lit 8765532) (nat_lit 2258300413) (nat_lit 0) D2M8K2.t3907 from rfl, totK_node, tot3906, tot3907]
  decide +kernel

theorem arows3902 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3902 = true := by
  rw [show D2M8K2.u3902 = KTree.node D2M8K2.t3908 (nat_lit 8768099) (nat_lit 2364030877) (nat_lit 0) D2M8K2.t3909 from rfl, allE_node, rows3908, irow3902, rows3909]
  all_goals rfl

theorem atot3902 : totK PD2M8K2 D2M8K2.u3902 = [0, 248898460525, 783991302243, 672489323349, 121151192991, 1429815836, 0, 0] := by
  rw [show D2M8K2.u3902 = KTree.node D2M8K2.t3908 (nat_lit 8768099) (nat_lit 2364030877) (nat_lit 0) D2M8K2.t3909 from rfl, totK_node, tot3908, tot3909]
  decide +kernel

theorem arows3903 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3903 = true := by
  rw [show D2M8K2.u3903 = KTree.node D2M8K2.t3910 (nat_lit 8769547) (nat_lit 1584360087) (nat_lit 0) D2M8K2.t3911 from rfl, allE_node, rows3910, irow3903, rows3911]
  all_goals rfl

theorem atot3903 : totK PD2M8K2 D2M8K2.u3903 = [0, 180127341725, 728607291177, 757037207950, 142920725675, 1248762627, 0, 0] := by
  rw [show D2M8K2.u3903 = KTree.node D2M8K2.t3910 (nat_lit 8769547) (nat_lit 1584360087) (nat_lit 0) D2M8K2.t3911 from rfl, totK_node, tot3910, tot3911]
  decide +kernel

theorem arows3906 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3906 = true := by
  rw [show D2M8K2.u3906 = KTree.node D2M8K2.t3912 (nat_lit 8771248) (nat_lit 3301886704) (nat_lit 0) D2M8K2.t3913 from rfl, allE_node, rows3912, irow3906, rows3913]
  all_goals rfl

theorem atot3906 : totK PD2M8K2 D2M8K2.u3906 = [0, 175146938256, 606639065526, 688457325642, 280414465809, 20681819431, 0, 0] := by
  rw [show D2M8K2.u3906 = KTree.node D2M8K2.t3912 (nat_lit 8771248) (nat_lit 3301886704) (nat_lit 0) D2M8K2.t3913 from rfl, totK_node, tot3912, tot3913]
  decide +kernel

theorem arows3907 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3907 = true := by
  rw [show D2M8K2.u3907 = KTree.node D2M8K2.t3914 (nat_lit 8793659) (nat_lit 2881265129) (nat_lit 0) D2M8K2.t3915 from rfl, allE_node, rows3914, irow3907, rows3915]
  all_goals rfl

theorem atot3907 : totK PD2M8K2 D2M8K2.u3907 = [0, 203533866854, 746963207250, 702022403904, 115479677530, 1369150432, 0, 0] := by
  rw [show D2M8K2.u3907 = KTree.node D2M8K2.t3914 (nat_lit 8793659) (nat_lit 2881265129) (nat_lit 0) D2M8K2.t3915 from rfl, totK_node, tot3914, tot3915]
  decide +kernel

theorem arows3909 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3909 = true := by
  rw [show D2M8K2.u3909 = KTree.node D2M8K2.t3916 (nat_lit 8796062) (nat_lit 3831962033) (nat_lit 0) D2M8K2.t3917 from rfl, allE_node, rows3916, irow3909, rows3917]
  all_goals rfl

theorem atot3909 : totK PD2M8K2 D2M8K2.u3909 = [0, 281403039579, 848579509057, 647946727342, 69969726789, 0, 0, 0] := by
  rw [show D2M8K2.u3909 = KTree.node D2M8K2.t3916 (nat_lit 8796062) (nat_lit 3831962033) (nat_lit 0) D2M8K2.t3917 from rfl, totK_node, tot3916, tot3917]
  decide +kernel

theorem arows3910 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3910 = true := by
  rw [show D2M8K2.u3910 = KTree.node D2M8K2.t3918 (nat_lit 8797621) (nat_lit 578112471) (nat_lit 0) D2M8K2.t3919 from rfl, allE_node, rows3918, irow3910, rows3919]
  all_goals rfl

theorem atot3910 : totK PD2M8K2 D2M8K2.u3910 = [0, 139248936037, 627109569462, 739153919678, 289640702090, 23329198674, 0, 0] := by
  rw [show D2M8K2.u3910 = KTree.node D2M8K2.t3918 (nat_lit 8797621) (nat_lit 578112471) (nat_lit 0) D2M8K2.t3919 from rfl, totK_node, tot3918, tot3919]
  decide +kernel

theorem arows3914 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3914 = true := by
  rw [show D2M8K2.u3914 = KTree.node D2M8K2.t3920 (nat_lit 8798913) (nat_lit 653366916) (nat_lit 0) D2M8K2.t3921 from rfl, allE_node, rows3920, irow3914, rows3921]
  all_goals rfl

theorem atot3914 : totK PD2M8K2 D2M8K2.u3914 = [0, 173281589747, 611709712662, 749119833020, 260270277850, 9435633141, 0, 0] := by
  rw [show D2M8K2.u3914 = KTree.node D2M8K2.t3920 (nat_lit 8798913) (nat_lit 653366916) (nat_lit 0) D2M8K2.t3921 from rfl, totK_node, tot3920, tot3921]
  decide +kernel

theorem arows3915 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3915 = true := by
  rw [show D2M8K2.u3915 = KTree.node D2M8K2.t3922 (nat_lit 8800417) (nat_lit 1553212496) (nat_lit 0) D2M8K2.t3923 from rfl, allE_node, rows3922, irow3915, rows3923]
  all_goals rfl

theorem atot3915 : totK PD2M8K2 D2M8K2.u3915 = [0, 264577241838, 808024937512, 623520661296, 101339164284, 1164319620, 0, 0] := by
  rw [show D2M8K2.u3915 = KTree.node D2M8K2.t3922 (nat_lit 8800417) (nat_lit 1553212496) (nat_lit 0) D2M8K2.t3923 from rfl, totK_node, tot3922, tot3923]
  decide +kernel

theorem arows3917 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3917 = true := by
  rw [show D2M8K2.u3917 = KTree.node D2M8K2.t3924 (nat_lit 8802050) (nat_lit 3635478296) (nat_lit 0) D2M8K2.t3925 from rfl, allE_node, rows3924, irow3917, rows3925]
  all_goals rfl

theorem atot3917 : totK PD2M8K2 D2M8K2.u3917 = [0, 152451502468, 641671595164, 770794597289, 220749777488, 11885407614, 0, 0] := by
  rw [show D2M8K2.u3917 = KTree.node D2M8K2.t3924 (nat_lit 8802050) (nat_lit 3635478296) (nat_lit 0) D2M8K2.t3925 from rfl, totK_node, tot3924, tot3925]
  decide +kernel

theorem arows3918 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3918 = true := by
  rw [show D2M8K2.u3918 = KTree.node D2M8K2.t3926 (nat_lit 8807218) (nat_lit 3148926775) (nat_lit 0) D2M8K2.t3927 from rfl, allE_node, rows3926, irow3918, rows3927]
  all_goals rfl

theorem atot3918 : totK PD2M8K2 D2M8K2.u3918 = [0, 174557790337, 763371019723, 752930163512, 104004330125, 1062926506, 0, 0] := by
  rw [show D2M8K2.u3918 = KTree.node D2M8K2.t3926 (nat_lit 8807218) (nat_lit 3148926775) (nat_lit 0) D2M8K2.t3927 from rfl, totK_node, tot3926, tot3927]
  decide +kernel

theorem arows3921 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3921 = true := by
  rw [show D2M8K2.u3921 = KTree.node D2M8K2.t3928 (nat_lit 8809734) (nat_lit 3108006264) (nat_lit 0) D2M8K2.t3929 from rfl, allE_node, rows3928, irow3921, rows3929]
  all_goals rfl

theorem atot3921 : totK PD2M8K2 D2M8K2.u3921 = [0, 314155848134, 815343359556, 561769429536, 103022985891, 3720136285, 0, 0] := by
  rw [show D2M8K2.u3921 = KTree.node D2M8K2.t3928 (nat_lit 8809734) (nat_lit 3108006264) (nat_lit 0) D2M8K2.t3929 from rfl, totK_node, tot3928, tot3929]
  decide +kernel

theorem arows3922 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3922 = true := by
  rw [show D2M8K2.u3922 = KTree.node D2M8K2.t3930 (nat_lit 8811209) (nat_lit 1560100343) (nat_lit 0) D2M8K2.t3931 from rfl, allE_node, rows3930, irow3922, rows3931]
  all_goals rfl

theorem atot3922 : totK PD2M8K2 D2M8K2.u3922 = [0, 111868955890, 633797255465, 831053311217, 207988919460, 4967996017, 0, 0] := by
  rw [show D2M8K2.u3922 = KTree.node D2M8K2.t3930 (nat_lit 8811209) (nat_lit 1560100343) (nat_lit 0) D2M8K2.t3931 from rfl, totK_node, tot3930, tot3931]
  decide +kernel

theorem arows3924 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3924 = true := by
  rw [show D2M8K2.u3924 = KTree.node D2M8K2.t3932 (nat_lit 8812902) (nat_lit 2746444626) (nat_lit 0) D2M8K2.t3933 from rfl, allE_node, rows3932, irow3924, rows3933]
  all_goals rfl

theorem atot3924 : totK PD2M8K2 D2M8K2.u3924 = [0, 0, 360239766062, 943585870657, 430321912396, 23613665221, 0, 0] := by
  rw [show D2M8K2.u3924 = KTree.node D2M8K2.t3932 (nat_lit 8812902) (nat_lit 2746444626) (nat_lit 0) D2M8K2.t3933 from rfl, totK_node, tot3932, tot3933]
  decide +kernel

theorem arows3925 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3925 = true := by
  rw [show D2M8K2.u3925 = KTree.node D2M8K2.t3934 (nat_lit 8814648) (nat_lit 3640629068) (nat_lit 0) D2M8K2.t3935 from rfl, allE_node, rows3934, irow3925, rows3935]
  all_goals rfl

theorem atot3925 : totK PD2M8K2 D2M8K2.u3925 = [0, 0, 165230232403, 769797696494, 703853462125, 83044794530, 1166720416, 0] := by
  rw [show D2M8K2.u3925 = KTree.node D2M8K2.t3934 (nat_lit 8814648) (nat_lit 3640629068) (nat_lit 0) D2M8K2.t3935 from rfl, totK_node, tot3934, tot3935]
  decide +kernel

theorem arows3930 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3930 = true := by
  rw [show D2M8K2.u3930 = KTree.node D2M8K2.t3936 (nat_lit 8817224) (nat_lit 3798084972) (nat_lit 0) D2M8K2.t3937 from rfl, allE_node, rows3936, irow3930, rows3937]
  all_goals rfl

theorem atot3930 : totK PD2M8K2 D2M8K2.u3930 = [0, 0, 476940623691, 965283843849, 365605157029, 20774790511, 0, 0] := by
  rw [show D2M8K2.u3930 = KTree.node D2M8K2.t3936 (nat_lit 8817224) (nat_lit 3798084972) (nat_lit 0) D2M8K2.t3937 from rfl, totK_node, tot3936, tot3937]
  decide +kernel

theorem arows3931 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3931 = true := by
  rw [show D2M8K2.u3931 = KTree.node D2M8K2.t3938 (nat_lit 8820483) (nat_lit 3056665025) (nat_lit 0) D2M8K2.t3939 from rfl, allE_node, rows3938, irow3931, rows3939]
  all_goals rfl

theorem atot3931 : totK PD2M8K2 D2M8K2.u3931 = [0, 0, 346278439343, 935930051506, 466130717706, 27216293363, 0, 0] := by
  rw [show D2M8K2.u3931 = KTree.node D2M8K2.t3938 (nat_lit 8820483) (nat_lit 3056665025) (nat_lit 0) D2M8K2.t3939 from rfl, totK_node, tot3938, tot3939]
  decide +kernel

theorem arows3933 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3933 = true := by
  rw [show D2M8K2.u3933 = KTree.node D2M8K2.t3940 (nat_lit 8822212) (nat_lit 4016555572) (nat_lit 0) D2M8K2.t3941 from rfl, allE_node, rows3940, irow3933, rows3941]
  all_goals rfl

theorem atot3933 : totK PD2M8K2 D2M8K2.u3933 = [0, 0, 115255062804, 650515594894, 769571087829, 170410864260, 5134755853, 0] := by
  rw [show D2M8K2.u3933 = KTree.node D2M8K2.t3940 (nat_lit 8822212) (nat_lit 4016555572) (nat_lit 0) D2M8K2.t3941 from rfl, totK_node, tot3940, tot3941]
  decide +kernel

theorem arows3934 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3934 = true := by
  rw [show D2M8K2.u3934 = KTree.node D2M8K2.t3942 (nat_lit 8830093) (nat_lit 1391339689) (nat_lit 0) D2M8K2.t3943 from rfl, allE_node, rows3942, irow3934, rows3943]
  all_goals rfl

theorem atot3934 : totK PD2M8K2 D2M8K2.u3934 = [0, 0, 427412479316, 949110472577, 367349244537, 18804176403, 0, 0] := by
  rw [show D2M8K2.u3934 = KTree.node D2M8K2.t3942 (nat_lit 8830093) (nat_lit 1391339689) (nat_lit 0) D2M8K2.t3943 from rfl, totK_node, tot3942, tot3943]
  decide +kernel

theorem arows3937 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3937 = true := by
  rw [show D2M8K2.u3937 = KTree.node D2M8K2.t3944 (nat_lit 8831668) (nat_lit 3724428541) (nat_lit 0) D2M8K2.t3945 from rfl, allE_node, rows3944, irow3937, rows3945]
  all_goals rfl

theorem atot3937 : totK PD2M8K2 D2M8K2.u3937 = [0, 150840131194, 557071756807, 723525411781, 321731057777, 22919250980, 0, 0] := by
  rw [show D2M8K2.u3937 = KTree.node D2M8K2.t3944 (nat_lit 8831668) (nat_lit 3724428541) (nat_lit 0) D2M8K2.t3945 from rfl, totK_node, tot3944, tot3945]
  decide +kernel

theorem arows3938 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3938 = true := by
  rw [show D2M8K2.u3938 = KTree.node D2M8K2.t3946 (nat_lit 8835059) (nat_lit 2897870831) (nat_lit 0) D2M8K2.t3947 from rfl, allE_node, rows3946, irow3938, rows3947]
  all_goals rfl

theorem atot3938 : totK PD2M8K2 D2M8K2.u3938 = [0, 227936941001, 776308484485, 672327258415, 107034074392, 1369150432, 0, 0] := by
  rw [show D2M8K2.u3938 = KTree.node D2M8K2.t3946 (nat_lit 8835059) (nat_lit 2897870831) (nat_lit 0) D2M8K2.t3947 from rfl, totK_node, tot3946, tot3947]
  decide +kernel

theorem arows3940 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3940 = true := by
  rw [show D2M8K2.u3940 = KTree.node D2M8K2.t3948 (nat_lit 8837482) (nat_lit 3883896084) (nat_lit 0) D2M8K2.t3949 from rfl, allE_node, rows3948, irow3940, rows3949]
  all_goals rfl

theorem atot3940 : totK PD2M8K2 D2M8K2.u3940 = [0, 252388224268, 835489942673, 680503974958, 77475625525, 0, 0, 0] := by
  rw [show D2M8K2.u3940 = KTree.node D2M8K2.t3948 (nat_lit 8837482) (nat_lit 3883896084) (nat_lit 0) D2M8K2.t3949 from rfl, totK_node, tot3948, tot3949]
  decide +kernel

theorem arows3941 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3941 = true := by
  rw [show D2M8K2.u3941 = KTree.node D2M8K2.t3950 (nat_lit 8839048) (nat_lit 3819821506) (nat_lit 0) D2M8K2.t3951 from rfl, allE_node, rows3950, irow3941, rows3951]
  all_goals rfl

theorem atot3941 : totK PD2M8K2 D2M8K2.u3941 = [0, 168335624325, 662463106634, 713897973543, 260995704144, 20729740161, 0, 0] := by
  rw [show D2M8K2.u3941 = KTree.node D2M8K2.t3950 (nat_lit 8839048) (nat_lit 3819821506) (nat_lit 0) D2M8K2.t3951 from rfl, totK_node, tot3950, tot3951]
  decide +kernel

theorem arows3945 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3945 = true := by
  rw [show D2M8K2.u3945 = KTree.node D2M8K2.t3952 (nat_lit 8840305) (nat_lit 1358852103) (nat_lit 0) D2M8K2.t3953 from rfl, allE_node, rows3952, irow3945, rows3953]
  all_goals rfl

theorem atot3945 : totK PD2M8K2 D2M8K2.u3945 = [0, 173357259223, 594182304329, 739146826412, 285216344175, 12075845174, 0, 0] := by
  rw [show D2M8K2.u3945 = KTree.node D2M8K2.t3952 (nat_lit 8840305) (nat_lit 1358852103) (nat_lit 0) D2M8K2.t3953 from rfl, totK_node, tot3952, tot3953]
  decide +kernel

theorem arows3946 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3946 = true := by
  rw [show D2M8K2.u3946 = KTree.node D2M8K2.t3954 (nat_lit 8845233) (nat_lit 1614214292) (nat_lit 0) D2M8K2.t3955 from rfl, allE_node, rows3954, irow3946, rows3955]
  all_goals rfl

theorem atot3946 : totK PD2M8K2 D2M8K2.u3946 = [0, 264696109929, 813982938982, 627411743195, 88196182374, 1198073392, 0, 0] := by
  rw [show D2M8K2.u3946 = KTree.node D2M8K2.t3954 (nat_lit 8845233) (nat_lit 1614214292) (nat_lit 0) D2M8K2.t3955 from rfl, totK_node, tot3954, tot3955]
  decide +kernel

theorem arows3948 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3948 = true := by
  rw [show D2M8K2.u3948 = KTree.node D2M8K2.t3956 (nat_lit 8846882) (nat_lit 4038167588) (nat_lit 0) D2M8K2.t3957 from rfl, allE_node, rows3956, irow3948, rows3957]
  all_goals rfl

theorem atot3948 : totK PD2M8K2 D2M8K2.u3948 = [0, 122003319170, 604513701031, 812171590507, 246547597658, 11991925116, 0, 0] := by
  rw [show D2M8K2.u3948 = KTree.node D2M8K2.t3956 (nat_lit 8846882) (nat_lit 4038167588) (nat_lit 0) D2M8K2.t3957 from rfl, totK_node, tot3956, tot3957]
  decide +kernel

theorem arows3949 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3949 = true := by
  rw [show D2M8K2.u3949 = KTree.node D2M8K2.t3958 (nat_lit 8848606) (nat_lit 3073242423) (nat_lit 0) D2M8K2.t3959 from rfl, allE_node, rows3958, irow3949, rows3959]
  all_goals rfl

theorem atot3949 : totK PD2M8K2 D2M8K2.u3949 = [0, 205146021975, 797269581749, 713648487698, 100709462339, 1096505104, 0, 0] := by
  rw [show D2M8K2.u3949 = KTree.node D2M8K2.t3958 (nat_lit 8848606) (nat_lit 3073242423) (nat_lit 0) D2M8K2.t3959 from rfl, totK_node, tot3958, tot3959]
  decide +kernel

theorem arows3952 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3952 = true := by
  rw [show D2M8K2.u3952 = KTree.node D2M8K2.t3960 (nat_lit 8851149) (nat_lit 1431418000) (nat_lit 0) D2M8K2.t3961 from rfl, allE_node, rows3960, irow3952, rows3961]
  all_goals rfl

theorem atot3952 : totK PD2M8K2 D2M8K2.u3952 = [0, 283735521811, 793136254034, 598968384225, 109538400721, 3821179711, 0, 0] := by
  rw [show D2M8K2.u3952 = KTree.node D2M8K2.t3960 (nat_lit 8851149) (nat_lit 1431418000) (nat_lit 0) D2M8K2.t3961 from rfl, totK_node, tot3960, tot3961]
  decide +kernel

theorem arows3953 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3953 = true := by
  rw [show D2M8K2.u3953 = KTree.node D2M8K2.t3962 (nat_lit 8852617) (nat_lit 1512170416) (nat_lit 0) D2M8K2.t3963 from rfl, allE_node, rows3962, irow3953, rows3963]
  all_goals rfl

theorem atot3953 : totK PD2M8K2 D2M8K2.u3953 = [0, 138278827267, 664911383258, 784963329036, 195909127887, 4899206309, 0, 0] := by
  rw [show D2M8K2.u3953 = KTree.node D2M8K2.t3962 (nat_lit 8852617) (nat_lit 1512170416) (nat_lit 0) D2M8K2.t3963 from rfl, totK_node, tot3962, tot3963]
  decide +kernel

theorem arows3955 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3955 = true := by
  rw [show D2M8K2.u3955 = KTree.node D2M8K2.t3964 (nat_lit 8854294) (nat_lit 3547600099) (nat_lit 0) D2M8K2.t3965 from rfl, allE_node, rows3964, irow3955, rows3965]
  all_goals rfl

theorem atot3955 : totK PD2M8K2 D2M8K2.u3955 = [0, 0, 393766315617, 958334094281, 395706933937, 20781990054, 0, 0] := by
  rw [show D2M8K2.u3955 = KTree.node D2M8K2.t3964 (nat_lit 8854294) (nat_lit 3547600099) (nat_lit 0) D2M8K2.t3965 from rfl, totK_node, tot3964, tot3965]
  decide +kernel

theorem arows3956 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3956 = true := by
  rw [show D2M8K2.u3956 = KTree.node D2M8K2.t3966 (nat_lit 8856059) (nat_lit 2597867178) (nat_lit 0) D2M8K2.t3967 from rfl, allE_node, rows3966, irow3956, rows3967]
  all_goals rfl

theorem atot3956 : totK PD2M8K2 D2M8K2.u3956 = [0, 0, 148801743801, 777078587957, 708424945483, 80893241676, 1200365979, 0] := by
  rw [show D2M8K2.u3956 = KTree.node D2M8K2.t3966 (nat_lit 8856059) (nat_lit 2597867178) (nat_lit 0) D2M8K2.t3967 from rfl, totK_node, tot3966, tot3967]
  decide +kernel

theorem arows3963 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3963 = true := by
  rw [show D2M8K2.u3963 = KTree.node D2M8K2.t3968 (nat_lit 8858722) (nat_lit 4117617877) (nat_lit 0) D2M8K2.t3969 from rfl, allE_node, rows3968, irow3963, rows3969]
  all_goals rfl

theorem atot3963 : totK PD2M8K2 D2M8K2.u3963 = [0, 0, 464187850535, 943948536976, 405984600260, 28642566137, 0, 0] := by
  rw [show D2M8K2.u3963 = KTree.node D2M8K2.t3968 (nat_lit 8858722) (nat_lit 4117617877) (nat_lit 0) D2M8K2.t3969 from rfl, totK_node, tot3968, tot3969]
  decide +kernel

theorem arows3964 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3964 = true := by
  rw [show D2M8K2.u3964 = KTree.node D2M8K2.t3970 (nat_lit 8865628) (nat_lit 3099847688) (nat_lit 0) D2M8K2.t3971 from rfl, allE_node, rows3970, irow3964, rows3971]
  all_goals rfl

theorem atot3964 : totK PD2M8K2 D2M8K2.u3964 = [0, 0, 379748141692, 940890946585, 433552858321, 24896594090, 0, 0] := by
  rw [show D2M8K2.u3964 = KTree.node D2M8K2.t3970 (nat_lit 8865628) (nat_lit 3099847688) (nat_lit 0) D2M8K2.t3971 from rfl, totK_node, tot3970, tot3971]
  decide +kernel

theorem arows3966 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3966 = true := by
  rw [show D2M8K2.u3966 = KTree.node D2M8K2.t3972 (nat_lit 8867353) (nat_lit 1457060603) (nat_lit 0) D2M8K2.t3973 from rfl, allE_node, rows3972, irow3966, rows3973]
  all_goals rfl

theorem atot3966 : totK PD2M8K2 D2M8K2.u3966 = [0, 0, 74134837701, 647166067059, 813399820976, 174837086623, 5163565574, 0] := by
  rw [show D2M8K2.u3966 = KTree.node D2M8K2.t3972 (nat_lit 8867353) (nat_lit 1457060603) (nat_lit 0) D2M8K2.t3973 from rfl, totK_node, tot3972, tot3973]
  decide +kernel

theorem arows3967 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3967 = true := by
  rw [show D2M8K2.u3967 = KTree.node D2M8K2.t3974 (nat_lit 8871614) (nat_lit 2564622701) (nat_lit 0) D2M8K2.t3975 from rfl, allE_node, rows3974, irow3967, rows3975]
  all_goals rfl

theorem atot3967 : totK PD2M8K2 D2M8K2.u3967 = [0, 0, 487146135168, 950260219607, 325521533000, 15264253750, 0, 0] := by
  rw [show D2M8K2.u3967 = KTree.node D2M8K2.t3974 (nat_lit 8871614) (nat_lit 2564622701) (nat_lit 0) D2M8K2.t3975 from rfl, totK_node, tot3974, tot3975]
  decide +kernel

theorem arows3970 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3970 = true := by
  rw [show D2M8K2.u3970 = KTree.node D2M8K2.t3976 (nat_lit 8873158) (nat_lit 3485877379) (nat_lit 0) D2M8K2.t3977 from rfl, allE_node, rows3976, irow3970, rows3977]
  all_goals rfl

theorem atot3970 : totK PD2M8K2 D2M8K2.u3970 = [0, 173861880260, 579321793886, 688712496296, 328099908373, 23883506540, 0, 0] := by
  rw [show D2M8K2.u3970 = KTree.node D2M8K2.t3976 (nat_lit 8873158) (nat_lit 3485877379) (nat_lit 0) D2M8K2.t3977 from rfl, totK_node, tot3976, tot3977]
  decide +kernel

theorem arows3971 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3971 = true := by
  rw [show D2M8K2.u3971 = KTree.node D2M8K2.t3978 (nat_lit 8917978) (nat_lit 3992918297) (nat_lit 0) D2M8K2.t3979 from rfl, allE_node, rows3978, irow3971, rows3979]
  all_goals rfl

theorem atot3971 : totK PD2M8K2 D2M8K2.u3971 = [0, 224525737327, 773846952392, 657663387114, 103783668118, 1369150432, 0, 0] := by
  rw [show D2M8K2.u3971 = KTree.node D2M8K2.t3978 (nat_lit 8917978) (nat_lit 3992918297) (nat_lit 0) D2M8K2.t3979 from rfl, totK_node, tot3978, tot3979]
  decide +kernel

theorem arows3973 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3973 = true := by
  rw [show D2M8K2.u3973 = KTree.node D2M8K2.t3980 (nat_lit 8920355) (nat_lit 2962688467) (nat_lit 0) D2M8K2.t3981 from rfl, allE_node, rows3980, irow3973, rows3981]
  all_goals rfl

theorem atot3973 : totK PD2M8K2 D2M8K2.u3973 = [0, 249237874631, 812110670105, 690574189879, 76258809512, 0, 0, 0] := by
  rw [show D2M8K2.u3973 = KTree.node D2M8K2.t3980 (nat_lit 8920355) (nat_lit 2962688467) (nat_lit 0) D2M8K2.t3981 from rfl, totK_node, tot3980, tot3981]
  decide +kernel

theorem arows3974 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3974 = true := by
  rw [show D2M8K2.u3974 = KTree.node D2M8K2.t3982 (nat_lit 8921581) (nat_lit 1024261028) (nat_lit 0) D2M8K2.t3983 from rfl, allE_node, rows3982, irow3974, rows3983]
  all_goals rfl

theorem atot3974 : totK PD2M8K2 D2M8K2.u3974 = [0, 175058849830, 707760595735, 706571263604, 220296003012, 18724171075, 0, 0] := by
  rw [show D2M8K2.u3974 = KTree.node D2M8K2.t3982 (nat_lit 8921581) (nat_lit 1024261028) (nat_lit 0) D2M8K2.t3983 from rfl, totK_node, tot3982, tot3983]
  decide +kernel

theorem arows3978 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3978 = true := by
  rw [show D2M8K2.u3978 = KTree.node D2M8K2.t3984 (nat_lit 8923144) (nat_lit 3806966238) (nat_lit 0) D2M8K2.t3985 from rfl, allE_node, rows3984, irow3978, rows3985]
  all_goals rfl

theorem atot3978 : totK PD2M8K2 D2M8K2.u3978 = [0, 137975527160, 543356170003, 773431542324, 320975817599, 11683261214, 0, 0] := by
  rw [show D2M8K2.u3978 = KTree.node D2M8K2.t3984 (nat_lit 8923144) (nat_lit 3806966238) (nat_lit 0) D2M8K2.t3985 from rfl, totK_node, tot3984, tot3985]
  decide +kernel

theorem arows3979 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3979 = true := by
  rw [show D2M8K2.u3979 = KTree.node D2M8K2.t3986 (nat_lit 8924597) (nat_lit 2385402881) (nat_lit 0) D2M8K2.t3987 from rfl, allE_node, rows3986, irow3979, rows3987]
  all_goals rfl

theorem atot3979 : totK PD2M8K2 D2M8K2.u3979 = [0, 276799313661, 857752114372, 604588953192, 62622565700, 0, 0, 0] := by
  rw [show D2M8K2.u3979 = KTree.node D2M8K2.t3986 (nat_lit 8924597) (nat_lit 2385402881) (nat_lit 0) D2M8K2.t3987 from rfl, totK_node, tot3986, tot3987]
  decide +kernel

theorem arows3981 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3981 = true := by
  rw [show D2M8K2.u3981 = KTree.node D2M8K2.t3988 (nat_lit 8926322) (nat_lit 3995083918) (nat_lit 0) D2M8K2.t3989 from rfl, allE_node, rows3988, irow3981, rows3989]
  all_goals rfl

theorem atot3981 : totK PD2M8K2 D2M8K2.u3981 = [0, 113620377193, 582803655729, 820289131400, 236340104837, 8557595888, 0, 0] := by
  rw [show D2M8K2.u3981 = KTree.node D2M8K2.t3988 (nat_lit 8926322) (nat_lit 3995083918) (nat_lit 0) D2M8K2.t3989 from rfl, totK_node, tot3988, tot3989]
  decide +kernel

theorem arows3982 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3982 = true := by
  rw [show D2M8K2.u3982 = KTree.node D2M8K2.t3990 (nat_lit 8928018) (nat_lit 3378061122) (nat_lit 0) D2M8K2.t3991 from rfl, allE_node, rows3990, irow3982, rows3991]
  all_goals rfl

theorem atot3982 : totK PD2M8K2 D2M8K2.u3982 = [0, 301584311106, 888603776128, 567058010391, 52832607744, 0, 0, 0] := by
  rw [show D2M8K2.u3982 = KTree.node D2M8K2.t3990 (nat_lit 8928018) (nat_lit 3378061122) (nat_lit 0) D2M8K2.t3991 from rfl, totK_node, tot3990, tot3991]
  decide +kernel

theorem arows3985 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3985 = true := by
  rw [show D2M8K2.u3985 = KTree.node D2M8K2.t3992 (nat_lit 8929734) (nat_lit 3738511779) (nat_lit 0) D2M8K2.t3993 from rfl, allE_node, rows3992, irow3985, rows3993]
  all_goals rfl

theorem atot3985 : totK PD2M8K2 D2M8K2.u3985 = [0, 86419853613, 559273419549, 855746399657, 255464673385, 8656689423, 0, 0] := by
  rw [show D2M8K2.u3985 = KTree.node D2M8K2.t3992 (nat_lit 8929734) (nat_lit 3738511779) (nat_lit 0) D2M8K2.t3993 from rfl, totK_node, tot3992, tot3993]
  decide +kernel

theorem arows3986 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3986 = true := by
  rw [show D2M8K2.u3986 = KTree.node D2M8K2.t3994 (nat_lit 8934590) (nat_lit 2438678736) (nat_lit 0) D2M8K2.t3995 from rfl, allE_node, rows3994, irow3986, rows3995]
  all_goals rfl

theorem atot3986 : totK PD2M8K2 D2M8K2.u3986 = [0, 361086053141, 924220902863, 523179368837, 43541683325, 0, 0, 0] := by
  rw [show D2M8K2.u3986 = KTree.node D2M8K2.t3994 (nat_lit 8934590) (nat_lit 2438678736) (nat_lit 0) D2M8K2.t3995 from rfl, totK_node, tot3994, tot3995]
  decide +kernel

theorem arows3988 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3988 = true := by
  rw [show D2M8K2.u3988 = KTree.node D2M8K2.t3996 (nat_lit 8936198) (nat_lit 3951223819) (nat_lit 0) D2M8K2.t3997 from rfl, allE_node, rows3996, irow3988, rows3997]
  all_goals rfl

theorem atot3988 : totK PD2M8K2 D2M8K2.u3988 = [0, 0, 460411700365, 992973762669, 332261536296, 9938656398, 0, 0] := by
  rw [show D2M8K2.u3988 = KTree.node D2M8K2.t3996 (nat_lit 8936198) (nat_lit 3951223819) (nat_lit 0) D2M8K2.t3997 from rfl, totK_node, tot3996, tot3997]
  decide +kernel

theorem arows3989 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3989 = true := by
  rw [show D2M8K2.u3989 = KTree.node D2M8K2.t3998 (nat_lit 8937997) (nat_lit 1097895557) (nat_lit 0) D2M8K2.t3999 from rfl, allE_node, rows3998, irow3989, rows3999]
  all_goals rfl

theorem atot3989 : totK PD2M8K2 D2M8K2.u3989 = [0, 0, 373518682776, 928354733268, 396647784599, 22431078601, 0, 0] := by
  rw [show D2M8K2.u3989 = KTree.node D2M8K2.t3998 (nat_lit 8937997) (nat_lit 1097895557) (nat_lit 0) D2M8K2.t3999 from rfl, totK_node, tot3998, tot3999]
  decide +kernel

theorem arows3994 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3994 = true := by
  rw [show D2M8K2.u3994 = KTree.node D2M8K2.t4000 (nat_lit 8939815) (nat_lit 2313081393) (nat_lit 0) D2M8K2.t4001 from rfl, allE_node, rows4000, irow3994, rows4001]
  all_goals rfl

theorem atot3994 : totK PD2M8K2 D2M8K2.u3994 = [0, 0, 112046531778, 683685097781, 829575831842, 127059663185, 1288491354, 0] := by
  rw [show D2M8K2.u3994 = KTree.node D2M8K2.t4000 (nat_lit 8939815) (nat_lit 2313081393) (nat_lit 0) D2M8K2.t4001 from rfl, totK_node, tot4000, tot4001]
  decide +kernel

theorem arows3995 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3995 = true := by
  rw [show D2M8K2.u3995 = KTree.node D2M8K2.t4002 (nat_lit 8941800) (nat_lit 3171974766) (nat_lit 0) D2M8K2.t4003 from rfl, allE_node, rows4002, irow3995, rows4003]
  all_goals rfl

theorem atot3995 : totK PD2M8K2 D2M8K2.u3995 = [0, 0, 410937195278, 958965134266, 408854021090, 25185837974, 0, 0] := by
  rw [show D2M8K2.u3995 = KTree.node D2M8K2.t4002 (nat_lit 8941800) (nat_lit 3171974766) (nat_lit 0) D2M8K2.t4003 from rfl, totK_node, tot4002, tot4003]
  decide +kernel

theorem arows3997 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3997 = true := by
  rw [show D2M8K2.u3997 = KTree.node D2M8K2.t4004 (nat_lit 8944909) (nat_lit 1193301329) (nat_lit 0) D2M8K2.t4005 from rfl, allE_node, rows4004, irow3997, rows4005]
  all_goals rfl

theorem atot3997 : totK PD2M8K2 D2M8K2.u3997 = [0, 0, 330635651658, 917991635522, 496361960978, 33808867418, 0, 0] := by
  rw [show D2M8K2.u3997 = KTree.node D2M8K2.t4004 (nat_lit 8944909) (nat_lit 1193301329) (nat_lit 0) D2M8K2.t4005 from rfl, totK_node, tot4004, tot4005]
  decide +kernel

theorem arows3998 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3998 = true := by
  rw [show D2M8K2.u3998 = KTree.node D2M8K2.t4006 (nat_lit 8947021) (nat_lit 1058979360) (nat_lit 0) D2M8K2.t4007 from rfl, allE_node, rows4006, irow3998, rows4007]
  all_goals rfl

theorem atot3998 : totK PD2M8K2 D2M8K2.u3998 = [0, 0, 149609352928, 667987879790, 720220686030, 153281082490, 4787054165, 0] := by
  rw [show D2M8K2.u3998 = KTree.node D2M8K2.t4006 (nat_lit 8947021) (nat_lit 1058979360) (nat_lit 0) D2M8K2.t4007 from rfl, totK_node, tot4006, tot4007]
  decide +kernel

theorem arows4001 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4001 = true := by
  rw [show D2M8K2.u4001 = KTree.node D2M8K2.t4008 (nat_lit 8948907) (nat_lit 2677243362) (nat_lit 0) D2M8K2.t4009 from rfl, allE_node, rows4008, irow4001, rows4009]
  all_goals rfl

theorem atot4001 : totK PD2M8K2 D2M8K2.u4001 = [0, 0, 260244156700, 813574993225, 595978324953, 79256147595, 1086231185, 0] := by
  rw [show D2M8K2.u4001 = KTree.node D2M8K2.t4008 (nat_lit 8948907) (nat_lit 2677243362) (nat_lit 0) D2M8K2.t4009 from rfl, totK_node, tot4008, tot4009]
  decide +kernel

theorem arows4002 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4002 = true := by
  rw [show D2M8K2.u4002 = KTree.node D2M8K2.t4010 (nat_lit 8950891) (nat_lit 1609529532) (nat_lit 0) D2M8K2.t4011 from rfl, allE_node, rows4010, irow4002, rows4011]
  all_goals rfl

theorem atot4002 : totK PD2M8K2 D2M8K2.u4002 = [0, 0, 195854956453, 766149649299, 674825971225, 124880738971, 3752012233, 0] := by
  rw [show D2M8K2.u4002 = KTree.node D2M8K2.t4010 (nat_lit 8950891) (nat_lit 1609529532) (nat_lit 0) D2M8K2.t4011 from rfl, totK_node, tot4010, tot4011]
  decide +kernel

theorem arows4004 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4004 = true := by
  rw [show D2M8K2.u4004 = KTree.node D2M8K2.t4012 (nat_lit 8955982) (nat_lit 4019137817) (nat_lit 0) D2M8K2.t4013 from rfl, allE_node, rows4012, irow4004, rows4013]
  all_goals rfl

theorem atot4004 : totK PD2M8K2 D2M8K2.u4004 = [0, 0, 242411503064, 792653659063, 647764643847, 102641869518, 1242138600, 0] := by
  rw [show D2M8K2.u4004 = KTree.node D2M8K2.t4012 (nat_lit 8955982) (nat_lit 4019137817) (nat_lit 0) D2M8K2.t4013 from rfl, totK_node, tot4012, tot4013]
  decide +kernel

theorem arows4005 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4005 = true := by
  rw [show D2M8K2.u4005 = KTree.node D2M8K2.t4014 (nat_lit 8957690) (nat_lit 4222122315) (nat_lit 0) D2M8K2.t4015 from rfl, allE_node, rows4014, irow4005, rows4015]
  all_goals rfl

theorem atot4005 : totK PD2M8K2 D2M8K2.u4005 = [0, 94445126902, 239990604536, 445039504699, 683791517394, 290434913853, 20509029466, 0] := by
  rw [show D2M8K2.u4005 = KTree.node D2M8K2.t4014 (nat_lit 8957690) (nat_lit 4222122315) (nat_lit 0) D2M8K2.t4015 from rfl, totK_node, tot4014, tot4015]
  decide +kernel

theorem arows4009 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4009 = true := by
  rw [show D2M8K2.u4009 = KTree.node D2M8K2.t4016 (nat_lit 9501697) (nat_lit 1183169838) (nat_lit 0) D2M8K2.t4017 from rfl, allE_node, rows4016, irow4009, rows4017]
  all_goals rfl

theorem atot4009 : totK PD2M8K2 D2M8K2.u4009 = [0, 355489735814, 935781078737, 512552148011, 41630613123, 0, 0, 0] := by
  rw [show D2M8K2.u4009 = KTree.node D2M8K2.t4016 (nat_lit 9501697) (nat_lit 1183169838) (nat_lit 0) D2M8K2.t4017 from rfl, totK_node, tot4016, tot4017]
  decide +kernel

theorem arows4010 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4010 = true := by
  rw [show D2M8K2.u4010 = KTree.node D2M8K2.t4018 (nat_lit 9503146) (nat_lit 3691428894) (nat_lit 0) D2M8K2.t4019 from rfl, allE_node, rows4018, irow4010, rows4019]
  all_goals rfl

theorem atot4010 : totK PD2M8K2 D2M8K2.u4010 = [0, 0, 386575915670, 947006985370, 455062258141, 30804453458, 0, 0] := by
  rw [show D2M8K2.u4010 = KTree.node D2M8K2.t4018 (nat_lit 9503146) (nat_lit 3691428894) (nat_lit 0) D2M8K2.t4019 from rfl, totK_node, tot4018, tot4019]
  decide +kernel

theorem arows4012 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4012 = true := by
  rw [show D2M8K2.u4012 = KTree.node D2M8K2.t4020 (nat_lit 9504474) (nat_lit 3625354406) (nat_lit 0) D2M8K2.t4021 from rfl, allE_node, rows4020, irow4012, rows4021]
  all_goals rfl

theorem atot4012 : totK PD2M8K2 D2M8K2.u4012 = [0, 335268704928, 819625264470, 540393199264, 133556176023, 6804944647, 0, 0] := by
  rw [show D2M8K2.u4012 = KTree.node D2M8K2.t4020 (nat_lit 9504474) (nat_lit 3625354406) (nat_lit 0) D2M8K2.t4021 from rfl, totK_node, tot4020, tot4021]
  decide +kernel

theorem arows4013 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4013 = true := by
  rw [show D2M8K2.u4013 = KTree.node D2M8K2.t4022 (nat_lit 9505996) (nat_lit 3736817080) (nat_lit 0) D2M8K2.t4023 from rfl, allE_node, rows4022, irow4013, rows4023]
  all_goals rfl

theorem atot4013 : totK PD2M8K2 D2M8K2.u4013 = [0, 87489962043, 632070640146, 854623788956, 215559809005, 8154189357, 0, 0] := by
  rw [show D2M8K2.u4013 = KTree.node D2M8K2.t4022 (nat_lit 9505996) (nat_lit 3736817080) (nat_lit 0) D2M8K2.t4023 from rfl, totK_node, tot4022, tot4023]
  decide +kernel

theorem arows4016 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4016 = true := by
  rw [show D2M8K2.u4016 = KTree.node D2M8K2.t4024 (nat_lit 9507849) (nat_lit 1895681444) (nat_lit 0) D2M8K2.t4025 from rfl, allE_node, rows4024, irow4016, rows4025]
  all_goals rfl

theorem atot4016 : totK PD2M8K2 D2M8K2.u4016 = [0, 298046231608, 805996579364, 601598648680, 114048607332, 3215984770, 0, 0] := by
  rw [show D2M8K2.u4016 = KTree.node D2M8K2.t4024 (nat_lit 9507849) (nat_lit 1895681444) (nat_lit 0) D2M8K2.t4025 from rfl, totK_node, tot4024, tot4025]
  decide +kernel

theorem arows4017 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4017 = true := by
  rw [show D2M8K2.u4017 = KTree.node D2M8K2.t4026 (nat_lit 9509318) (nat_lit 3270929762) (nat_lit 0) D2M8K2.t4027 from rfl, allE_node, rows4026, irow4017, rows4027]
  all_goals rfl

theorem atot4017 : totK PD2M8K2 D2M8K2.u4017 = [0, 124921220308, 654110873726, 802769277792, 210794185206, 8199159193, 0, 0] := by
  rw [show D2M8K2.u4017 = KTree.node D2M8K2.t4026 (nat_lit 9509318) (nat_lit 3270929762) (nat_lit 0) D2M8K2.t4027 from rfl, totK_node, tot4026, tot4027]
  decide +kernel

theorem arows4019 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4019 = true := by
  rw [show D2M8K2.u4019 = KTree.node D2M8K2.t4028 (nat_lit 9511243) (nat_lit 1804167824) (nat_lit 0) D2M8K2.t4029 from rfl, allE_node, rows4028, irow4019, rows4029]
  all_goals rfl

theorem atot4019 : totK PD2M8K2 D2M8K2.u4019 = [0, 255285361691, 769192075233, 646000913437, 128808100800, 3329039539, 0, 0] := by
  rw [show D2M8K2.u4019 = KTree.node D2M8K2.t4028 (nat_lit 9511243) (nat_lit 1804167824) (nat_lit 0) D2M8K2.t4029 from rfl, totK_node, tot4028, tot4029]
  decide +kernel

theorem arows4020 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4020 = true := by
  rw [show D2M8K2.u4020 = KTree.node D2M8K2.t4030 (nat_lit 9512700) (nat_lit 2995400837) (nat_lit 0) D2M8K2.t4031 from rfl, allE_node, rows4030, irow4020, rows4031]
  all_goals rfl

theorem atot4020 : totK PD2M8K2 D2M8K2.u4020 = [0, 162189279840, 765510973490, 772061042025, 116763693383, 0, 0, 0] := by
  rw [show D2M8K2.u4020 = KTree.node D2M8K2.t4030 (nat_lit 9512700) (nat_lit 2995400837) (nat_lit 0) D2M8K2.t4031 from rfl, totK_node, tot4030, tot4031]
  decide +kernel

theorem arows4026 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4026 = true := by
  rw [show D2M8K2.u4026 = KTree.node D2M8K2.t4032 (nat_lit 9514749) (nat_lit 1432470239) (nat_lit 0) D2M8K2.t4033 from rfl, allE_node, rows4032, irow4026, rows4033]
  all_goals rfl

theorem atot4026 : totK PD2M8K2 D2M8K2.u4026 = [0, 299512681770, 801779743898, 602142487304, 122257020214, 3632925411, 0, 0] := by
  rw [show D2M8K2.u4026 = KTree.node D2M8K2.t4032 (nat_lit 9514749) (nat_lit 1432470239) (nat_lit 0) D2M8K2.t4033 from rfl, totK_node, tot4032, tot4033]
  decide +kernel

theorem arows4027 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4027 = true := by
  rw [show D2M8K2.u4027 = KTree.node D2M8K2.t4034 (nat_lit 9516187) (nat_lit 1677118092) (nat_lit 0) D2M8K2.t4035 from rfl, allE_node, rows4034, irow4027, rows4035]
  all_goals rfl

theorem atot4027 : totK PD2M8K2 D2M8K2.u4027 = [0, 125863117380, 666404889817, 813139643283, 194763002223, 3439610676, 0, 0] := by
  rw [show D2M8K2.u4027 = KTree.node D2M8K2.t4034 (nat_lit 9516187) (nat_lit 1677118092) (nat_lit 0) D2M8K2.t4035 from rfl, totK_node, tot4034, tot4035]
  decide +kernel

theorem arows4029 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4029 = true := by
  rw [show D2M8K2.u4029 = KTree.node D2M8K2.t4036 (nat_lit 9521632) (nat_lit 3751831776) (nat_lit 0) D2M8K2.t4037 from rfl, allE_node, rows4036, irow4029, rows4037]
  all_goals rfl

theorem atot4029 : totK PD2M8K2 D2M8K2.u4029 = [0, 0, 360039167152, 914541236132, 505063801703, 45021325875, 0, 0] := by
  rw [show D2M8K2.u4029 = KTree.node D2M8K2.t4036 (nat_lit 9521632) (nat_lit 3751831776) (nat_lit 0) D2M8K2.t4037 from rfl, totK_node, tot4036, tot4037]
  decide +kernel

theorem arows4030 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4030 = true := by
  rw [show D2M8K2.u4030 = KTree.node D2M8K2.t4038 (nat_lit 9522784) (nat_lit 3741127726) (nat_lit 0) D2M8K2.t4039 from rfl, allE_node, rows4038, irow4030, rows4039]
  all_goals rfl

theorem atot4030 : totK PD2M8K2 D2M8K2.u4030 = [0, 0, 232566442062, 772951170194, 628304940040, 187195116938, 21385604922, 0] := by
  rw [show D2M8K2.u4030 = KTree.node D2M8K2.t4038 (nat_lit 9522784) (nat_lit 3741127726) (nat_lit 0) D2M8K2.t4039 from rfl, totK_node, tot4038, tot4039]
  decide +kernel

theorem arows4033 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4033 = true := by
  rw [show D2M8K2.u4033 = KTree.node D2M8K2.t4040 (nat_lit 9524244) (nat_lit 2589052680) (nat_lit 0) D2M8K2.t4041 from rfl, allE_node, rows4040, irow4033, rows4041]
  all_goals rfl

theorem atot4033 : totK PD2M8K2 D2M8K2.u4033 = [0, 0, 66225297140, 460220180071, 869861282047, 360830669415, 15536268932, 0] := by
  rw [show D2M8K2.u4033 = KTree.node D2M8K2.t4040 (nat_lit 9524244) (nat_lit 2589052680) (nat_lit 0) D2M8K2.t4041 from rfl, totK_node, tot4040, tot4041]
  decide +kernel

theorem arows4034 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4034 = true := by
  rw [show D2M8K2.u4034 = KTree.node D2M8K2.t4042 (nat_lit 9525552) (nat_lit 3215746288) (nat_lit 0) D2M8K2.t4043 from rfl, allE_node, rows4042, irow4034, rows4043]
  all_goals rfl

theorem atot4034 : totK PD2M8K2 D2M8K2.u4034 = [0, 0, 354610372802, 923839813931, 509072306440, 38388663570, 0, 0] := by
  rw [show D2M8K2.u4034 = KTree.node D2M8K2.t4042 (nat_lit 9525552) (nat_lit 3215746288) (nat_lit 0) D2M8K2.t4043 from rfl, totK_node, tot4042, tot4043]
  decide +kernel

theorem arows4036 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4036 = true := by
  rw [show D2M8K2.u4036 = KTree.node D2M8K2.t4044 (nat_lit 9527647) (nat_lit 1921776686) (nat_lit 0) D2M8K2.t4045 from rfl, allE_node, rows4044, irow4036, rows4045]
  all_goals rfl

theorem atot4036 : totK PD2M8K2 D2M8K2.u4036 = [0, 0, 94106722254, 625309185878, 867196868519, 201114680407, 5159868635, 0] := by
  rw [show D2M8K2.u4036 = KTree.node D2M8K2.t4044 (nat_lit 9527647) (nat_lit 1921776686) (nat_lit 0) D2M8K2.t4045 from rfl, totK_node, tot4044, tot4045]
  decide +kernel

theorem arows4037 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4037 = true := by
  rw [show D2M8K2.u4037 = KTree.node D2M8K2.t4046 (nat_lit 9529357) (nat_lit 978762866) (nat_lit 2) D2M8K2.t4047 from rfl, allE_node, rows4046, irow4037, rows4047]
  all_goals rfl

theorem atot4037 : totK PD2M8K2 D2M8K2.u4037 = [0, 0, 323364954001, 908344250713, 543548665711, 45100428834, 0, 0] := by
  rw [show D2M8K2.u4037 = KTree.node D2M8K2.t4046 (nat_lit 9529357) (nat_lit 978762866) (nat_lit 2) D2M8K2.t4047 from rfl, totK_node, tot4046, tot4047]
  decide +kernel

theorem arows4041 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4041 = true := by
  rw [show D2M8K2.u4041 = KTree.node D2M8K2.t4048 (nat_lit 9531165) (nat_lit 1561392632) (nat_lit 0) D2M8K2.t4049 from rfl, allE_node, rows4048, irow4041, rows4049]
  all_goals rfl

theorem atot4041 : totK PD2M8K2 D2M8K2.u4041 = [0, 0, 135903802350, 635963409030, 805481196994, 200647924496, 5218872685, 0] := by
  rw [show D2M8K2.u4041 = KTree.node D2M8K2.t4048 (nat_lit 9531165) (nat_lit 1561392632) (nat_lit 0) D2M8K2.t4049 from rfl, totK_node, tot4048, tot4049]
  decide +kernel

theorem arows4042 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4042 = true := by
  rw [show D2M8K2.u4042 = KTree.node D2M8K2.t4050 (nat_lit 9532611) (nat_lit 3644688201) (nat_lit 0) D2M8K2.t4051 from rfl, allE_node, rows4050, irow4042, rows4051]
  all_goals rfl

theorem atot4042 : totK PD2M8K2 D2M8K2.u4042 = [0, 0, 278653469980, 889296922895, 590106750437, 44577712955, 0, 0] := by
  rw [show D2M8K2.u4042 = KTree.node D2M8K2.t4050 (nat_lit 9532611) (nat_lit 3644688201) (nat_lit 0) D2M8K2.t4051 from rfl, totK_node, tot4050, tot4051]
  decide +kernel

theorem arows4044 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4044 = true := by
  rw [show D2M8K2.u4044 = KTree.node D2M8K2.t4052 (nat_lit 9534640) (nat_lit 3392280839) (nat_lit 0) D2M8K2.t4053 from rfl, allE_node, rows4052, irow4044, rows4053]
  all_goals rfl

theorem atot4044 : totK PD2M8K2 D2M8K2.u4044 = [0, 0, 157758791320, 722979786982, 810872400404, 144582980061, 1415142070, 0] := by
  rw [show D2M8K2.u4044 = KTree.node D2M8K2.t4052 (nat_lit 9534640) (nat_lit 3392280839) (nat_lit 0) D2M8K2.t4053 from rfl, totK_node, tot4052, tot4053]
  decide +kernel

theorem arows4045 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4045 = true := by
  rw [show D2M8K2.u4045 = KTree.node D2M8K2.t4054 (nat_lit 9536544) (nat_lit 3513329880) (nat_lit 0) D2M8K2.t4055 from rfl, allE_node, rows4054, irow4045, rows4055]
  all_goals rfl

theorem atot4045 : totK PD2M8K2 D2M8K2.u4045 = [0, 0, 265646355895, 880511199145, 614185024408, 57770526810, 0, 0] := by
  rw [show D2M8K2.u4045 = KTree.node D2M8K2.t4054 (nat_lit 9536544) (nat_lit 3513329880) (nat_lit 0) D2M8K2.t4055 from rfl, totK_node, tot4054, tot4055]
  decide +kernel

theorem arows4048 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4048 = true := by
  rw [show D2M8K2.u4048 = KTree.node D2M8K2.t4056 (nat_lit 9538408) (nat_lit 3774196079) (nat_lit 0) D2M8K2.t4057 from rfl, allE_node, rows4056, irow4048, rows4057]
  all_goals rfl

theorem atot4048 : totK PD2M8K2 D2M8K2.u4048 = [0, 159221153091, 377112284693, 376858713809, 610628426411, 241940454824, 9302370699, 0] := by
  rw [show D2M8K2.u4048 = KTree.node D2M8K2.t4056 (nat_lit 9538408) (nat_lit 3774196079) (nat_lit 0) D2M8K2.t4057 from rfl, totK_node, tot4056, tot4057]
  decide +kernel

theorem arows4049 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4049 = true := by
  rw [show D2M8K2.u4049 = KTree.node D2M8K2.t4058 (nat_lit 9540292) (nat_lit 3767302611) (nat_lit 0) D2M8K2.t4059 from rfl, allE_node, rows4058, irow4049, rows4059]
  all_goals rfl

theorem atot4049 : totK PD2M8K2 D2M8K2.u4049 = [0, 183615921856, 785482625929, 754882359478, 80613606899, 0, 0, 0] := by
  rw [show D2M8K2.u4049 = KTree.node D2M8K2.t4058 (nat_lit 9540292) (nat_lit 3767302611) (nat_lit 0) D2M8K2.t4059 from rfl, totK_node, tot4058, tot4059]
  decide +kernel

theorem arows4051 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4051 = true := by
  rw [show D2M8K2.u4051 = KTree.node D2M8K2.t4060 (nat_lit 9542906) (nat_lit 4242684642) (nat_lit 0) D2M8K2.t4061 from rfl, allE_node, rows4060, irow4051, rows4061]
  all_goals rfl

theorem atot4051 : totK PD2M8K2 D2M8K2.u4051 = [0, 374511795558, 932159641455, 493608733258, 41435152586, 0, 0, 0] := by
  rw [show D2M8K2.u4051 = KTree.node D2M8K2.t4060 (nat_lit 9542906) (nat_lit 4242684642) (nat_lit 0) D2M8K2.t4061 from rfl, totK_node, tot4060, tot4061]
  decide +kernel

theorem arows4052 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4052 = true := by
  rw [show D2M8K2.u4052 = KTree.node D2M8K2.t4062 (nat_lit 9544358) (nat_lit 4150634215) (nat_lit 0) D2M8K2.t4063 from rfl, allE_node, rows4062, irow4052, rows4063]
  all_goals rfl

theorem atot4052 : totK PD2M8K2 D2M8K2.u4052 = [0, 36516442283, 478572648147, 880365483577, 392546888476, 29387185185, 0, 0] := by
  rw [show D2M8K2.u4052 = KTree.node D2M8K2.t4062 (nat_lit 9544358) (nat_lit 4150634215) (nat_lit 0) D2M8K2.t4063 from rfl, totK_node, tot4062, tot4063]
  decide +kernel

theorem arows4057 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4057 = true := by
  rw [show D2M8K2.u4057 = KTree.node D2M8K2.t4064 (nat_lit 9545666) (nat_lit 3378556279) (nat_lit 0) D2M8K2.t4065 from rfl, allE_node, rows4064, irow4057, rows4065]
  all_goals rfl

theorem atot4057 : totK PD2M8K2 D2M8K2.u4057 = [0, 264749465480, 721549073720, 634405917148, 201099481447, 8209931632, 0, 0] := by
  rw [show D2M8K2.u4057 = KTree.node D2M8K2.t4064 (nat_lit 9545666) (nat_lit 3378556279) (nat_lit 0) D2M8K2.t4065 from rfl, totK_node, tot4064, tot4065]
  decide +kernel

theorem arows4058 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4058 = true := by
  rw [show D2M8K2.u4058 = KTree.node D2M8K2.t4066 (nat_lit 9547121) (nat_lit 1582786887) (nat_lit 0) D2M8K2.t4067 from rfl, allE_node, rows4066, irow4058, rows4067]
  all_goals rfl

theorem atot4058 : totK PD2M8K2 D2M8K2.u4058 = [0, 175351648363, 755145509393, 759261871037, 123577044228, 1164319620, 0, 0] := by
  rw [show D2M8K2.u4058 = KTree.node D2M8K2.t4066 (nat_lit 9547121) (nat_lit 1582786887) (nat_lit 0) D2M8K2.t4067 from rfl, totK_node, tot4066, tot4067]
  decide +kernel

theorem arows4060 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4060 = true := by
  rw [show D2M8K2.u4060 = KTree.node D2M8K2.t4068 (nat_lit 9552402) (nat_lit 2476751776) (nat_lit 0) D2M8K2.t4069 from rfl, allE_node, rows4068, irow4060, rows4069]
  all_goals rfl

theorem atot4060 : totK PD2M8K2 D2M8K2.u4060 = [0, 199531275971, 654375155411, 708839655654, 213037284423, 11885407614, 0, 0] := by
  rw [show D2M8K2.u4060 = KTree.node D2M8K2.t4068 (nat_lit 9552402) (nat_lit 2476751776) (nat_lit 0) D2M8K2.t4069 from rfl, totK_node, tot4068, tot4069]
  decide +kernel

theorem arows4061 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4061 = true := by
  rw [show D2M8K2.u4061 = KTree.node D2M8K2.t4070 (nat_lit 9553636) (nat_lit 3811867265) (nat_lit 0) D2M8K2.t4071 from rfl, allE_node, rows4070, irow4061, rows4071]
  all_goals rfl

theorem atot4061 : totK PD2M8K2 D2M8K2.u4061 = [0, 211162441403, 790028349276, 699496629597, 97029080709, 1096505104, 0, 0] := by
  rw [show D2M8K2.u4061 = KTree.node D2M8K2.t4070 (nat_lit 9553636) (nat_lit 3811867265) (nat_lit 0) D2M8K2.t4071 from rfl, totK_node, tot4070, tot4071]
  decide +kernel

theorem arows4064 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4064 = true := by
  rw [show D2M8K2.u4064 = KTree.node D2M8K2.t4072 (nat_lit 9555976) (nat_lit 3769889359) (nat_lit 0) D2M8K2.t4073 from rfl, allE_node, rows4072, irow4064, rows4073]
  all_goals rfl

theorem atot4064 : totK PD2M8K2 D2M8K2.u4064 = [0, 254890719727, 766776584677, 661891922976, 135832351910, 3884009855, 0, 0] := by
  rw [show D2M8K2.u4064 = KTree.node D2M8K2.t4072 (nat_lit 9555976) (nat_lit 3769889359) (nat_lit 0) D2M8K2.t4073 from rfl, totK_node, tot4072, tot4073]
  decide +kernel

theorem arows4065 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4065 = true := by
  rw [show D2M8K2.u4065 = KTree.node D2M8K2.t4074 (nat_lit 9557503) (nat_lit 2374013626) (nat_lit 0) D2M8K2.t4075 from rfl, allE_node, rows4074, irow4065, rows4075]
  all_goals rfl

theorem atot4065 : totK PD2M8K2 D2M8K2.u4065 = [0, 161409159507, 747322361146, 772328922752, 134678216071, 1268739303, 0, 0] := by
  rw [show D2M8K2.u4065 = KTree.node D2M8K2.t4074 (nat_lit 9557503) (nat_lit 2374013626) (nat_lit 0) D2M8K2.t4075 from rfl, totK_node, tot4074, tot4075]
  decide +kernel

theorem arows4067 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4067 = true := by
  rw [show D2M8K2.u4067 = KTree.node D2M8K2.t4076 (nat_lit 9559232) (nat_lit 1965459565) (nat_lit 0) D2M8K2.t4077 from rfl, allE_node, rows4076, irow4067, rows4077]
  all_goals rfl

theorem atot4067 : totK PD2M8K2 D2M8K2.u4067 = [0, 0, 345667362557, 935642921940, 459699327442, 29075628518, 0, 0] := by
  rw [show D2M8K2.u4067 = KTree.node D2M8K2.t4076 (nat_lit 9559232) (nat_lit 1965459565) (nat_lit 0) D2M8K2.t4077 from rfl, totK_node, tot4076, tot4077]
  decide +kernel

theorem arows4068 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4068 = true := by
  rw [show D2M8K2.u4068 = KTree.node D2M8K2.t4078 (nat_lit 9561146) (nat_lit 1933107067) (nat_lit 0) D2M8K2.t4079 from rfl, allE_node, rows4078, irow4068, rows4079]
  all_goals rfl

theorem atot4068 : totK PD2M8K2 D2M8K2.u4068 = [0, 0, 229572601235, 825706352766, 660023653674, 57502811150, 0, 0] := by
  rw [show D2M8K2.u4068 = KTree.node D2M8K2.t4078 (nat_lit 9561146) (nat_lit 1933107067) (nat_lit 0) D2M8K2.t4079 from rfl, totK_node, tot4078, tot4079]
  decide +kernel

theorem arows4072 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4072 = true := by
  rw [show D2M8K2.u4072 = KTree.node D2M8K2.t4080 (nat_lit 9563787) (nat_lit 3736031856) (nat_lit 0) D2M8K2.t4081 from rfl, allE_node, rows4080, irow4072, rows4081]
  all_goals rfl

theorem atot4072 : totK PD2M8K2 D2M8K2.u4072 = [0, 0, 336317946543, 938213210415, 516596661672, 39604713226, 0, 0] := by
  rw [show D2M8K2.u4072 = KTree.node D2M8K2.t4080 (nat_lit 9563787) (nat_lit 3736031856) (nat_lit 0) D2M8K2.t4081 from rfl, totK_node, tot4080, tot4081]
  decide +kernel

theorem arows4073 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4073 = true := by
  rw [show D2M8K2.u4073 = KTree.node D2M8K2.t4082 (nat_lit 9566767) (nat_lit 1834426229) (nat_lit 0) D2M8K2.t4083 from rfl, allE_node, rows4082, irow4073, rows4083]
  all_goals rfl

theorem atot4073 : totK PD2M8K2 D2M8K2.u4073 = [0, 0, 357974379145, 928864123644, 482524453624, 36060699458, 0, 0] := by
  rw [show D2M8K2.u4073 = KTree.node D2M8K2.t4082 (nat_lit 9566767) (nat_lit 1834426229) (nat_lit 0) D2M8K2.t4083 from rfl, totK_node, tot4082, tot4083]
  decide +kernel

theorem arows4075 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4075 = true := by
  rw [show D2M8K2.u4075 = KTree.node D2M8K2.t4084 (nat_lit 9568328) (nat_lit 3872593837) (nat_lit 0) D2M8K2.t4085 from rfl, allE_node, rows4084, irow4075, rows4085]
  all_goals rfl

theorem atot4075 : totK PD2M8K2 D2M8K2.u4075 = [0, 0, 77611112426, 567166128388, 845208945038, 246260957320, 9072174562, 0] := by
  rw [show D2M8K2.u4075 = KTree.node D2M8K2.t4084 (nat_lit 9568328) (nat_lit 3872593837) (nat_lit 0) D2M8K2.t4085 from rfl, totK_node, tot4084, tot4085]
  decide +kernel

theorem arows4076 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4076 = true := by
  rw [show D2M8K2.u4076 = KTree.node D2M8K2.t4086 (nat_lit 9573621) (nat_lit 1127566079) (nat_lit 0) D2M8K2.t4087 from rfl, allE_node, rows4086, irow4076, rows4087]
  all_goals rfl

theorem atot4076 : totK PD2M8K2 D2M8K2.u4076 = [0, 0, 336067799401, 922336249086, 501837301982, 36768349441, 0, 0] := by
  rw [show D2M8K2.u4076 = KTree.node D2M8K2.t4086 (nat_lit 9573621) (nat_lit 1127566079) (nat_lit 0) D2M8K2.t4087 from rfl, totK_node, tot4086, tot4087]
  decide +kernel

theorem arows4079 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4079 = true := by
  rw [show D2M8K2.u4079 = KTree.node D2M8K2.t4088 (nat_lit 9575444) (nat_lit 3106372352) (nat_lit 0) D2M8K2.t4089 from rfl, allE_node, rows4088, irow4079, rows4089]
  all_goals rfl

theorem atot4079 : totK PD2M8K2 D2M8K2.u4079 = [0, 0, 138410390292, 691990424189, 768806086390, 130999965619, 2340352732, 0] := by
  rw [show D2M8K2.u4079 = KTree.node D2M8K2.t4088 (nat_lit 9575444) (nat_lit 3106372352) (nat_lit 0) D2M8K2.t4089 from rfl, totK_node, tot4088, tot4089]
  decide +kernel

theorem arows4080 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4080 = true := by
  rw [show D2M8K2.u4080 = KTree.node D2M8K2.t4090 (nat_lit 9577295) (nat_lit 2771375578) (nat_lit 0) D2M8K2.t4091 from rfl, allE_node, rows4090, irow4080, rows4091]
  all_goals rfl

theorem atot4080 : totK PD2M8K2 D2M8K2.u4080 = [0, 0, 342700875225, 942138172522, 507511323309, 33222090786, 0, 0] := by
  rw [show D2M8K2.u4080 = KTree.node D2M8K2.t4090 (nat_lit 9577295) (nat_lit 2771375578) (nat_lit 0) D2M8K2.t4091 from rfl, totK_node, tot4090, tot4091]
  decide +kernel

theorem arows4082 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4082 = true := by
  rw [show D2M8K2.u4082 = KTree.node D2M8K2.t4092 (nat_lit 9581215) (nat_lit 2304413796) (nat_lit 0) D2M8K2.t4093 from rfl, allE_node, rows4092, irow4082, rows4093]
  all_goals rfl

theorem atot4082 : totK PD2M8K2 D2M8K2.u4082 = [0, 323005806339, 879668381779, 503460627724, 79407803863, 9433566158, 0, 0] := by
  rw [show D2M8K2.u4082 = KTree.node D2M8K2.t4092 (nat_lit 9581215) (nat_lit 2304413796) (nat_lit 0) D2M8K2.t4093 from rfl, totK_node, tot4092, tot4093]
  decide +kernel

theorem arows4083 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4083 = true := by
  rw [show D2M8K2.u4083 = KTree.node D2M8K2.t4094 (nat_lit 9583873) (nat_lit 1133678816) (nat_lit 0) D2M8K2.t4095 from rfl, allE_node, rows4094, irow4083, rows4095]
  all_goals rfl

theorem atot4083 : totK PD2M8K2 D2M8K2.u4083 = [0, 241054195557, 810289328284, 713196094399, 83810626589, 0, 0, 0] := by
  rw [show D2M8K2.u4083 = KTree.node D2M8K2.t4094 (nat_lit 9583873) (nat_lit 1133678816) (nat_lit 0) D2M8K2.t4095 from rfl, totK_node, tot4094, tot4095]
  decide +kernel

theorem arows4095 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4095 = true := by
  rw [show D2M8K2.u4095 = KTree.node D2M8K2.t4096 (nat_lit 9585076) (nat_lit 3019288231) (nat_lit 0) D2M8K2.t4097 from rfl, allE_node, rows4096, irow4095, rows4097]
  all_goals rfl

theorem atot4095 : totK PD2M8K2 D2M8K2.u4095 = [0, 189993146895, 731468608193, 677022523455, 208691688135, 21393864572, 0, 0] := by
  rw [show D2M8K2.u4095 = KTree.node D2M8K2.t4096 (nat_lit 9585076) (nat_lit 3019288231) (nat_lit 0) D2M8K2.t4097 from rfl, totK_node, tot4096, tot4097]
  decide +kernel

theorem arows4096 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4096 = true := by
  rw [show D2M8K2.u4096 = KTree.node D2M8K2.t4098 (nat_lit 9586585) (nat_lit 1282965558) (nat_lit 0) D2M8K2.t4099 from rfl, allE_node, rows4098, irow4096, rows4099]
  all_goals rfl

theorem atot4096 : totK PD2M8K2 D2M8K2.u4096 = [0, 101459537549, 483256019416, 822605942986, 372674846278, 16201225427, 0, 0] := by
  rw [show D2M8K2.u4096 = KTree.node D2M8K2.t4098 (nat_lit 9586585) (nat_lit 1282965558) (nat_lit 0) D2M8K2.t4099 from rfl, totK_node, tot4098, tot4099]
  decide +kernel

theorem arows4098 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4098 = true := by
  rw [show D2M8K2.u4098 = KTree.node D2M8K2.t4100 (nat_lit 9591538) (nat_lit 4109470449) (nat_lit 0) D2M8K2.t4101 from rfl, allE_node, rows4100, irow4098, rows4101]
  all_goals rfl

theorem atot4098 : totK PD2M8K2 D2M8K2.u4098 = [0, 338815762882, 921709937844, 535177358336, 47649494496, 0, 0, 0] := by
  rw [show D2M8K2.u4098 = KTree.node D2M8K2.t4100 (nat_lit 9591538) (nat_lit 4109470449) (nat_lit 0) D2M8K2.t4101 from rfl, totK_node, tot4100, tot4101]
  decide +kernel

theorem arows4099 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4099 = true := by
  rw [show D2M8K2.u4099 = KTree.node D2M8K2.t4102 (nat_lit 9593209) (nat_lit 1425751637) (nat_lit 0) D2M8K2.t4103 from rfl, allE_node, rows4102, irow4099, rows4103]
  all_goals rfl

theorem atot4099 : totK PD2M8K2 D2M8K2.u4099 = [0, 50692750027, 493382554454, 924166189608, 300878776662, 13250685261, 0, 0] := by
  rw [show D2M8K2.u4099 = KTree.node D2M8K2.t4102 (nat_lit 9593209) (nat_lit 1425751637) (nat_lit 0) D2M8K2.t4103 from rfl, totK_node, tot4102, tot4103]
  decide +kernel

theorem arows4102 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4102 = true := by
  rw [show D2M8K2.u4102 = KTree.node D2M8K2.t4104 (nat_lit 9594583) (nat_lit 1123296044) (nat_lit 0) D2M8K2.t4105 from rfl, allE_node, rows4104, irow4102, rows4105]
  all_goals rfl

theorem atot4102 : totK PD2M8K2 D2M8K2.u4102 = [0, 356800739135, 922787828562, 498194921975, 40267308837, 0, 0, 0] := by
  rw [show D2M8K2.u4102 = KTree.node D2M8K2.t4104 (nat_lit 9594583) (nat_lit 1123296044) (nat_lit 0) D2M8K2.t4105 from rfl, totK_node, tot4104, tot4105]
  decide +kernel

theorem arows4103 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4103 = true := by
  rw [show D2M8K2.u4103 = KTree.node D2M8K2.t4106 (nat_lit 9596476) (nat_lit 3058323271) (nat_lit 0) D2M8K2.t4107 from rfl, allE_node, rows4106, irow4103, rows4107]
  all_goals rfl

theorem atot4103 : totK PD2M8K2 D2M8K2.u4103 = [0, 77035357472, 624510037208, 885831780669, 195331989787, 4980514959, 0, 0] := by
  rw [show D2M8K2.u4103 = KTree.node D2M8K2.t4106 (nat_lit 9596476) (nat_lit 3058323271) (nat_lit 0) D2M8K2.t4107 from rfl, totK_node, tot4106, tot4107]
  decide +kernel

theorem arows4105 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4105 = true := by
  rw [show D2M8K2.u4105 = KTree.node D2M8K2.t4108 (nat_lit 9598189) (nat_lit 1382786610) (nat_lit 0) D2M8K2.t4109 from rfl, allE_node, rows4108, irow4105, rows4109]
  all_goals rfl

theorem atot4105 : totK PD2M8K2 D2M8K2.u4105 = [0, 339347743896, 920070526260, 538652825838, 48623107717, 0, 0, 0] := by
  rw [show D2M8K2.u4105 = KTree.node D2M8K2.t4108 (nat_lit 9598189) (nat_lit 1382786610) (nat_lit 0) D2M8K2.t4109 from rfl, totK_node, tot4108, tot4109]
  decide +kernel

theorem arows4106 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4106 = true := by
  rw [show D2M8K2.u4106 = KTree.node D2M8K2.t4110 (nat_lit 9599904) (nat_lit 3686859352) (nat_lit 0) D2M8K2.t4111 from rfl, allE_node, rows4110, irow4106, rows4111]
  all_goals rfl

theorem atot4106 : totK PD2M8K2 D2M8K2.u4106 = [0, 0, 415481781539, 960910446422, 386106951460, 20539705592, 0, 0] := by
  rw [show D2M8K2.u4106 = KTree.node D2M8K2.t4110 (nat_lit 9599904) (nat_lit 3686859352) (nat_lit 0) D2M8K2.t4111 from rfl, totK_node, tot4110, tot4111]
  decide +kernel

theorem arows4110 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4110 = true := by
  rw [show D2M8K2.u4110 = KTree.node D2M8K2.t4112 (nat_lit 9602011) (nat_lit 2237630558) (nat_lit 0) D2M8K2.t4113 from rfl, allE_node, rows4112, irow4110, rows4113]
  all_goals rfl

theorem atot4110 : totK PD2M8K2 D2M8K2.u4110 = [0, 0, 303551103569, 912987490561, 528595182324, 31397621993, 0, 0] := by
  rw [show D2M8K2.u4110 = KTree.node D2M8K2.t4112 (nat_lit 9602011) (nat_lit 2237630558) (nat_lit 0) D2M8K2.t4113 from rfl, totK_node, tot4112, tot4113]
  decide +kernel

theorem arows4111 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4111 = true := by
  rw [show D2M8K2.u4111 = KTree.node D2M8K2.t4114 (nat_lit 9604716) (nat_lit 1119948283) (nat_lit 0) D2M8K2.t4115 from rfl, allE_node, rows4114, irow4111, rows4115]
  all_goals rfl

theorem atot4111 : totK PD2M8K2 D2M8K2.u4111 = [0, 0, 255527943874, 852865955866, 656075952530, 65030082907, 0, 0] := by
  rw [show D2M8K2.u4111 = KTree.node D2M8K2.t4114 (nat_lit 9604716) (nat_lit 1119948283) (nat_lit 0) D2M8K2.t4115 from rfl, totK_node, tot4114, tot4115]
  decide +kernel

theorem arows4113 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4113 = true := by
  rw [show D2M8K2.u4113 = KTree.node D2M8K2.t4116 (nat_lit 9611140) (nat_lit 2499269714) (nat_lit 0) D2M8K2.t4117 from rfl, allE_node, rows4116, irow4113, rows4117]
  all_goals rfl

theorem atot4113 : totK PD2M8K2 D2M8K2.u4113 = [0, 0, 369972893123, 930374967094, 479615337716, 36485206293, 0, 0] := by
  rw [show D2M8K2.u4113 = KTree.node D2M8K2.t4116 (nat_lit 9611140) (nat_lit 2499269714) (nat_lit 0) D2M8K2.t4117 from rfl, totK_node, tot4116, tot4117]
  decide +kernel

theorem arows4114 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4114 = true := by
  rw [show D2M8K2.u4114 = KTree.node D2M8K2.t4118 (nat_lit 9612621) (nat_lit 1272940039) (nat_lit 0) D2M8K2.t4119 from rfl, allE_node, rows4118, irow4114, rows4119]
  all_goals rfl

theorem atot4114 : totK PD2M8K2 D2M8K2.u4114 = [0, 0, 242862605968, 817589394407, 651919044361, 80268119773, 0, 0] := by
  rw [show D2M8K2.u4114 = KTree.node D2M8K2.t4118 (nat_lit 9612621) (nat_lit 1272940039) (nat_lit 0) D2M8K2.t4119 from rfl, totK_node, tot4118, tot4119]
  decide +kernel

theorem arows4117 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4117 = true := by
  rw [show D2M8K2.u4117 = KTree.node D2M8K2.t4120 (nat_lit 9614338) (nat_lit 4046412260) (nat_lit 0) D2M8K2.t4121 from rfl, allE_node, rows4120, irow4117, rows4121]
  all_goals rfl

theorem atot4117 : totK PD2M8K2 D2M8K2.u4117 = [0, 0, 163281325637, 664044064451, 717407957429, 206149125483, 9135329004, 0] := by
  rw [show D2M8K2.u4117 = KTree.node D2M8K2.t4120 (nat_lit 9614338) (nat_lit 4046412260) (nat_lit 0) D2M8K2.t4121 from rfl, totK_node, tot4120, tot4121]
  decide +kernel

theorem arows4118 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4118 = true := by
  rw [show D2M8K2.u4118 = KTree.node D2M8K2.t4122 (nat_lit 9615795) (nat_lit 3595489035) (nat_lit 0) D2M8K2.t4123 from rfl, allE_node, rows4122, irow4118, rows4123]
  all_goals rfl

theorem atot4118 : totK PD2M8K2 D2M8K2.u4118 = [0, 0, 246407789312, 846146230853, 631343485121, 55787216421, 0, 0] := by
  rw [show D2M8K2.u4118 = KTree.node D2M8K2.t4122 (nat_lit 9615795) (nat_lit 3595489035) (nat_lit 0) D2M8K2.t4123 from rfl, totK_node, tot4122, tot4123]
  decide +kernel

theorem arows4120 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4120 = true := by
  rw [show D2M8K2.u4120 = KTree.node D2M8K2.t4124 (nat_lit 9618193) (nat_lit 1557510902) (nat_lit 0) D2M8K2.t4125 from rfl, allE_node, rows4124, irow4120, rows4125]
  all_goals rfl

theorem atot4120 : totK PD2M8K2 D2M8K2.u4120 = [0, 0, 234306229341, 771516130536, 652776795109, 113176950833, 2417524611, 0] := by
  rw [show D2M8K2.u4120 = KTree.node D2M8K2.t4124 (nat_lit 9618193) (nat_lit 1557510902) (nat_lit 0) D2M8K2.t4125 from rfl, totK_node, tot4124, tot4125]
  decide +kernel

theorem arows4121 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4121 = true := by
  rw [show D2M8K2.u4121 = KTree.node D2M8K2.t4126 (nat_lit 9619724) (nat_lit 1442715125) (nat_lit 0) D2M8K2.t4127 from rfl, allE_node, rows4126, irow4121, rows4127]
  all_goals rfl

theorem atot4121 : totK PD2M8K2 D2M8K2.u4121 = [0, 190813401391, 622783582971, 666081671432, 294075231083, 24133031181, 0, 0] := by
  rw [show D2M8K2.u4121 = KTree.node D2M8K2.t4126 (nat_lit 9619724) (nat_lit 1442715125) (nat_lit 0) D2M8K2.t4127 from rfl, totK_node, tot4126, tot4127]
  decide +kernel

theorem arows4126 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4126 = true := by
  rw [show D2M8K2.u4126 = KTree.node D2M8K2.t4128 (nat_lit 9623341) (nat_lit 1131131107) (nat_lit 0) D2M8K2.t4129 from rfl, allE_node, rows4128, irow4126, rows4129]
  all_goals rfl

theorem atot4126 : totK PD2M8K2 D2M8K2.u4126 = [0, 203853385935, 814775844618, 714799263403, 72620562755, 0, 0, 0] := by
  rw [show D2M8K2.u4126 = KTree.node D2M8K2.t4128 (nat_lit 9623341) (nat_lit 1131131107) (nat_lit 0) D2M8K2.t4129 from rfl, totK_node, tot4128, tot4129]
  decide +kernel

theorem arows4127 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4127 = true := by
  rw [show D2M8K2.u4127 = KTree.node D2M8K2.t4130 (nat_lit 9625932) (nat_lit 2939332927) (nat_lit 0) D2M8K2.t4131 from rfl, allE_node, rows4130, irow4127, rows4131]
  all_goals rfl

theorem atot4127 : totK PD2M8K2 D2M8K2.u4127 = [0, 349009718210, 926767523623, 518156810112, 42869104198, 0, 0, 0] := by
  rw [show D2M8K2.u4127 = KTree.node D2M8K2.t4130 (nat_lit 9625932) (nat_lit 2939332927) (nat_lit 0) D2M8K2.t4131 from rfl, totK_node, tot4130, tot4131]
  decide +kernel

theorem arows4129 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4129 = true := by
  rw [show D2M8K2.u4129 = KTree.node D2M8K2.t4132 (nat_lit 9627406) (nat_lit 3927471630) (nat_lit 0) D2M8K2.t4133 from rfl, allE_node, rows4132, irow4129, rows4133]
  all_goals rfl

theorem atot4129 : totK PD2M8K2 D2M8K2.u4129 = [0, 0, 413593154289, 948592863652, 422360620384, 29391110695, 0, 0] := by
  rw [show D2M8K2.u4129 = KTree.node D2M8K2.t4132 (nat_lit 9627406) (nat_lit 3927471630) (nat_lit 0) D2M8K2.t4133 from rfl, totK_node, tot4132, tot4133]
  decide +kernel

theorem arows4130 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4130 = true := by
  rw [show D2M8K2.u4130 = KTree.node D2M8K2.t4134 (nat_lit 9628766) (nat_lit 3939444844) (nat_lit 0) D2M8K2.t4135 from rfl, allE_node, rows4134, irow4130, rows4135]
  all_goals rfl

theorem atot4130 : totK PD2M8K2 D2M8K2.u4130 = [0, 280872432327, 758361509366, 584158124987, 177900764404, 8210597527, 0, 0] := by
  rw [show D2M8K2.u4130 = KTree.node D2M8K2.t4134 (nat_lit 9628766) (nat_lit 3939444844) (nat_lit 0) D2M8K2.t4135 from rfl, totK_node, tot4134, tot4135]
  decide +kernel

theorem arows4133 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4133 = true := by
  rw [show D2M8K2.u4133 = KTree.node D2M8K2.t4136 (nat_lit 9630275) (nat_lit 2879316947) (nat_lit 0) D2M8K2.t4137 from rfl, allE_node, rows4136, irow4133, rows4137]
  all_goals rfl

theorem atot4133 : totK PD2M8K2 D2M8K2.u4133 = [0, 131749273644, 658205868587, 797631387912, 198508937587, 9587713104, 0, 0] := by
  rw [show D2M8K2.u4133 = KTree.node D2M8K2.t4136 (nat_lit 9630275) (nat_lit 2879316947) (nat_lit 0) D2M8K2.t4137 from rfl, totK_node, tot4136, tot4137]
  decide +kernel

theorem arows4134 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4134 = true := by
  rw [show D2M8K2.u4134 = KTree.node D2M8K2.t4138 (nat_lit 9632201) (nat_lit 1747102028) (nat_lit 0) D2M8K2.t4139 from rfl, allE_node, rows4138, irow4134, rows4139]
  all_goals rfl

theorem atot4134 : totK PD2M8K2 D2M8K2.u4134 = [0, 256038984625, 776812758651, 641352410475, 123121391376, 3462014130, 0, 0] := by
  rw [show D2M8K2.u4134 = KTree.node D2M8K2.t4138 (nat_lit 9632201) (nat_lit 1747102028) (nat_lit 0) D2M8K2.t4139 from rfl, totK_node, tot4138, tot4139]
  decide +kernel

theorem arows4136 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4136 = true := by
  rw [show D2M8K2.u4136 = KTree.node D2M8K2.t4140 (nat_lit 9633701) (nat_lit 2063893156) (nat_lit 0) D2M8K2.t4141 from rfl, allE_node, rows4140, irow4136, rows4141]
  all_goals rfl

theorem atot4136 : totK PD2M8K2 D2M8K2.u4136 = [0, 153125176227, 662580304767, 764277399084, 205071014652, 9668735432, 0, 0] := by
  rw [show D2M8K2.u4136 = KTree.node D2M8K2.t4140 (nat_lit 9633701) (nat_lit 2063893156) (nat_lit 0) D2M8K2.t4141 from rfl, totK_node, tot4140, tot4141]
  decide +kernel

theorem arows4137 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4137 = true := by
  rw [show D2M8K2.u4137 = KTree.node D2M8K2.t4142 (nat_lit 9635554) (nat_lit 3230958882) (nat_lit 0) D2M8K2.t4143 from rfl, allE_node, rows4142, irow4137, rows4143]
  all_goals rfl

theorem atot4137 : totK PD2M8K2 D2M8K2.u4137 = [0, 257874672001, 773068071362, 646387853751, 128589956528, 3581949829, 0, 0] := by
  rw [show D2M8K2.u4137 = KTree.node D2M8K2.t4142 (nat_lit 9635554) (nat_lit 3230958882) (nat_lit 0) D2M8K2.t4143 from rfl, totK_node, tot4142, tot4143]
  decide +kernel

theorem arows4141 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4141 = true := by
  rw [show D2M8K2.u4141 = KTree.node D2M8K2.t4144 (nat_lit 9636727) (nat_lit 2258536135) (nat_lit 0) D2M8K2.t4145 from rfl, allE_node, rows4144, irow4141, rows4145]
  all_goals rfl

theorem atot4141 : totK PD2M8K2 D2M8K2.u4141 = [0, 180183318095, 770462881447, 753108352418, 109416318744, 1096505104, 0, 0] := by
  rw [show D2M8K2.u4141 = KTree.node D2M8K2.t4144 (nat_lit 9636727) (nat_lit 2258536135) (nat_lit 0) D2M8K2.t4145 from rfl, totK_node, tot4144, tot4145]
  decide +kernel

theorem arows4142 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4142 = true := by
  rw [show D2M8K2.u4142 = KTree.node D2M8K2.t4146 (nat_lit 9642486) (nat_lit 3674576289) (nat_lit 0) D2M8K2.t4147 from rfl, allE_node, rows4146, irow4142, rows4147]
  all_goals rfl

theorem atot4142 : totK PD2M8K2 D2M8K2.u4142 = [0, 0, 411821754036, 951043604137, 376789497673, 22145572651, 0, 0] := by
  rw [show D2M8K2.u4142 = KTree.node D2M8K2.t4146 (nat_lit 9642486) (nat_lit 3674576289) (nat_lit 0) D2M8K2.t4147 from rfl, totK_node, tot4146, tot4147]
  decide +kernel

theorem arows4144 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4144 = true := by
  rw [show D2M8K2.u4144 = KTree.node D2M8K2.t4148 (nat_lit 9644959) (nat_lit 2336849049) (nat_lit 0) D2M8K2.t4149 from rfl, allE_node, rows4148, irow4144, rows4149]
  all_goals rfl

theorem atot4144 : totK PD2M8K2 D2M8K2.u4144 = [0, 0, 214812465193, 822241070800, 683508102825, 68469633744, 0, 0] := by
  rw [show D2M8K2.u4144 = KTree.node D2M8K2.t4148 (nat_lit 9644959) (nat_lit 2336849049) (nat_lit 0) D2M8K2.t4149 from rfl, totK_node, tot4148, tot4149]
  decide +kernel

theorem arows4145 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4145 = true := by
  rw [show D2M8K2.u4145 = KTree.node D2M8K2.t4150 (nat_lit 9646952) (nat_lit 3942464715) (nat_lit 0) D2M8K2.t4151 from rfl, allE_node, rows4150, irow4145, rows4151]
  all_goals rfl

theorem atot4145 : totK PD2M8K2 D2M8K2.u4145 = [0, 0, 349085317359, 955313721643, 454414913028, 25702417828, 0, 0] := by
  rw [show D2M8K2.u4145 = KTree.node D2M8K2.t4150 (nat_lit 9646952) (nat_lit 3942464715) (nat_lit 0) D2M8K2.t4151 from rfl, totK_node, tot4150, tot4151]
  decide +kernel

theorem arows4148 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4148 = true := by
  rw [show D2M8K2.u4148 = KTree.node D2M8K2.t4152 (nat_lit 9650304) (nat_lit 3686533672) (nat_lit 0) D2M8K2.t4153 from rfl, allE_node, rows4152, irow4148, rows4153]
  all_goals rfl

theorem atot4148 : totK PD2M8K2 D2M8K2.u4148 = [0, 0, 398789629476, 947384967026, 447346730673, 24537643821, 0, 0] := by
  rw [show D2M8K2.u4148 = KTree.node D2M8K2.t4152 (nat_lit 9650304) (nat_lit 3686533672) (nat_lit 0) D2M8K2.t4153 from rfl, totK_node, tot4152, tot4153]
  decide +kernel

theorem arows4149 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4149 = true := by
  rw [show D2M8K2.u4149 = KTree.node D2M8K2.t4154 (nat_lit 9653622) (nat_lit 3827012122) (nat_lit 0) D2M8K2.t4155 from rfl, allE_node, rows4154, irow4149, rows4155]
  all_goals rfl

theorem atot4149 : totK PD2M8K2 D2M8K2.u4149 = [0, 0, 350062404084, 953912670291, 480591703064, 25911449626, 0, 0] := by
  rw [show D2M8K2.u4149 = KTree.node D2M8K2.t4154 (nat_lit 9653622) (nat_lit 3827012122) (nat_lit 0) D2M8K2.t4155 from rfl, totK_node, tot4154, tot4155]
  decide +kernel

theorem arows4151 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4151 = true := by
  rw [show D2M8K2.u4151 = KTree.node D2M8K2.t4156 (nat_lit 9656660) (nat_lit 3232123941) (nat_lit 0) D2M8K2.t4157 from rfl, allE_node, rows4156, irow4151, rows4157]
  all_goals rfl

theorem atot4151 : totK PD2M8K2 D2M8K2.u4151 = [0, 0, 380817925223, 930154230226, 448968385472, 32547243808, 0, 0] := by
  rw [show D2M8K2.u4151 = KTree.node D2M8K2.t4156 (nat_lit 9656660) (nat_lit 3232123941) (nat_lit 0) D2M8K2.t4157 from rfl, totK_node, tot4156, tot4157]
  decide +kernel

theorem arows4152 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4152 = true := by
  rw [show D2M8K2.u4152 = KTree.node D2M8K2.t4158 (nat_lit 9658372) (nat_lit 3806624988) (nat_lit 0) D2M8K2.t4159 from rfl, allE_node, rows4158, irow4152, rows4159]
  all_goals rfl

theorem atot4152 : totK PD2M8K2 D2M8K2.u4152 = [0, 28842453189, 90160701577, 619482115524, 836285310051, 176772209528, 2586295899, 0] := by
  rw [show D2M8K2.u4152 = KTree.node D2M8K2.t4158 (nat_lit 9658372) (nat_lit 3806624988) (nat_lit 0) D2M8K2.t4159 from rfl, totK_node, tot4158, tot4159]
  decide +kernel

theorem arows4158 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4158 = true := by
  rw [show D2M8K2.u4158 = KTree.node D2M8K2.t4160 (nat_lit 9663984) (nat_lit 3693311653) (nat_lit 0) D2M8K2.t4161 from rfl, allE_node, rows4160, irow4158, rows4161]
  all_goals rfl

theorem atot4158 : totK PD2M8K2 D2M8K2.u4158 = [0, 293100253625, 901775279409, 572779599439, 45124199736, 0, 0, 0] := by
  rw [show D2M8K2.u4158 = KTree.node D2M8K2.t4160 (nat_lit 9663984) (nat_lit 3693311653) (nat_lit 0) D2M8K2.t4161 from rfl, totK_node, tot4160, tot4161]
  decide +kernel

theorem arows4159 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4159 = true := by
  rw [show D2M8K2.u4159 = KTree.node D2M8K2.t4162 (nat_lit 9666902) (nat_lit 4150964372) (nat_lit 0) D2M8K2.t4163 from rfl, allE_node, rows4162, irow4159, rows4163]
  all_goals rfl

theorem atot4159 : totK PD2M8K2 D2M8K2.u4159 = [0, 268379818248, 827835258090, 672570445912, 78438518981, 0, 0, 0] := by
  rw [show D2M8K2.u4159 = KTree.node D2M8K2.t4162 (nat_lit 9666902) (nat_lit 4150964372) (nat_lit 0) D2M8K2.t4163 from rfl, totK_node, tot4162, tot4163]
  decide +kernel

theorem arows4161 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4161 = true := by
  rw [show D2M8K2.u4161 = KTree.node D2M8K2.t4164 (nat_lit 9668097) (nat_lit 1427785407) (nat_lit 0) D2M8K2.t4165 from rfl, allE_node, rows4164, irow4161, rows4165]
  all_goals rfl

theorem atot4161 : totK PD2M8K2 D2M8K2.u4161 = [0, 162975290697, 683896157028, 730915459599, 237592306340, 21391863750, 0, 0] := by
  rw [show D2M8K2.u4161 = KTree.node D2M8K2.t4164 (nat_lit 9668097) (nat_lit 1427785407) (nat_lit 0) D2M8K2.t4165 from rfl, totK_node, tot4164, tot4165]
  decide +kernel

theorem arows4162 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4162 = true := by
  rw [show D2M8K2.u4162 = KTree.node D2M8K2.t4166 (nat_lit 9669634) (nat_lit 4091617113) (nat_lit 0) D2M8K2.t4167 from rfl, allE_node, rows4166, irow4162, rows4167]
  all_goals rfl

theorem atot4162 : totK PD2M8K2 D2M8K2.u4162 = [0, 146733090398, 541573244562, 756884414314, 340530377158, 16197583040, 0, 0] := by
  rw [show D2M8K2.u4162 = KTree.node D2M8K2.t4166 (nat_lit 9669634) (nat_lit 4091617113) (nat_lit 0) D2M8K2.t4167 from rfl, totK_node, tot4166, tot4167]
  decide +kernel

theorem arows4165 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4165 = true := by
  rw [show D2M8K2.u4165 = KTree.node D2M8K2.t4168 (nat_lit 9671136) (nat_lit 3246055448) (nat_lit 0) D2M8K2.t4169 from rfl, allE_node, rows4168, irow4165, rows4169]
  all_goals rfl

theorem atot4165 : totK PD2M8K2 D2M8K2.u4165 = [0, 267502257078, 845291800336, 621685636578, 80408317102, 1164319620, 0, 0] := by
  rw [show D2M8K2.u4165 = KTree.node D2M8K2.t4168 (nat_lit 9671136) (nat_lit 3246055448) (nat_lit 0) D2M8K2.t4169 from rfl, totK_node, tot4168, tot4169]
  decide +kernel

theorem arows4166 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4166 = true := by
  rw [show D2M8K2.u4166 = KTree.node D2M8K2.t4170 (nat_lit 9672866) (nat_lit 3990335714) (nat_lit 0) D2M8K2.t4171 from rfl, allE_node, rows4170, irow4166, rows4171]
  all_goals rfl

theorem atot4166 : totK PD2M8K2 D2M8K2.u4166 = [0, 130141355245, 601685872396, 815227717540, 242829866887, 10451052283, 0, 0] := by
  rw [show D2M8K2.u4166 = KTree.node D2M8K2.t4170 (nat_lit 9672866) (nat_lit 3990335714) (nat_lit 0) D2M8K2.t4171 from rfl, totK_node, tot4170, tot4171]
  decide +kernel

theorem arows4168 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4168 = true := by
  rw [show D2M8K2.u4168 = KTree.node D2M8K2.t4172 (nat_lit 9674570) (nat_lit 4000223268) (nat_lit 0) D2M8K2.t4173 from rfl, allE_node, rows4172, irow4168, rows4173]
  all_goals rfl

theorem atot4168 : totK PD2M8K2 D2M8K2.u4168 = [0, 284343447621, 870527724519, 612507984017, 61202221889, 0, 0, 0] := by
  rw [show D2M8K2.u4168 = KTree.node D2M8K2.t4172 (nat_lit 9674570) (nat_lit 4000223268) (nat_lit 0) D2M8K2.t4173 from rfl, totK_node, tot4172, tot4173]
  decide +kernel

theorem arows4169 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4169 = true := by
  rw [show D2M8K2.u4169 = KTree.node D2M8K2.t4174 (nat_lit 9676296) (nat_lit 3280908450) (nat_lit 0) D2M8K2.t4175 from rfl, allE_node, rows4174, irow4169, rows4175]
  all_goals rfl

theorem atot4169 : totK PD2M8K2 D2M8K2.u4169 = [0, 102225942908, 577132309388, 832148707365, 271764002229, 11775199386, 0, 0] := by
  rw [show D2M8K2.u4169 = KTree.node D2M8K2.t4174 (nat_lit 9676296) (nat_lit 3280908450) (nat_lit 0) D2M8K2.t4175 from rfl, totK_node, tot4174, tot4175]
  decide +kernel

theorem arows4173 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4173 = true := by
  rw [show D2M8K2.u4173 = KTree.node D2M8K2.t4176 (nat_lit 9681138) (nat_lit 3433520064) (nat_lit 0) D2M8K2.t4177 from rfl, allE_node, rows4176, irow4173, rows4177]
  all_goals rfl

theorem atot4173 : totK PD2M8K2 D2M8K2.u4173 = [0, 340088530745, 911374744227, 542884048845, 51904182268, 0, 0, 0] := by
  rw [show D2M8K2.u4173 = KTree.node D2M8K2.t4176 (nat_lit 9681138) (nat_lit 3433520064) (nat_lit 0) D2M8K2.t4177 from rfl, totK_node, tot4176, tot4177]
  decide +kernel

theorem arows4174 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4174 = true := by
  rw [show D2M8K2.u4174 = KTree.node D2M8K2.t4178 (nat_lit 9682753) (nat_lit 1393479757) (nat_lit 0) D2M8K2.t4179 from rfl, allE_node, rows4178, irow4174, rows4179]
  all_goals rfl

theorem atot4174 : totK PD2M8K2 D2M8K2.u4174 = [0, 0, 421743864540, 987286332820, 363602229499, 12440031250, 0, 0] := by
  rw [show D2M8K2.u4174 = KTree.node D2M8K2.t4178 (nat_lit 9682753) (nat_lit 1393479757) (nat_lit 0) D2M8K2.t4179 from rfl, totK_node, tot4178, tot4179]
  decide +kernel

theorem arows4176 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4176 = true := by
  rw [show D2M8K2.u4176 = KTree.node D2M8K2.t4180 (nat_lit 9684659) (nat_lit 2856913723) (nat_lit 0) D2M8K2.t4181 from rfl, allE_node, rows4180, irow4176, rows4181]
  all_goals rfl

theorem atot4176 : totK PD2M8K2 D2M8K2.u4176 = [0, 0, 323171032067, 913742082289, 524073860333, 36505195182, 0, 0] := by
  rw [show D2M8K2.u4176 = KTree.node D2M8K2.t4180 (nat_lit 9684659) (nat_lit 2856913723) (nat_lit 0) D2M8K2.t4181 from rfl, totK_node, tot4180, tot4181]
  decide +kernel

theorem arows4177 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4177 = true := by
  rw [show D2M8K2.u4177 = KTree.node D2M8K2.t4182 (nat_lit 9687580) (nat_lit 3875912919) (nat_lit 0) D2M8K2.t4183 from rfl, allE_node, rows4182, irow4177, rows4183]
  all_goals rfl

theorem atot4177 : totK PD2M8K2 D2M8K2.u4177 = [0, 0, 248729928365, 816155499255, 698030941184, 69264147049, 0, 0] := by
  rw [show D2M8K2.u4177 = KTree.node D2M8K2.t4182 (nat_lit 9687580) (nat_lit 3875912919) (nat_lit 0) D2M8K2.t4183 from rfl, totK_node, tot4182, tot4183]
  decide +kernel

theorem arows4180 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4180 = true := by
  rw [show D2M8K2.u4180 = KTree.node D2M8K2.t4184 (nat_lit 9688809) (nat_lit 1362427955) (nat_lit 0) D2M8K2.t4185 from rfl, allE_node, rows4184, irow4180, rows4185]
  all_goals rfl

theorem atot4180 : totK PD2M8K2 D2M8K2.u4180 = [0, 0, 345729199044, 937316889697, 509854795374, 36267499600, 0, 0] := by
  rw [show D2M8K2.u4180 = KTree.node D2M8K2.t4184 (nat_lit 9688809) (nat_lit 1362427955) (nat_lit 0) D2M8K2.t4185 from rfl, totK_node, tot4184, tot4185]
  decide +kernel

theorem arows4181 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4181 = true := by
  rw [show D2M8K2.u4181 = KTree.node D2M8K2.t4186 (nat_lit 9692098) (nat_lit 4070374803) (nat_lit 0) D2M8K2.t4187 from rfl, allE_node, rows4186, irow4181, rows4187]
  all_goals rfl

theorem atot4181 : totK PD2M8K2 D2M8K2.u4181 = [0, 0, 248060530923, 828798721064, 652446999428, 70598386202, 0, 0] := by
  rw [show D2M8K2.u4181 = KTree.node D2M8K2.t4186 (nat_lit 9692098) (nat_lit 4070374803) (nat_lit 0) D2M8K2.t4187 from rfl, totK_node, tot4186, tot4187]
  decide +kernel

theorem arows4183 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4183 = true := by
  rw [show D2M8K2.u4183 = KTree.node D2M8K2.t4188 (nat_lit 9694183) (nat_lit 2347207200) (nat_lit 0) D2M8K2.t4189 from rfl, allE_node, rows4188, irow4183, rows4189]
  all_goals rfl

theorem atot4183 : totK PD2M8K2 D2M8K2.u4183 = [0, 0, 241059193671, 759214832023, 662293390182, 123750979918, 2516941024, 0] := by
  rw [show D2M8K2.u4183 = KTree.node D2M8K2.t4188 (nat_lit 9694183) (nat_lit 2347207200) (nat_lit 0) D2M8K2.t4189 from rfl, totK_node, tot4188, tot4189]
  decide +kernel

theorem arows4184 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4184 = true := by
  rw [show D2M8K2.u4184 = KTree.node D2M8K2.t4190 (nat_lit 9695722) (nat_lit 3984837731) (nat_lit 0) D2M8K2.t4191 from rfl, allE_node, rows4190, irow4184, rows4191]
  all_goals rfl

theorem atot4184 : totK PD2M8K2 D2M8K2.u4184 = [0, 0, 168062828938, 767004862016, 748404029294, 103896112283, 0, 0] := by
  rw [show D2M8K2.u4184 = KTree.node D2M8K2.t4190 (nat_lit 9695722) (nat_lit 3984837731) (nat_lit 0) D2M8K2.t4191 from rfl, totK_node, tot4190, tot4191]
  decide +kernel

theorem arows4189 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4189 = true := by
  rw [show D2M8K2.u4189 = KTree.node D2M8K2.t4192 (nat_lit 9701325) (nat_lit 1422869584) (nat_lit 0) D2M8K2.t4193 from rfl, allE_node, rows4192, irow4189, rows4193]
  all_goals rfl

theorem atot4189 : totK PD2M8K2 D2M8K2.u4189 = [0, 0, 276575571060, 830494029380, 602017345028, 89221428126, 2532065704, 0] := by
  rw [show D2M8K2.u4189 = KTree.node D2M8K2.t4192 (nat_lit 9701325) (nat_lit 1422869584) (nat_lit 0) D2M8K2.t4193 from rfl, totK_node, tot4192, tot4193]
  decide +kernel

theorem arows4190 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4190 = true := by
  rw [show D2M8K2.u4190 = KTree.node D2M8K2.t4194 (nat_lit 9702733) (nat_lit 1364086415) (nat_lit 0) D2M8K2.t4195 from rfl, allE_node, rows4194, irow4190, rows4195]
  all_goals rfl

theorem atot4190 : totK PD2M8K2 D2M8K2.u4190 = [0, 0, 164196490766, 699130195203, 769507298454, 154886600813, 2348340425, 0] := by
  rw [show D2M8K2.u4190 = KTree.node D2M8K2.t4194 (nat_lit 9702733) (nat_lit 1364086415) (nat_lit 0) D2M8K2.t4195 from rfl, totK_node, tot4194, tot4195]
  decide +kernel

theorem arows4192 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4192 = true := by
  rw [show D2M8K2.u4192 = KTree.node D2M8K2.t4196 (nat_lit 9749704) (nat_lit 3869423843) (nat_lit 0) D2M8K2.t4197 from rfl, allE_node, rows4196, irow4192, rows4197]
  all_goals rfl

theorem atot4192 : totK PD2M8K2 D2M8K2.u4192 = [0, 0, 183285179032, 644337867154, 725733349659, 239475995763, 13764981515, 0] := by
  rw [show D2M8K2.u4192 = KTree.node D2M8K2.t4196 (nat_lit 9749704) (nat_lit 3869423843) (nat_lit 0) D2M8K2.t4197 from rfl, totK_node, tot4196, tot4197]
  decide +kernel

theorem arows4193 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4193 = true := by
  rw [show D2M8K2.u4193 = KTree.node D2M8K2.t4198 (nat_lit 9750847) (nat_lit 2304886826) (nat_lit 0) D2M8K2.t4199 from rfl, allE_node, rows4198, irow4193, rows4199]
  all_goals rfl

theorem atot4193 : totK PD2M8K2 D2M8K2.u4193 = [0, 0, 266649683684, 777429119454, 599729761908, 181757957301, 17186218589, 0] := by
  rw [show D2M8K2.u4193 = KTree.node D2M8K2.t4198 (nat_lit 9750847) (nat_lit 2304886826) (nat_lit 0) D2M8K2.t4199 from rfl, totK_node, tot4198, tot4199]
  decide +kernel

theorem arows4196 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4196 = true := by
  rw [show D2M8K2.u4196 = KTree.node D2M8K2.t4200 (nat_lit 9752295) (nat_lit 3632587653) (nat_lit 0) D2M8K2.t4201 from rfl, allE_node, rows4200, irow4196, rows4201]
  all_goals rfl

theorem atot4196 : totK PD2M8K2 D2M8K2.u4196 = [0, 0, 59699811499, 432935768117, 897261558470, 400263801686, 19311493318, 0] := by
  rw [show D2M8K2.u4196 = KTree.node D2M8K2.t4200 (nat_lit 9752295) (nat_lit 3632587653) (nat_lit 0) D2M8K2.t4201 from rfl, totK_node, tot4200, tot4201]
  decide +kernel

theorem arows4197 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4197 = true := by
  rw [show D2M8K2.u4197 = KTree.node D2M8K2.t4202 (nat_lit 9753562) (nat_lit 3745492570) (nat_lit 0) D2M8K2.t4203 from rfl, allE_node, rows4202, irow4197, rows4203]
  all_goals rfl

theorem atot4197 : totK PD2M8K2 D2M8K2.u4197 = [0, 0, 360004832389, 945983005990, 479429140397, 34792600035, 0, 0] := by
  rw [show D2M8K2.u4197 = KTree.node D2M8K2.t4202 (nat_lit 9753562) (nat_lit 3745492570) (nat_lit 0) D2M8K2.t4203 from rfl, totK_node, tot4202, tot4203]
  decide +kernel

theorem arows4199 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4199 = true := by
  rw [show D2M8K2.u4199 = KTree.node D2M8K2.t4204 (nat_lit 9755274) (nat_lit 2983709837) (nat_lit 0) D2M8K2.t4205 from rfl, allE_node, rows4204, irow4199, rows4205]
  all_goals rfl

theorem atot4199 : totK PD2M8K2 D2M8K2.u4199 = [0, 0, 32419875878, 510966851701, 956522828892, 272908200178, 8706415949, 0] := by
  rw [show D2M8K2.u4199 = KTree.node D2M8K2.t4204 (nat_lit 9755274) (nat_lit 2983709837) (nat_lit 0) D2M8K2.t4205 from rfl, totK_node, tot4204, tot4205]
  decide +kernel

theorem arows4200 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4200 = true := by
  rw [show D2M8K2.u4200 = KTree.node D2M8K2.t4206 (nat_lit 9757272) (nat_lit 3451047143) (nat_lit 0) D2M8K2.t4207 from rfl, allE_node, rows4206, irow4200, rows4207]
  all_goals rfl

theorem atot4200 : totK PD2M8K2 D2M8K2.u4200 = [0, 0, 390547576038, 951498732714, 451337523832, 33988345407, 0, 0] := by
  rw [show D2M8K2.u4200 = KTree.node D2M8K2.t4206 (nat_lit 9757272) (nat_lit 3451047143) (nat_lit 0) D2M8K2.t4207 from rfl, totK_node, tot4206, tot4207]
  decide +kernel

theorem arows4204 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4204 = true := by
  rw [show D2M8K2.u4204 = KTree.node D2M8K2.t4208 (nat_lit 9758979) (nat_lit 3615454077) (nat_lit 0) D2M8K2.t4209 from rfl, allE_node, rows4208, irow4204, rows4209]
  all_goals rfl

theorem atot4204 : totK PD2M8K2 D2M8K2.u4204 = [0, 0, 0, 510504036608, 976547166589, 277491885832, 8824320960, 0] := by
  rw [show D2M8K2.u4204 = KTree.node D2M8K2.t4208 (nat_lit 9758979) (nat_lit 3615454077) (nat_lit 0) D2M8K2.t4209 from rfl, totK_node, tot4208, tot4209]
  decide +kernel

theorem arows4205 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4205 = true := by
  rw [show D2M8K2.u4205 = KTree.node D2M8K2.t4210 (nat_lit 9760372) (nat_lit 4062894510) (nat_lit 0) D2M8K2.t4211 from rfl, allE_node, rows4210, irow4205, rows4211]
  all_goals rfl

theorem atot4205 : totK PD2M8K2 D2M8K2.u4205 = [0, 0, 382863451800, 919623274627, 468483933212, 44459038521, 0, 0] := by
  rw [show D2M8K2.u4205 = KTree.node D2M8K2.t4210 (nat_lit 9760372) (nat_lit 4062894510) (nat_lit 0) D2M8K2.t4211 from rfl, totK_node, tot4210, tot4211]
  decide +kernel

theorem arows4207 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4207 = true := by
  rw [show D2M8K2.u4207 = KTree.node D2M8K2.t4212 (nat_lit 9762101) (nat_lit 2400409922) (nat_lit 0) D2M8K2.t4213 from rfl, allE_node, rows4212, irow4207, rows4213]
  all_goals rfl

theorem atot4207 : totK PD2M8K2 D2M8K2.u4207 = [0, 0, 86473555660, 639402929192, 883605321727, 183274149299, 2498823382, 0] := by
  rw [show D2M8K2.u4207 = KTree.node D2M8K2.t4212 (nat_lit 9762101) (nat_lit 2400409922) (nat_lit 0) D2M8K2.t4213 from rfl, totK_node, tot4212, tot4213]
  decide +kernel

theorem arows4208 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4208 = true := by
  rw [show D2M8K2.u4208 = KTree.node D2M8K2.t4214 (nat_lit 9763927) (nat_lit 692312465) (nat_lit 0) D2M8K2.t4215 from rfl, allE_node, rows4214, irow4208, rows4215]
  all_goals rfl

theorem atot4208 : totK PD2M8K2 D2M8K2.u4208 = [0, 0, 372951037057, 942391361919, 477323644690, 38370490904, 0, 0] := by
  rw [show D2M8K2.u4208 = KTree.node D2M8K2.t4214 (nat_lit 9763927) (nat_lit 692312465) (nat_lit 0) D2M8K2.t4215 from rfl, totK_node, tot4214, tot4215]
  decide +kernel

theorem arows4211 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4211 = true := by
  rw [show D2M8K2.u4211 = KTree.node D2M8K2.t4216 (nat_lit 9765620) (nat_lit 3308764656) (nat_lit 0) D2M8K2.t4217 from rfl, allE_node, rows4216, irow4211, rows4217]
  all_goals rfl

theorem atot4211 : totK PD2M8K2 D2M8K2.u4211 = [0, 0, 0, 497408370625, 1000212440411, 279500285303, 4627616211, 0] := by
  rw [show D2M8K2.u4211 = KTree.node D2M8K2.t4216 (nat_lit 9765620) (nat_lit 3308764656) (nat_lit 0) D2M8K2.t4217 from rfl, totK_node, tot4216, tot4217]
  decide +kernel

theorem arows4212 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4212 = true := by
  rw [show D2M8K2.u4212 = KTree.node D2M8K2.t4218 (nat_lit 9770814) (nat_lit 3164418772) (nat_lit 0) D2M8K2.t4219 from rfl, allE_node, rows4218, irow4212, rows4219]
  all_goals rfl

theorem atot4212 : totK PD2M8K2 D2M8K2.u4212 = [0, 0, 0, 357490378450, 904524199070, 521055251847, 45892958740, 0] := by
  rw [show D2M8K2.u4212 = KTree.node D2M8K2.t4218 (nat_lit 9770814) (nat_lit 3164418772) (nat_lit 0) D2M8K2.t4219 from rfl, totK_node, tot4218, tot4219]
  decide +kernel

theorem arows4214 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4214 = true := by
  rw [show D2M8K2.u4214 = KTree.node D2M8K2.t4220 (nat_lit 9772311) (nat_lit 3626128243) (nat_lit 0) D2M8K2.t4221 from rfl, allE_node, rows4220, irow4214, rows4221]
  all_goals rfl

theorem atot4214 : totK PD2M8K2 D2M8K2.u4214 = [0, 0, 0, 88555651143, 573692552696, 819807649216, 303679096791, 25191558099] := by
  rw [show D2M8K2.u4214 = KTree.node D2M8K2.t4220 (nat_lit 9772311) (nat_lit 3626128243) (nat_lit 0) D2M8K2.t4221 from rfl, totK_node, tot4220, tot4221]
  decide +kernel

theorem arows4215 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4215 = true := by
  rw [show D2M8K2.u4215 = KTree.node D2M8K2.t4222 (nat_lit 9773555) (nat_lit 2859806474) (nat_lit 0) D2M8K2.t4223 from rfl, allE_node, rows4222, irow4215, rows4223]
  all_goals rfl

theorem atot4215 : totK PD2M8K2 D2M8K2.u4215 = [0, 0, 0, 206253610334, 615038005256, 694143380961, 260502195474, 11730315755] := by
  rw [show D2M8K2.u4215 = KTree.node D2M8K2.t4222 (nat_lit 9773555) (nat_lit 2859806474) (nat_lit 0) D2M8K2.t4223 from rfl, totK_node, tot4222, tot4223]
  decide +kernel

theorem arows4222 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4222 = true := by
  rw [show D2M8K2.u4222 = KTree.node D2M8K2.t4224 (nat_lit 9775093) (nat_lit 648239716) (nat_lit 0) D2M8K2.t4225 from rfl, allE_node, rows4224, irow4222, rows4225]
  all_goals rfl

theorem atot4222 : totK PD2M8K2 D2M8K2.u4222 = [0, 0, 0, 206868536083, 836569088317, 673123293294, 64108318716, 0] := by
  rw [show D2M8K2.u4222 = KTree.node D2M8K2.t4224 (nat_lit 9775093) (nat_lit 648239716) (nat_lit 0) D2M8K2.t4225 from rfl, totK_node, tot4224, tot4225]
  decide +kernel

theorem arows4223 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4223 = true := by
  rw [show D2M8K2.u4223 = KTree.node D2M8K2.t4226 (nat_lit 9777168) (nat_lit 1845584383) (nat_lit 2176) D2M8K2.t4227 from rfl, allE_node, rows4226, irow4223, rows4227]
  all_goals rfl

theorem atot4223 : totK PD2M8K2 D2M8K2.u4223 = [0, 0, 0, 246946885685, 714493052032, 656735616061, 153802745401, 5067863418] := by
  rw [show D2M8K2.u4223 = KTree.node D2M8K2.t4226 (nat_lit 9777168) (nat_lit 1845584383) (nat_lit 2176) D2M8K2.t4227 from rfl, totK_node, tot4226, tot4227]
  decide +kernel

theorem arows4225 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4225 = true := by
  rw [show D2M8K2.u4225 = KTree.node D2M8K2.t4228 (nat_lit 9778689) (nat_lit 1479622053) (nat_lit 0) D2M8K2.t4229 from rfl, allE_node, rows4228, irow4225, rows4229]
  all_goals rfl

theorem atot4225 : totK PD2M8K2 D2M8K2.u4225 = [0, 0, 0, 170350051523, 743067744462, 712220202297, 129892753058, 3962658158] := by
  rw [show D2M8K2.u4225 = KTree.node D2M8K2.t4228 (nat_lit 9778689) (nat_lit 1479622053) (nat_lit 0) D2M8K2.t4229 from rfl, totK_node, tot4228, tot4229]
  decide +kernel

theorem arows4226 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4226 = true := by
  rw [show D2M8K2.u4226 = KTree.node D2M8K2.t4230 (nat_lit 9780832) (nat_lit 3741771442) (nat_lit 0) D2M8K2.t4231 from rfl, allE_node, rows4230, irow4226, rows4231]
  all_goals rfl

theorem atot4226 : totK PD2M8K2 D2M8K2.u4226 = [0, 0, 0, 272499009460, 771028454297, 621184301315, 102767866537, 1163853884] := by
  rw [show D2M8K2.u4226 = KTree.node D2M8K2.t4230 (nat_lit 9780832) (nat_lit 3741771442) (nat_lit 0) D2M8K2.t4231 from rfl, totK_node, tot4230, tot4231]
  decide +kernel

theorem arows4229 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4229 = true := by
  rw [show D2M8K2.u4229 = KTree.node D2M8K2.t4232 (nat_lit 9782313) (nat_lit 1899722518) (nat_lit 0) D2M8K2.t4233 from rfl, allE_node, rows4232, irow4229, rows4233]
  all_goals rfl

theorem atot4229 : totK PD2M8K2 D2M8K2.u4229 = [0, 0, 0, 142350605717, 792201249534, 779427217649, 75408551948, 0] := by
  rw [show D2M8K2.u4229 = KTree.node D2M8K2.t4232 (nat_lit 9782313) (nat_lit 1899722518) (nat_lit 0) D2M8K2.t4233 from rfl, totK_node, tot4232, tot4233]
  decide +kernel

theorem arows4230 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4230 = true := by
  rw [show D2M8K2.u4230 = KTree.node D2M8K2.t4234 (nat_lit 9784492) (nat_lit 3823409457) (nat_lit 0) D2M8K2.t4235 from rfl, allE_node, rows4234, irow4230, rows4235]
  all_goals rfl

theorem atot4230 : totK PD2M8K2 D2M8K2.u4230 = [0, 0, 0, 338479175536, 833681945287, 536750781498, 85186170273, 1392055030] := by
  rw [show D2M8K2.u4230 = KTree.node D2M8K2.t4234 (nat_lit 9784492) (nat_lit 3823409457) (nat_lit 0) D2M8K2.t4235 from rfl, totK_node, tot4234, tot4235]
  decide +kernel

theorem arows4232 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4232 = true := by
  rw [show D2M8K2.u4232 = KTree.node D2M8K2.t4236 (nat_lit 9786293) (nat_lit 2401304114) (nat_lit 0) D2M8K2.t4237 from rfl, allE_node, rows4236, irow4232, rows4237]
  all_goals rfl

theorem atot4232 : totK PD2M8K2 D2M8K2.u4232 = [0, 0, 0, 81025935947, 625406348494, 867325092821, 191473267119, 2437267027] := by
  rw [show D2M8K2.u4232 = KTree.node D2M8K2.t4236 (nat_lit 9786293) (nat_lit 2401304114) (nat_lit 0) D2M8K2.t4237 from rfl, totK_node, tot4236, tot4237]
  decide +kernel

theorem arows4233 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4233 = true := by
  rw [show D2M8K2.u4233 = KTree.node D2M8K2.t4238 (nat_lit 9788606) (nat_lit 3564299072) (nat_lit 0) D2M8K2.t4239 from rfl, allE_node, rows4238, irow4233, rows4239]
  all_goals rfl

theorem atot4233 : totK PD2M8K2 D2M8K2.u4233 = [0, 0, 320804550429, 849639506092, 446534956898, 86642438112, 69057510705, 6701800220] := by
  rw [show D2M8K2.u4233 = KTree.node D2M8K2.t4238 (nat_lit 9788606) (nat_lit 3564299072) (nat_lit 0) D2M8K2.t4239 from rfl, totK_node, tot4238, tot4239]
  decide +kernel

theorem arows4237 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4237 = true := by
  rw [show D2M8K2.u4237 = KTree.node D2M8K2.t4240 (nat_lit 9791337) (nat_lit 1804899571) (nat_lit 0) D2M8K2.t4241 from rfl, allE_node, rows4240, irow4237, rows4241]
  all_goals rfl

theorem atot4237 : totK PD2M8K2 D2M8K2.u4237 = [0, 0, 256318553045, 839055169473, 671527815334, 75843799172, 0, 0] := by
  rw [show D2M8K2.u4237 = KTree.node D2M8K2.t4240 (nat_lit 9791337) (nat_lit 1804899571) (nat_lit 0) D2M8K2.t4241 from rfl, totK_node, tot4240, tot4241]
  decide +kernel

theorem arows4238 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4238 = true := by
  rw [show D2M8K2.u4238 = KTree.node D2M8K2.t4242 (nat_lit 9792558) (nat_lit 3771102559) (nat_lit 0) D2M8K2.t4243 from rfl, allE_node, rows4242, irow4238, rows4243]
  all_goals rfl

theorem atot4238 : totK PD2M8K2 D2M8K2.u4238 = [0, 0, 174692607031, 657714565424, 703801831339, 255565255967, 24256071441, 0] := by
  rw [show D2M8K2.u4238 = KTree.node D2M8K2.t4242 (nat_lit 9792558) (nat_lit 3771102559) (nat_lit 0) D2M8K2.t4243 from rfl, totK_node, tot4242, tot4243]
  decide +kernel

theorem arows4240 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4240 = true := by
  rw [show D2M8K2.u4240 = KTree.node D2M8K2.t4244 (nat_lit 9794067) (nat_lit 3649675009) (nat_lit 0) D2M8K2.t4245 from rfl, allE_node, rows4244, irow4240, rows4245]
  all_goals rfl

theorem atot4240 : totK PD2M8K2 D2M8K2.u4240 = [0, 0, 163536014650, 571869550446, 735452443078, 312100396188, 13231254741, 0] := by
  rw [show D2M8K2.u4240 = KTree.node D2M8K2.t4244 (nat_lit 9794067) (nat_lit 3649675009) (nat_lit 0) D2M8K2.t4245 from rfl, totK_node, tot4244, tot4245]
  decide +kernel

theorem arows4241 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4241 = true := by
  rw [show D2M8K2.u4241 = KTree.node D2M8K2.t4246 (nat_lit 9795540) (nat_lit 2762155663) (nat_lit 0) D2M8K2.t4247 from rfl, allE_node, rows4246, irow4241, rows4247]
  all_goals rfl

theorem atot4241 : totK PD2M8K2 D2M8K2.u4241 = [0, 0, 272710153596, 878106647331, 611021095618, 57222727257, 0, 0] := by
  rw [show D2M8K2.u4241 = KTree.node D2M8K2.t4246 (nat_lit 9795540) (nat_lit 2762155663) (nat_lit 0) D2M8K2.t4247 from rfl, totK_node, tot4246, tot4247]
  decide +kernel

theorem arows4244 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4244 = true := by
  rw [show D2M8K2.u4244 = KTree.node D2M8K2.t4248 (nat_lit 9797233) (nat_lit 1459124010) (nat_lit 0) D2M8K2.t4249 from rfl, allE_node, rows4248, irow4244, rows4249]
  all_goals rfl

theorem atot4244 : totK PD2M8K2 D2M8K2.u4244 = [0, 0, 94351752822, 568055851092, 856918228192, 260979520325, 9094631223, 0] := by
  rw [show D2M8K2.u4244 = KTree.node D2M8K2.t4248 (nat_lit 9797233) (nat_lit 1459124010) (nat_lit 0) D2M8K2.t4249 from rfl, totK_node, tot4248, tot4249]
  decide +kernel

theorem arows4245 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4245 = true := by
  rw [show D2M8K2.u4245 = KTree.node D2M8K2.t4250 (nat_lit 9802100) (nat_lit 3232666867) (nat_lit 0) D2M8K2.t4251 from rfl, allE_node, rows4250, irow4245, rows4251]
  all_goals rfl

theorem atot4245 : totK PD2M8K2 D2M8K2.u4245 = [0, 0, 315643549525, 892175584273, 547211308389, 49801290741, 0, 0] := by
  rw [show D2M8K2.u4245 = KTree.node D2M8K2.t4250 (nat_lit 9802100) (nat_lit 3232666867) (nat_lit 0) D2M8K2.t4251 from rfl, totK_node, tot4250, tot4251]
  decide +kernel

theorem arows4247 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4247 = true := by
  rw [show D2M8K2.u4247 = KTree.node D2M8K2.t4252 (nat_lit 9804156) (nat_lit 2999151431) (nat_lit 0) D2M8K2.t4253 from rfl, allE_node, rows4252, irow4247, rows4253]
  all_goals rfl

theorem atot4247 : totK PD2M8K2 D2M8K2.u4247 = [0, 0, 165327025006, 693685821264, 787562578010, 172771857365, 2586295899, 0] := by
  rw [show D2M8K2.u4247 = KTree.node D2M8K2.t4252 (nat_lit 9804156) (nat_lit 2999151431) (nat_lit 0) D2M8K2.t4253 from rfl, totK_node, tot4252, tot4253]
  decide +kernel

theorem arows4248 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4248 = true := by
  rw [show D2M8K2.u4248 = KTree.node D2M8K2.t4254 (nat_lit 9805763) (nat_lit 2696209974) (nat_lit 0) D2M8K2.t4255 from rfl, allE_node, rows4254, irow4248, rows4255]
  all_goals rfl

theorem atot4248 : totK PD2M8K2 D2M8K2.u4248 = [0, 0, 250266552724, 804488724584, 665707429537, 92152425699, 0, 0] := by
  rw [show D2M8K2.u4248 = KTree.node D2M8K2.t4254 (nat_lit 9805763) (nat_lit 2696209974) (nat_lit 0) D2M8K2.t4255 from rfl, totK_node, tot4254, tot4255]
  decide +kernel

theorem arows4253 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4253 = true := by
  rw [show D2M8K2.u4253 = KTree.node D2M8K2.t4256 (nat_lit 9807847) (nat_lit 1608905451) (nat_lit 2) D2M8K2.t4257 from rfl, allE_node, rows4256, irow4253, rows4257]
  all_goals rfl

theorem atot4253 : totK PD2M8K2 D2M8K2.u4253 = [0, 0, 0, 466340218799, 968726181333, 327156447577, 13638630599, 0] := by
  rw [show D2M8K2.u4253 = KTree.node D2M8K2.t4256 (nat_lit 9807847) (nat_lit 1608905451) (nat_lit 2) D2M8K2.t4257 from rfl, totK_node, tot4256, tot4257]
  decide +kernel

theorem arows4254 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4254 = true := by
  rw [show D2M8K2.u4254 = KTree.node D2M8K2.t4258 (nat_lit 9812050) (nat_lit 3991163690) (nat_lit 0) D2M8K2.t4259 from rfl, allE_node, rows4258, irow4254, rows4259]
  all_goals rfl

theorem atot4254 : totK PD2M8K2 D2M8K2.u4254 = [0, 0, 0, 415440303363, 965677527129, 404617867603, 28488717195, 0] := by
  rw [show D2M8K2.u4254 = KTree.node D2M8K2.t4258 (nat_lit 9812050) (nat_lit 3991163690) (nat_lit 0) D2M8K2.t4259 from rfl, totK_node, tot4258, tot4259]
  decide +kernel

theorem arows4256 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4256 = true := by
  rw [show D2M8K2.u4256 = KTree.node D2M8K2.t4260 (nat_lit 9813293) (nat_lit 2131769361) (nat_lit 0) D2M8K2.t4261 from rfl, allE_node, rows4260, irow4256, rows4261]
  all_goals rfl

theorem atot4256 : totK PD2M8K2 D2M8K2.u4256 = [0, 0, 0, 369424004588, 924106030487, 463022137605, 30834703124, 0] := by
  rw [show D2M8K2.u4256 = KTree.node D2M8K2.t4260 (nat_lit 9813293) (nat_lit 2131769361) (nat_lit 0) D2M8K2.t4261 from rfl, totK_node, tot4260, tot4261]
  decide +kernel

theorem arows4257 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4257 = true := by
  rw [show D2M8K2.u4257 = KTree.node D2M8K2.t4262 (nat_lit 9816529) (nat_lit 1487015166) (nat_lit 0) D2M8K2.t4263 from rfl, allE_node, rows4262, irow4257, rows4263]
  all_goals rfl

theorem atot4257 : totK PD2M8K2 D2M8K2.u4257 = [0, 0, 0, 236656255330, 870998794866, 627444543990, 48612161636, 0] := by
  rw [show D2M8K2.u4257 = KTree.node D2M8K2.t4262 (nat_lit 9816529) (nat_lit 1487015166) (nat_lit 0) D2M8K2.t4263 from rfl, totK_node, tot4262, tot4263]
  decide +kernel

theorem arows4260 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4260 = true := by
  rw [show D2M8K2.u4260 = KTree.node D2M8K2.t4264 (nat_lit 9822033) (nat_lit 1818937101) (nat_lit 0) D2M8K2.t4265 from rfl, allE_node, rows4264, irow4260, rows4265]
  all_goals rfl

theorem atot4260 : totK PD2M8K2 D2M8K2.u4260 = [0, 0, 0, 248798472037, 735129695204, 615596615731, 147449644039, 5320761635] := by
  rw [show D2M8K2.u4260 = KTree.node D2M8K2.t4264 (nat_lit 9822033) (nat_lit 1818937101) (nat_lit 0) D2M8K2.t4265 from rfl, totK_node, tot4264, tot4265]
  decide +kernel

theorem arows4261 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4261 = true := by
  rw [show D2M8K2.u4261 = KTree.node D2M8K2.t4266 (nat_lit 9823685) (nat_lit 2295405609) (nat_lit 0) D2M8K2.t4267 from rfl, allE_node, rows4266, irow4261, rows4267]
  all_goals rfl

theorem atot4261 : totK PD2M8K2 D2M8K2.u4261 = [0, 0, 0, 157841096676, 849222896137, 688619608031, 52911899998, 0] := by
  rw [show D2M8K2.u4261 = KTree.node D2M8K2.t4266 (nat_lit 9823685) (nat_lit 2295405609) (nat_lit 0) D2M8K2.t4267 from rfl, totK_node, tot4266, tot4267]
  decide +kernel

theorem arows4263 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4263 = true := by
  rw [show D2M8K2.u4263 = KTree.node D2M8K2.t4268 (nat_lit 9825991) (nat_lit 801616295) (nat_lit 2) D2M8K2.t4269 from rfl, allE_node, rows4268, irow4263, rows4269]
  all_goals rfl

theorem atot4263 : totK PD2M8K2 D2M8K2.u4263 = [0, 0, 0, 398431080354, 874164559403, 457032719354, 60884427044, 1225787871] := by
  rw [show D2M8K2.u4263 = KTree.node D2M8K2.t4268 (nat_lit 9825991) (nat_lit 801616295) (nat_lit 2) D2M8K2.t4269 from rfl, totK_node, tot4268, tot4269]
  decide +kernel

theorem arows4264 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4264 = true := by
  rw [show D2M8K2.u4264 = KTree.node D2M8K2.t4270 (nat_lit 9830023) (nat_lit 2350901073) (nat_lit 0) D2M8K2.t4271 from rfl, allE_node, rows4270, irow4264, rows4271]
  all_goals rfl

theorem atot4264 : totK PD2M8K2 D2M8K2.u4264 = [0, 0, 320954541705, 823683227710, 497911958794, 139902525814, 10051291645, 0] := by
  rw [show D2M8K2.u4264 = KTree.node D2M8K2.t4270 (nat_lit 9830023) (nat_lit 2350901073) (nat_lit 0) D2M8K2.t4271 from rfl, totK_node, tot4270, tot4271]
  decide +kernel

theorem arows4268 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4268 = true := by
  rw [show D2M8K2.u4268 = KTree.node D2M8K2.t4272 (nat_lit 9832745) (nat_lit 1557259990) (nat_lit 0) D2M8K2.t4273 from rfl, allE_node, rows4272, irow4268, rows4273]
  all_goals rfl

theorem atot4268 : totK PD2M8K2 D2M8K2.u4268 = [0, 0, 256340840216, 828124367815, 680587781998, 75200588490, 0, 0] := by
  rw [show D2M8K2.u4268 = KTree.node D2M8K2.t4272 (nat_lit 9832745) (nat_lit 1557259990) (nat_lit 0) D2M8K2.t4273 from rfl, totK_node, tot4272, tot4273]
  decide +kernel

theorem arows4269 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4269 = true := by
  rw [show D2M8K2.u4269 = KTree.node D2M8K2.t4274 (nat_lit 9833962) (nat_lit 3965242122) (nat_lit 0) D2M8K2.t4275 from rfl, allE_node, rows4274, irow4269, rows4275]
  all_goals rfl

theorem atot4269 : totK PD2M8K2 D2M8K2.u4269 = [0, 0, 174706502236, 687264999012, 698238155794, 237900066496, 21393864572, 0] := by
  rw [show D2M8K2.u4269 = KTree.node D2M8K2.t4274 (nat_lit 9833962) (nat_lit 3965242122) (nat_lit 0) D2M8K2.t4275 from rfl, totK_node, tot4274, tot4275]
  decide +kernel

theorem arows4271 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4271 = true := by
  rw [show D2M8K2.u4271 = KTree.node D2M8K2.t4276 (nat_lit 9835495) (nat_lit 1857905548) (nat_lit 0) D2M8K2.t4277 from rfl, allE_node, rows4276, irow4271, rows4277]
  all_goals rfl

theorem atot4271 : totK PD2M8K2 D2M8K2.u4271 = [0, 0, 134860001436, 535796234901, 778341547875, 330951977888, 16091834962, 0] := by
  rw [show D2M8K2.u4271 = KTree.node D2M8K2.t4276 (nat_lit 9835495) (nat_lit 1857905548) (nat_lit 0) D2M8K2.t4277 from rfl, totK_node, tot4276, tot4277]
  decide +kernel

theorem arows4272 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4272 = true := by
  rw [show D2M8K2.u4272 = KTree.node D2M8K2.t4278 (nat_lit 9840427) (nat_lit 1808038048) (nat_lit 0) D2M8K2.t4279 from rfl, allE_node, rows4278, irow4272, rows4279]
  all_goals rfl

theorem atot4272 : totK PD2M8K2 D2M8K2.u4272 = [0, 0, 305147742754, 897858585793, 574556147671, 53506594750, 0, 0] := by
  rw [show D2M8K2.u4272 = KTree.node D2M8K2.t4278 (nat_lit 9840427) (nat_lit 1808038048) (nat_lit 0) D2M8K2.t4279 from rfl, totK_node, tot4278, tot4279]
  decide +kernel

theorem arows4275 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4275 = true := by
  rw [show D2M8K2.u4275 = KTree.node D2M8K2.t4280 (nat_lit 9842116) (nat_lit 2919506666) (nat_lit 0) D2M8K2.t4281 from rfl, allE_node, rows4280, irow4275, rows4281]
  all_goals rfl

theorem atot4275 : totK PD2M8K2 D2M8K2.u4275 = [0, 0, 74723461799, 540934731905, 879948584534, 276139263281, 9198031362, 0] := by
  rw [show D2M8K2.u4275 = KTree.node D2M8K2.t4280 (nat_lit 9842116) (nat_lit 2919506666) (nat_lit 0) D2M8K2.t4281 from rfl, totK_node, tot4280, tot4281]
  decide +kernel

theorem arows4276 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4276 = true := by
  rw [show D2M8K2.u4276 = KTree.node D2M8K2.t4282 (nat_lit 9843568) (nat_lit 2296507867) (nat_lit 0) D2M8K2.t4283 from rfl, allE_node, rows4282, irow4276, rows4283]
  all_goals rfl

theorem atot4276 : totK PD2M8K2 D2M8K2.u4276 = [0, 0, 335338511724, 916823282994, 518862222873, 42573933353, 0, 0] := by
  rw [show D2M8K2.u4276 = KTree.node D2M8K2.t4282 (nat_lit 9843568) (nat_lit 2296507867) (nat_lit 0) D2M8K2.t4283 from rfl, totK_node, tot4282, tot4283]
  decide +kernel

theorem arows4278 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4278 = true := by
  rw [show D2M8K2.u4278 = KTree.node D2M8K2.t4284 (nat_lit 9845580) (nat_lit 3332288308) (nat_lit 0) D2M8K2.t4285 from rfl, allE_node, rows4284, irow4278, rows4285]
  all_goals rfl

theorem atot4278 : totK PD2M8K2 D2M8K2.u4278 = [0, 0, 149384902058, 678838905466, 806431456099, 173120480871, 2586295899, 0] := by
  rw [show D2M8K2.u4278 = KTree.node D2M8K2.t4284 (nat_lit 9845580) (nat_lit 3332288308) (nat_lit 0) D2M8K2.t4285 from rfl, totK_node, tot4284, tot4285]
  decide +kernel

theorem arows4279 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4279 = true := by
  rw [show D2M8K2.u4279 = KTree.node D2M8K2.t4286 (nat_lit 9847172) (nat_lit 2608781627) (nat_lit 0) D2M8K2.t4287 from rfl, allE_node, rows4286, irow4279, rows4287]
  all_goals rfl

theorem atot4279 : totK PD2M8K2 D2M8K2.u4279 = [0, 0, 266291711167, 831337516268, 645738167748, 78328043417, 0, 0] := by
  rw [show D2M8K2.u4279 = KTree.node D2M8K2.t4286 (nat_lit 9847172) (nat_lit 2608781627) (nat_lit 0) D2M8K2.t4287 from rfl, totK_node, tot4286, tot4287]
  decide +kernel

theorem arows4285 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4285 = true := by
  rw [show D2M8K2.u4285 = KTree.node D2M8K2.t4288 (nat_lit 9848955) (nat_lit 2396558320) (nat_lit 0) D2M8K2.t4289 from rfl, allE_node, rows4288, irow4285, rows4289]
  all_goals rfl

theorem atot4285 : totK PD2M8K2 D2M8K2.u4285 = [0, 0, 0, 489012436880, 953558948043, 330153847040, 13654627229, 0] := by
  rw [show D2M8K2.u4285 = KTree.node D2M8K2.t4288 (nat_lit 9848955) (nat_lit 2396558320) (nat_lit 0) D2M8K2.t4289 from rfl, totK_node, tot4288, tot4289]
  decide +kernel

theorem arows4286 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4286 = true := by
  rw [show D2M8K2.u4286 = KTree.node D2M8K2.t4290 (nat_lit 9853544) (nat_lit 3570474573) (nat_lit 0) D2M8K2.t4291 from rfl, allE_node, rows4290, irow4286, rows4291]
  all_goals rfl

theorem atot4286 : totK PD2M8K2 D2M8K2.u4286 = [0, 0, 0, 418302586584, 949511976556, 415954640102, 30437187744, 0] := by
  rw [show D2M8K2.u4286 = KTree.node D2M8K2.t4290 (nat_lit 9853544) (nat_lit 3570474573) (nat_lit 0) D2M8K2.t4291 from rfl, totK_node, tot4290, tot4291]
  decide +kernel

theorem arows4288 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4288 = true := by
  rw [show D2M8K2.u4288 = KTree.node D2M8K2.t4292 (nat_lit 9859969) (nat_lit 1573092198) (nat_lit 0) D2M8K2.t4293 from rfl, allE_node, rows4292, irow4288, rows4293]
  all_goals rfl

theorem atot4288 : totK PD2M8K2 D2M8K2.u4288 = [0, 0, 0, 376221403282, 923345856676, 464130484388, 32678988433, 0] := by
  rw [show D2M8K2.u4288 = KTree.node D2M8K2.t4292 (nat_lit 9859969) (nat_lit 1573092198) (nat_lit 0) D2M8K2.t4293 from rfl, totK_node, tot4292, tot4293]
  decide +kernel

theorem arows4289 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4289 = true := by
  rw [show D2M8K2.u4289 = KTree.node D2M8K2.t4294 (nat_lit 9861480) (nat_lit 3534038886) (nat_lit 0) D2M8K2.t4295 from rfl, allE_node, rows4294, irow4289, rows4295]
  all_goals rfl

theorem atot4289 : totK PD2M8K2 D2M8K2.u4289 = [0, 0, 0, 228184608349, 854651367213, 643959207620, 50796444960, 0] := by
  rw [show D2M8K2.u4289 = KTree.node D2M8K2.t4294 (nat_lit 9861480) (nat_lit 3534038886) (nat_lit 0) D2M8K2.t4295 from rfl, totK_node, tot4294, tot4295]
  decide +kernel

theorem arows4292 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4292 = true := by
  rw [show D2M8K2.u4292 = KTree.node D2M8K2.t4296 (nat_lit 9863522) (nat_lit 3266617108) (nat_lit 0) D2M8K2.t4297 from rfl, allE_node, rows4296, irow4292, rows4297]
  all_goals rfl

theorem atot4292 : totK PD2M8K2 D2M8K2.u4292 = [0, 0, 0, 226679465337, 736136986567, 634648969116, 146931223252, 5352782441] := by
  rw [show D2M8K2.u4292 = KTree.node D2M8K2.t4296 (nat_lit 9863522) (nat_lit 3266617108) (nat_lit 0) D2M8K2.t4297 from rfl, totK_node, tot4296, tot4297]
  decide +kernel

theorem arows4293 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4293 = true := by
  rw [show D2M8K2.u4293 = KTree.node D2M8K2.t4298 (nat_lit 9865225) (nat_lit 1495852217) (nat_lit 0) D2M8K2.t4299 from rfl, allE_node, rows4298, irow4293, rows4299]
  all_goals rfl

theorem atot4293 : totK PD2M8K2 D2M8K2.u4293 = [0, 0, 0, 178017608236, 831888640804, 690291295836, 58690251594, 0] := by
  rw [show D2M8K2.u4293 = KTree.node D2M8K2.t4298 (nat_lit 9865225) (nat_lit 1495852217) (nat_lit 0) D2M8K2.t4299 from rfl, totK_node, tot4298, tot4299]
  decide +kernel

theorem arows4295 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4295 = true := by
  rw [show D2M8K2.u4295 = KTree.node D2M8K2.t4300 (nat_lit 9867489) (nat_lit 1303746901) (nat_lit 0) D2M8K2.t4301 from rfl, allE_node, rows4300, irow4295, rows4301]
  all_goals rfl

theorem atot4295 : totK PD2M8K2 D2M8K2.u4295 = [0, 0, 0, 404177318756, 876812431173, 456623974415, 59974494565, 1271866555] := by
  rw [show D2M8K2.u4295 = KTree.node D2M8K2.t4300 (nat_lit 9867489) (nat_lit 1303746901) (nat_lit 0) D2M8K2.t4301 from rfl, totK_node, tot4300, tot4301]
  decide +kernel

theorem arows4296 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4296 = true := by
  rw [show D2M8K2.u4296 = KTree.node D2M8K2.t4302 (nat_lit 9871231) (nat_lit 2358909988) (nat_lit 0) D2M8K2.t4303 from rfl, allE_node, rows4302, irow4296, rows4303]
  all_goals rfl

theorem atot4296 : totK PD2M8K2 D2M8K2.u4296 = [0, 0, 319053168236, 795150531031, 498909132888, 142026627729, 10061564396, 0] := by
  rw [show D2M8K2.u4296 = KTree.node D2M8K2.t4302 (nat_lit 9871231) (nat_lit 2358909988) (nat_lit 0) D2M8K2.t4303 from rfl, totK_node, tot4302, tot4303]
  decide +kernel

theorem arows4300 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4300 = true := by
  rw [show D2M8K2.u4300 = KTree.node D2M8K2.t4304 (nat_lit 9874200) (nat_lit 2374062778) (nat_lit 0) D2M8K2.t4305 from rfl, allE_node, rows4304, irow4300, rows4305]
  all_goals rfl

theorem atot4300 : totK PD2M8K2 D2M8K2.u4300 = [0, 0, 246975358685, 814223787305, 694853353019, 73106485791, 0, 0] := by
  rw [show D2M8K2.u4300 = KTree.node D2M8K2.t4304 (nat_lit 9874200) (nat_lit 2374062778) (nat_lit 0) D2M8K2.t4305 from rfl, totK_node, tot4304, tot4305]
  decide +kernel

theorem arows4301 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4301 = true := by
  rw [show D2M8K2.u4301 = KTree.node D2M8K2.t4306 (nat_lit 9875406) (nat_lit 3824042446) (nat_lit 0) D2M8K2.t4307 from rfl, allE_node, rows4306, irow4301, rows4307]
  all_goals rfl

theorem atot4301 : totK PD2M8K2 D2M8K2.u4301 = [0, 0, 179880361390, 730488004559, 680839425614, 206965721985, 21396654552, 0] := by
  rw [show D2M8K2.u4301 = KTree.node D2M8K2.t4306 (nat_lit 9875406) (nat_lit 3824042446) (nat_lit 0) D2M8K2.t4307 from rfl, totK_node, tot4306, tot4307]
  decide +kernel

theorem arows4303 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4303 = true := by
  rw [show D2M8K2.u4303 = KTree.node D2M8K2.t4308 (nat_lit 9876873) (nat_lit 1837758669) (nat_lit 0) D2M8K2.t4309 from rfl, allE_node, rows4308, irow4303, rows4309]
  all_goals rfl

theorem atot4303 : totK PD2M8K2 D2M8K2.u4303 = [0, 0, 124865311629, 502187114292, 784107291290, 365378557195, 16094634009, 0] := by
  rw [show D2M8K2.u4303 = KTree.node D2M8K2.t4308 (nat_lit 9876873) (nat_lit 1837758669) (nat_lit 0) D2M8K2.t4309 from rfl, totK_node, tot4308, tot4309]
  decide +kernel

theorem arows4304 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4304 = true := by
  rw [show D2M8K2.u4304 = KTree.node D2M8K2.t4310 (nat_lit 9878442) (nat_lit 3555811471) (nat_lit 0) D2M8K2.t4311 from rfl, allE_node, rows4310, irow4304, rows4311]
  all_goals rfl

theorem atot4304 : totK PD2M8K2 D2M8K2.u4304 = [0, 0, 287049030836, 866214671162, 592317409149, 58694928667, 0, 0] := by
  rw [show D2M8K2.u4304 = KTree.node D2M8K2.t4310 (nat_lit 9878442) (nat_lit 3555811471) (nat_lit 0) D2M8K2.t4311 from rfl, totK_node, tot4310, tot4311]
  decide +kernel

theorem arows4307 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4307 = true := by
  rw [show D2M8K2.u4307 = KTree.node D2M8K2.t4312 (nat_lit 9880197) (nat_lit 1514933268) (nat_lit 0) D2M8K2.t4313 from rfl, allE_node, rows4312, irow4307, rows4313]
  all_goals rfl

theorem atot4307 : totK PD2M8K2 D2M8K2.u4307 = [0, 0, 128291511328, 601553776849, 802683529634, 242404288684, 9094631223, 0] := by
  rw [show D2M8K2.u4307 = KTree.node D2M8K2.t4312 (nat_lit 9880197) (nat_lit 1514933268) (nat_lit 0) D2M8K2.t4313 from rfl, totK_node, tot4312, tot4313]
  decide +kernel

theorem arows4308 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4308 = true := by
  rw [show D2M8K2.u4308 = KTree.node D2M8K2.t4314 (nat_lit 9881906) (nat_lit 3886780097) (nat_lit 0) D2M8K2.t4315 from rfl, allE_node, rows4314, irow4308, rows4315]
  all_goals rfl

theorem atot4308 : totK PD2M8K2 D2M8K2.u4308 = [0, 0, 283851949190, 851009494645, 606620509439, 62407195888, 0, 0] := by
  rw [show D2M8K2.u4308 = KTree.node D2M8K2.t4314 (nat_lit 9881906) (nat_lit 3886780097) (nat_lit 0) D2M8K2.t4315 from rfl, totK_node, tot4314, tot4315]
  decide +kernel

theorem arows4310 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4310 = true := by
  rw [show D2M8K2.u4310 = KTree.node D2M8K2.t4316 (nat_lit 9883664) (nat_lit 3815758046) (nat_lit 0) D2M8K2.t4317 from rfl, allE_node, rows4316, irow4310, rows4317]
  all_goals rfl

theorem atot4310 : totK PD2M8K2 D2M8K2.u4310 = [0, 0, 118521934009, 596702167950, 808383678517, 249490787113, 9216081867, 0] := by
  rw [show D2M8K2.u4310 = KTree.node D2M8K2.t4316 (nat_lit 9883664) (nat_lit 3815758046) (nat_lit 0) D2M8K2.t4317 from rfl, totK_node, tot4316, tot4317]
  decide +kernel

theorem arows4311 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4311 = true := by
  rw [show D2M8K2.u4311 = KTree.node D2M8K2.t4318 (nat_lit 9885067) (nat_lit 1813946904) (nat_lit 0) D2M8K2.t4319 from rfl, allE_node, rows4318, irow4311, rows4319]
  all_goals rfl

theorem atot4311 : totK PD2M8K2 D2M8K2.u4311 = [0, 0, 316580252000, 905136610211, 549744700265, 48883962894, 0, 0] := by
  rw [show D2M8K2.u4311 = KTree.node D2M8K2.t4318 (nat_lit 9885067) (nat_lit 1813946904) (nat_lit 0) D2M8K2.t4319 from rfl, totK_node, tot4318, tot4319]
  decide +kernel

theorem arows4316 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4316 = true := by
  rw [show D2M8K2.u4316 = KTree.node D2M8K2.t4320 (nat_lit 9887041) (nat_lit 1548237003) (nat_lit 0) D2M8K2.t4321 from rfl, allE_node, rows4320, irow4316, rows4321]
  all_goals rfl

theorem atot4316 : totK PD2M8K2 D2M8K2.u4316 = [0, 0, 0, 531429909314, 1036403716497, 228954148903, 2586295899, 0] := by
  rw [show D2M8K2.u4316 = KTree.node D2M8K2.t4320 (nat_lit 9887041) (nat_lit 1548237003) (nat_lit 0) D2M8K2.t4321 from rfl, totK_node, tot4320, tot4321]
  decide +kernel

theorem arows4317 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4317 = true := by
  rw [show D2M8K2.u4317 = KTree.node D2M8K2.t4322 (nat_lit 9894913) (nat_lit 1105148087) (nat_lit 0) D2M8K2.t4323 from rfl, allE_node, rows4322, irow4317, rows4323]
  all_goals rfl

theorem atot4317 : totK PD2M8K2 D2M8K2.u4317 = [0, 0, 0, 400307308455, 966715508703, 401616825355, 28418235757, 0] := by
  rw [show D2M8K2.u4317 = KTree.node D2M8K2.t4322 (nat_lit 9894913) (nat_lit 1105148087) (nat_lit 0) D2M8K2.t4323 from rfl, totK_node, tot4322, tot4323]
  decide +kernel

theorem arows4319 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4319 = true := by
  rw [show D2M8K2.u4319 = KTree.node D2M8K2.t4324 (nat_lit 9896142) (nat_lit 3766152532) (nat_lit 0) D2M8K2.t4325 from rfl, allE_node, rows4324, irow4319, rows4325]
  all_goals rfl

theorem atot4319 : totK PD2M8K2 D2M8K2.u4319 = [0, 0, 0, 360709612006, 954611263029, 451590044750, 25729391676, 0] := by
  rw [show D2M8K2.u4319 = KTree.node D2M8K2.t4324 (nat_lit 9896142) (nat_lit 3766152532) (nat_lit 0) D2M8K2.t4325 from rfl, totK_node, tot4324, tot4325]
  decide +kernel

theorem arows4320 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4320 = true := by
  rw [show D2M8K2.u4320 = KTree.node D2M8K2.t4326 (nat_lit 9899444) (nat_lit 2331052281) (nat_lit 0) D2M8K2.t4327 from rfl, allE_node, rows4326, irow4320, rows4327]
  all_goals rfl

theorem atot4320 : totK PD2M8K2 D2M8K2.u4320 = [0, 0, 0, 411432645590, 973781139588, 387674230593, 16258141315, 0] := by
  rw [show D2M8K2.u4320 = KTree.node D2M8K2.t4326 (nat_lit 9899444) (nat_lit 2331052281) (nat_lit 0) D2M8K2.t4327 from rfl, totK_node, tot4326, tot4327]
  decide +kernel

theorem arows4323 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4323 = true := by
  rw [show D2M8K2.u4323 = KTree.node D2M8K2.t4328 (nat_lit 9902784) (nat_lit 3061585842) (nat_lit 0) D2M8K2.t4329 from rfl, allE_node, rows4328, irow4323, rows4329]
  all_goals rfl

theorem atot4323 : totK PD2M8K2 D2M8K2.u4323 = [0, 0, 0, 384276999670, 970088760923, 426490640339, 15094672668, 0] := by
  rw [show D2M8K2.u4323 = KTree.node D2M8K2.t4328 (nat_lit 9902784) (nat_lit 3061585842) (nat_lit 0) D2M8K2.t4329 from rfl, totK_node, tot4328, tot4329]
  decide +kernel

theorem arows4324 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4324 = true := by
  rw [show D2M8K2.u4324 = KTree.node D2M8K2.t4330 (nat_lit 9905858) (nat_lit 4021558888) (nat_lit 0) D2M8K2.t4331 from rfl, allE_node, rows4330, irow4324, rows4331]
  all_goals rfl

theorem atot4324 : totK PD2M8K2 D2M8K2.u4324 = [0, 0, 0, 300490025950, 910423328254, 530173572714, 35670353789, 0] := by
  rw [show D2M8K2.u4324 = KTree.node D2M8K2.t4330 (nat_lit 9905858) (nat_lit 4021558888) (nat_lit 0) D2M8K2.t4331 from rfl, totK_node, tot4330, tot4331]
  decide +kernel

theorem arows4326 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4326 = true := by
  rw [show D2M8K2.u4326 = KTree.node D2M8K2.t4332 (nat_lit 9907953) (nat_lit 1538960058) (nat_lit 0) D2M8K2.t4333 from rfl, allE_node, rows4332, irow4326, rows4333]
  all_goals rfl

theorem atot4326 : totK PD2M8K2 D2M8K2.u4326 = [0, 0, 233978599543, 451420361553, 442719512246, 539377912721, 112417467604, 1429815836] := by
  rw [show D2M8K2.u4326 = KTree.node D2M8K2.t4332 (nat_lit 9907953) (nat_lit 1538960058) (nat_lit 0) D2M8K2.t4333 from rfl, totK_node, tot4332, tot4333]
  decide +kernel

theorem arows4327 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4327 = true := by
  rw [show D2M8K2.u4327 = KTree.node D2M8K2.t4334 (nat_lit 9914244) (nat_lit 3223530506) (nat_lit 0) D2M8K2.t4335 from rfl, allE_node, rows4334, irow4327, rows4335]
  all_goals rfl

theorem atot4327 : totK PD2M8K2 D2M8K2.u4327 = [0, 0, 182396533245, 832411858560, 744841582142, 83416102303, 0, 0] := by
  rw [show D2M8K2.u4327 = KTree.node D2M8K2.t4334 (nat_lit 9914244) (nat_lit 3223530506) (nat_lit 0) D2M8K2.t4335 from rfl, totK_node, tot4334, tot4335]
  decide +kernel

theorem arows4331 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4331 = true := by
  rw [show D2M8K2.u4331 = KTree.node D2M8K2.t4336 (nat_lit 9916384) (nat_lit 1381749764) (nat_lit 0) D2M8K2.t4337 from rfl, allE_node, rows4336, irow4331, rows4337]
  all_goals rfl

theorem atot4331 : totK PD2M8K2 D2M8K2.u4331 = [0, 0, 337745090064, 912485381293, 528483093813, 47769594161, 0, 0] := by
  rw [show D2M8K2.u4331 = KTree.node D2M8K2.t4336 (nat_lit 9916384) (nat_lit 1381749764) (nat_lit 0) D2M8K2.t4337 from rfl, totK_node, tot4336, tot4337]
  decide +kernel

theorem arows4332 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4332 = true := by
  rw [show D2M8K2.u4332 = KTree.node D2M8K2.t4338 (nat_lit 9917886) (nat_lit 3971616199) (nat_lit 0) D2M8K2.t4339 from rfl, allE_node, rows4338, irow4332, rows4339]
  all_goals rfl

theorem atot4332 : totK PD2M8K2 D2M8K2.u4332 = [0, 0, 0, 391227752449, 939581724885, 439882555781, 30675760985, 0] := by
  rw [show D2M8K2.u4332 = KTree.node D2M8K2.t4338 (nat_lit 9917886) (nat_lit 3971616199) (nat_lit 0) D2M8K2.t4339 from rfl, totK_node, tot4338, tot4339]
  decide +kernel

theorem arows4334 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4334 = true := by
  rw [show D2M8K2.u4334 = KTree.node D2M8K2.t4340 (nat_lit 9919231) (nat_lit 2322872439) (nat_lit 0) D2M8K2.t4341 from rfl, allE_node, rows4340, irow4334, rows4341]
  all_goals rfl

theorem atot4334 : totK PD2M8K2 D2M8K2.u4334 = [0, 0, 335000339346, 833980152148, 509818858750, 127136368974, 6804944647, 0] := by
  rw [show D2M8K2.u4334 = KTree.node D2M8K2.t4340 (nat_lit 9919231) (nat_lit 2322872439) (nat_lit 0) D2M8K2.t4341 from rfl, totK_node, tot4340, tot4341]
  decide +kernel

theorem arows4335 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4335 = true := by
  rw [show D2M8K2.u4335 = KTree.node D2M8K2.t4342 (nat_lit 9920838) (nat_lit 3101367827) (nat_lit 0) D2M8K2.t4343 from rfl, allE_node, rows4342, irow4335, rows4343]
  all_goals rfl

theorem atot4335 : totK PD2M8K2 D2M8K2.u4335 = [0, 0, 78537910171, 580305220762, 894660748720, 236907345524, 6581970177, 0] := by
  rw [show D2M8K2.u4335 = KTree.node D2M8K2.t4342 (nat_lit 9920838) (nat_lit 3101367827) (nat_lit 0) D2M8K2.t4343 from rfl, totK_node, tot4342, tot4343]
  decide +kernel

theorem arows4338 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4338 = true := by
  rw [show D2M8K2.u4338 = KTree.node D2M8K2.t4344 (nat_lit 9922725) (nat_lit 1390080407) (nat_lit 0) D2M8K2.t4345 from rfl, allE_node, rows4344, irow4338, rows4345]
  all_goals rfl

theorem atot4338 : totK PD2M8K2 D2M8K2.u4338 = [0, 0, 360499312245, 926016322759, 497942765060, 49151118206, 0, 0] := by
  rw [show D2M8K2.u4338 = KTree.node D2M8K2.t4344 (nat_lit 9922725) (nat_lit 1390080407) (nat_lit 0) D2M8K2.t4345 from rfl, totK_node, tot4344, tot4345]
  decide +kernel

theorem arows4339 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4339 = true := by
  rw [show D2M8K2.u4339 = KTree.node D2M8K2.t4346 (nat_lit 9924329) (nat_lit 1177200892) (nat_lit 0) D2M8K2.t4347 from rfl, allE_node, rows4346, irow4339, rows4347]
  all_goals rfl

theorem atot4339 : totK PD2M8K2 D2M8K2.u4339 = [0, 0, 53287976846, 559784424549, 924347682417, 250007114229, 6654590951, 0] := by
  rw [show D2M8K2.u4339 = KTree.node D2M8K2.t4346 (nat_lit 9924329) (nat_lit 1177200892) (nat_lit 0) D2M8K2.t4347 from rfl, totK_node, tot4346, tot4347]
  decide +kernel

theorem arows4341 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4341 = true := by
  rw [show D2M8K2.u4341 = KTree.node D2M8K2.t4348 (nat_lit 9929644) (nat_lit 3823409457) (nat_lit 0) D2M8K2.t4349 from rfl, allE_node, rows4348, irow4341, rows4349]
  all_goals rfl

theorem atot4341 : totK PD2M8K2 D2M8K2.u4341 = [0, 0, 348279734651, 912132482821, 517026086733, 50707061807, 0, 0] := by
  rw [show D2M8K2.u4341 = KTree.node D2M8K2.t4348 (nat_lit 9929644) (nat_lit 3823409457) (nat_lit 0) D2M8K2.t4349 from rfl, totK_node, tot4348, tot4349]
  decide +kernel

theorem arows4342 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4342 = true := by
  rw [show D2M8K2.u4342 = KTree.node D2M8K2.t4350 (nat_lit 9931162) (nat_lit 3950404598) (nat_lit 0) D2M8K2.t4351 from rfl, allE_node, rows4350, irow4342, rows4351]
  all_goals rfl

theorem atot4342 : totK PD2M8K2 D2M8K2.u4342 = [0, 0, 93768764846, 590333969811, 886775771547, 231427076243, 2418991907, 0] := by
  rw [show D2M8K2.u4342 = KTree.node D2M8K2.t4350 (nat_lit 9931162) (nat_lit 3950404598) (nat_lit 0) D2M8K2.t4351 from rfl, totK_node, tot4350, tot4351]
  decide +kernel

theorem arows4350 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4350 = true := by
  rw [show D2M8K2.u4350 = KTree.node D2M8K2.t4352 (nat_lit 9933430) (nat_lit 3446634464) (nat_lit 0) D2M8K2.t4353 from rfl, allE_node, rows4352, irow4350, rows4353]
  all_goals rfl

theorem atot4350 : totK PD2M8K2 D2M8K2.u4350 = [0, 0, 0, 500036605201, 903905511990, 385502233144, 33656702577, 0] := by
  rw [show D2M8K2.u4350 = KTree.node D2M8K2.t4352 (nat_lit 9933430) (nat_lit 3446634464) (nat_lit 0) D2M8K2.t4353 from rfl, totK_node, tot4352, tot4353]
  decide +kernel

theorem arows4351 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4351 = true := by
  rw [show D2M8K2.u4351 = KTree.node D2M8K2.t4354 (nat_lit 9937198) (nat_lit 3433129622) (nat_lit 0) D2M8K2.t4355 from rfl, allE_node, rows4354, irow4351, rows4355]
  all_goals rfl

theorem atot4351 : totK PD2M8K2 D2M8K2.u4351 = [0, 0, 0, 403575590666, 929075963909, 444347829154, 22759576676, 0] := by
  rw [show D2M8K2.u4351 = KTree.node D2M8K2.t4354 (nat_lit 9937198) (nat_lit 3433129622) (nat_lit 0) D2M8K2.t4355 from rfl, totK_node, tot4354, tot4355]
  decide +kernel

theorem arows4353 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4353 = true := by
  rw [show D2M8K2.u4353 = KTree.node D2M8K2.t4356 (nat_lit 9940224) (nat_lit 3419229445) (nat_lit 0) D2M8K2.t4357 from rfl, allE_node, rows4356, irow4353, rows4357]
  all_goals rfl

theorem atot4353 : totK PD2M8K2 D2M8K2.u4353 = [0, 0, 0, 332243482830, 924855012925, 504159660777, 36093196441, 0] := by
  rw [show D2M8K2.u4353 = KTree.node D2M8K2.t4356 (nat_lit 9940224) (nat_lit 3419229445) (nat_lit 0) D2M8K2.t4357 from rfl, totK_node, tot4356, tot4357]
  decide +kernel

theorem arows4354 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4354 = true := by
  rw [show D2M8K2.u4354 = KTree.node D2M8K2.t4358 (nat_lit 9942686) (nat_lit 3538997172) (nat_lit 0) D2M8K2.t4359 from rfl, allE_node, rows4358, irow4354, rows4359]
  all_goals rfl

theorem atot4354 : totK PD2M8K2 D2M8K2.u4354 = [0, 0, 0, 180201175960, 755718456191, 736245570084, 106584358261, 1323630408] := by
  rw [show D2M8K2.u4354 = KTree.node D2M8K2.t4358 (nat_lit 9942686) (nat_lit 3538997172) (nat_lit 0) D2M8K2.t4359 from rfl, totK_node, tot4358, tot4359]
  decide +kernel

theorem arows4357 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4357 = true := by
  rw [show D2M8K2.u4357 = KTree.node D2M8K2.t4360 (nat_lit 9944486) (nat_lit 4005331914) (nat_lit 0) D2M8K2.t4361 from rfl, allE_node, rows4360, irow4357, rows4361]
  all_goals rfl

theorem atot4357 : totK PD2M8K2 D2M8K2.u4357 = [0, 0, 0, 223799763398, 811132818717, 661247297139, 81869125149, 1332468113] := by
  rw [show D2M8K2.u4357 = KTree.node D2M8K2.t4360 (nat_lit 9944486) (nat_lit 4005331914) (nat_lit 0) D2M8K2.t4361 from rfl, totK_node, tot4360, tot4361]
  decide +kernel

theorem arows4358 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4358 = true := by
  rw [show D2M8K2.u4358 = KTree.node D2M8K2.t4362 (nat_lit 9950248) (nat_lit 3790668661) (nat_lit 0) D2M8K2.t4363 from rfl, allE_node, rows4362, irow4358, rows4363]
  all_goals rfl

theorem atot4358 : totK PD2M8K2 D2M8K2.u4358 = [0, 0, 0, 336631271931, 897384875402, 513393914421, 45075417168, 0] := by
  rw [show D2M8K2.u4358 = KTree.node D2M8K2.t4362 (nat_lit 9950248) (nat_lit 3790668661) (nat_lit 0) D2M8K2.t4363 from rfl, totK_node, tot4362, tot4363]
  decide +kernel

theorem arows4360 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4360 = true := by
  rw [show D2M8K2.u4360 = KTree.node D2M8K2.t4364 (nat_lit 9951896) (nat_lit 3133824977) (nat_lit 0) D2M8K2.t4365 from rfl, allE_node, rows4364, irow4360, rows4365]
  all_goals rfl

theorem atot4360 : totK PD2M8K2 D2M8K2.u4360 = [0, 0, 0, 93211394557, 674691037334, 846507806194, 142616708961, 2465685039] := by
  rw [show D2M8K2.u4360 = KTree.node D2M8K2.t4364 (nat_lit 9951896) (nat_lit 3133824977) (nat_lit 0) D2M8K2.t4365 from rfl, totK_node, tot4364, tot4365]
  decide +kernel

theorem arows4361 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4361 = true := by
  rw [show D2M8K2.u4361 = KTree.node D2M8K2.t4366 (nat_lit 9953912) (nat_lit 3741770008) (nat_lit 0) D2M8K2.t4367 from rfl, allE_node, rows4366, irow4361, rows4367]
  all_goals rfl

theorem atot4361 : totK PD2M8K2 D2M8K2.u4361 = [0, 327677273344, 744594656918, 319603411471, 84124140125, 199281688199, 104581546405, 7068066807] := by
  rw [show D2M8K2.u4361 = KTree.node D2M8K2.t4366 (nat_lit 9953912) (nat_lit 3741770008) (nat_lit 0) D2M8K2.t4367 from rfl, totK_node, tot4366, tot4367]
  decide +kernel

theorem arows4365 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4365 = true := by
  rw [show D2M8K2.u4365 = KTree.node D2M8K2.t4368 (nat_lit 9955147) (nat_lit 1506807898) (nat_lit 0) D2M8K2.t4369 from rfl, allE_node, rows4368, irow4365, rows4369]
  all_goals rfl

theorem atot4365 : totK PD2M8K2 D2M8K2.u4365 = [0, 94118362629, 694444889075, 858740874605, 143333074541, 1369150432, 0, 0] := by
  rw [show D2M8K2.u4365 = KTree.node D2M8K2.t4368 (nat_lit 9955147) (nat_lit 1506807898) (nat_lit 0) D2M8K2.t4369 from rfl, totK_node, tot4368, tot4369]
  decide +kernel

theorem arows4366 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4366 = true := by
  rw [show D2M8K2.u4366 = KTree.node D2M8K2.t4370 (nat_lit 9960748) (nat_lit 3833912465) (nat_lit 0) D2M8K2.t4371 from rfl, allE_node, rows4370, irow4366, rows4371]
  all_goals rfl

theorem atot4366 : totK PD2M8K2 D2M8K2.u4366 = [0, 337632253561, 908488042570, 522374026543, 43222362562, 0, 0, 0] := by
  rw [show D2M8K2.u4366 = KTree.node D2M8K2.t4370 (nat_lit 9960748) (nat_lit 3833912465) (nat_lit 0) D2M8K2.t4371 from rfl, totK_node, tot4370, tot4371]
  decide +kernel

theorem arows4368 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4368 = true := by
  rw [show D2M8K2.u4368 = KTree.node D2M8K2.t4372 (nat_lit 9962266) (nat_lit 3899593997) (nat_lit 0) D2M8K2.t4373 from rfl, allE_node, rows4372, irow4368, rows4373]
  all_goals rfl

theorem atot4368 : totK PD2M8K2 D2M8K2.u4368 = [0, 86871980442, 557718687178, 876703608423, 250696685751, 10568566766, 0, 0] := by
  rw [show D2M8K2.u4368 = KTree.node D2M8K2.t4372 (nat_lit 9962266) (nat_lit 3899593997) (nat_lit 0) D2M8K2.t4373 from rfl, totK_node, tot4372, tot4373]
  decide +kernel

theorem arows4369 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4369 = true := by
  rw [show D2M8K2.u4369 = KTree.node D2M8K2.t4374 (nat_lit 9967574) (nat_lit 4134510003) (nat_lit 0) D2M8K2.t4375 from rfl, allE_node, rows4374, irow4369, rows4375]
  all_goals rfl

theorem atot4369 : totK PD2M8K2 D2M8K2.u4369 = [0, 307661061278, 861346061751, 547874032671, 77114061080, 2481160468, 0, 0] := by
  rw [show D2M8K2.u4369 = KTree.node D2M8K2.t4374 (nat_lit 9967574) (nat_lit 4134510003) (nat_lit 0) D2M8K2.t4375 from rfl, totK_node, tot4374, tot4375]
  decide +kernel

theorem arows4372 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4372 = true := by
  rw [show D2M8K2.u4372 = KTree.node D2M8K2.t4376 (nat_lit 9969179) (nat_lit 2171852252) (nat_lit 0) D2M8K2.t4377 from rfl, allE_node, rows4376, irow4372, rows4377]
  all_goals rfl

theorem atot4372 : totK PD2M8K2 D2M8K2.u4372 = [0, 90236764506, 632501506368, 888779607859, 169570252104, 2165917952, 0, 0] := by
  rw [show D2M8K2.u4372 = KTree.node D2M8K2.t4376 (nat_lit 9969179) (nat_lit 2171852252) (nat_lit 0) D2M8K2.t4377 from rfl, totK_node, tot4376, tot4377]
  decide +kernel

theorem arows4373 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4373 = true := by
  rw [show D2M8K2.u4373 = KTree.node D2M8K2.t4378 (nat_lit 9971183) (nat_lit 2130682150) (nat_lit 0) D2M8K2.t4379 from rfl, allE_node, rows4378, irow4373, rows4379]
  all_goals rfl

theorem atot4373 : totK PD2M8K2 D2M8K2.u4373 = [0, 403352293358, 931588176919, 438454648755, 47078208196, 2814597007, 0, 0] := by
  rw [show D2M8K2.u4373 = KTree.node D2M8K2.t4378 (nat_lit 9971183) (nat_lit 2130682150) (nat_lit 0) D2M8K2.t4379 from rfl, totK_node, tot4378, tot4379]
  decide +kernel

theorem arows4375 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4375 = true := by
  rw [show D2M8K2.u4375 = KTree.node D2M8K2.t4380 (nat_lit 9972909) (nat_lit 1138876443) (nat_lit 0) D2M8K2.t4381 from rfl, allE_node, rows4380, irow4375, rows4381]
  all_goals rfl

theorem atot4375 : totK PD2M8K2 D2M8K2.u4375 = [0, 0, 507013224451, 989015657067, 289819653746, 8697287237, 0, 0] := by
  rw [show D2M8K2.u4375 = KTree.node D2M8K2.t4380 (nat_lit 9972909) (nat_lit 1138876443) (nat_lit 0) D2M8K2.t4381 from rfl, totK_node, tot4380, tot4381]
  decide +kernel

theorem arows4376 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4376 = true := by
  rw [show D2M8K2.u4376 = KTree.node D2M8K2.t4382 (nat_lit 9974890) (nat_lit 3898314748) (nat_lit 0) D2M8K2.t4383 from rfl, allE_node, rows4382, irow4376, rows4383]
  all_goals rfl

theorem atot4376 : totK PD2M8K2 D2M8K2.u4376 = [0, 0, 404594556710, 955163701453, 380003969113, 19863433667, 0, 0] := by
  rw [show D2M8K2.u4376 = KTree.node D2M8K2.t4382 (nat_lit 9974890) (nat_lit 3898314748) (nat_lit 0) D2M8K2.t4383 from rfl, totK_node, tot4382, tot4383]
  decide +kernel

theorem arows4381 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4381 = true := by
  rw [show D2M8K2.u4381 = KTree.node D2M8K2.t4384 (nat_lit 9976690) (nat_lit 3899573183) (nat_lit 0) D2M8K2.t4385 from rfl, allE_node, rows4384, irow4381, rows4385]
  all_goals rfl

theorem atot4381 : totK PD2M8K2 D2M8K2.u4381 = [0, 0, 121666343255, 758668284224, 754464424347, 105432260396, 1369150432, 0] := by
  rw [show D2M8K2.u4381 = KTree.node D2M8K2.t4384 (nat_lit 9976690) (nat_lit 3899573183) (nat_lit 0) D2M8K2.t4385 from rfl, totK_node, tot4384, tot4385]
  decide +kernel

theorem arows4382 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4382 = true := by
  rw [show D2M8K2.u4382 = KTree.node D2M8K2.t4386 (nat_lit 9982142) (nat_lit 3758411305) (nat_lit 0) D2M8K2.t4387 from rfl, allE_node, rows4386, irow4382, rows4387]
  all_goals rfl

theorem atot4382 : totK PD2M8K2 D2M8K2.u4382 = [0, 0, 388716716331, 942456569711, 422537986732, 25145942292, 0, 0] := by
  rw [show D2M8K2.u4382 = KTree.node D2M8K2.t4386 (nat_lit 9982142) (nat_lit 3758411305) (nat_lit 0) D2M8K2.t4387 from rfl, totK_node, tot4386, tot4387]
  decide +kernel

theorem arows4384 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4384 = true := by
  rw [show D2M8K2.u4384 = KTree.node D2M8K2.t4388 (nat_lit 9988669) (nat_lit 983898430) (nat_lit 0) D2M8K2.t4389 from rfl, allE_node, rows4388, irow4384, rows4389]
  all_goals rfl

theorem atot4384 : totK PD2M8K2 D2M8K2.u4384 = [0, 0, 372976397217, 958602251099, 417141657303, 18746791620, 0, 0] := by
  rw [show D2M8K2.u4384 = KTree.node D2M8K2.t4388 (nat_lit 9988669) (nat_lit 983898430) (nat_lit 0) D2M8K2.t4389 from rfl, totK_node, tot4388, tot4389]
  decide +kernel

theorem arows4385 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4385 = true := by
  rw [show D2M8K2.u4385 = KTree.node D2M8K2.t4390 (nat_lit 9992027) (nat_lit 2361985304) (nat_lit 0) D2M8K2.t4391 from rfl, allE_node, rows4390, irow4385, rows4391]
  all_goals rfl

theorem atot4385 : totK PD2M8K2 D2M8K2.u4385 = [0, 0, 353341149825, 950231371068, 472710138680, 22623634463, 0, 0] := by
  rw [show D2M8K2.u4385 = KTree.node D2M8K2.t4390 (nat_lit 9992027) (nat_lit 2361985304) (nat_lit 0) D2M8K2.t4391 from rfl, totK_node, tot4390, tot4391]
  decide +kernel

theorem arows4388 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4388 = true := by
  rw [show D2M8K2.u4388 = KTree.node D2M8K2.t4392 (nat_lit 9998992) (nat_lit 3686841180) (nat_lit 0) D2M8K2.t4393 from rfl, allE_node, rows4392, irow4388, rows4393]
  all_goals rfl

theorem atot4388 : totK PD2M8K2 D2M8K2.u4388 = [0, 356032557978, 914385866063, 508596022096, 68702653755, 7093008096, 0, 0] := by
  rw [show D2M8K2.u4388 = KTree.node D2M8K2.t4392 (nat_lit 9998992) (nat_lit 3686841180) (nat_lit 0) D2M8K2.t4393 from rfl, totK_node, tot4392, tot4393]
  decide +kernel

theorem arows4389 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4389 = true := by
  rw [show D2M8K2.u4389 = KTree.node D2M8K2.t4394 (nat_lit 10000471) (nat_lit 2188946791) (nat_lit 0) D2M8K2.t4395 from rfl, allE_node, rows4394, irow4389, rows4395]
  all_goals rfl

theorem atot4389 : totK PD2M8K2 D2M8K2.u4389 = [0, 89058976036, 510126577158, 828421765219, 374534396033, 29394892645, 0, 0] := by
  rw [show D2M8K2.u4389 = KTree.node D2M8K2.t4394 (nat_lit 10000471) (nat_lit 2188946791) (nat_lit 0) D2M8K2.t4395 from rfl, totK_node, tot4394, tot4395]
  decide +kernel

theorem arows4391 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4391 = true := by
  rw [show D2M8K2.u4391 = KTree.node D2M8K2.t4396 (nat_lit 10001762) (nat_lit 3160816433) (nat_lit 0) D2M8K2.t4397 from rfl, allE_node, rows4396, irow4391, rows4397]
  all_goals rfl

theorem atot4391 : totK PD2M8K2 D2M8K2.u4391 = [0, 234662366559, 685412702477, 690076293572, 222106467335, 8214505460, 0, 0] := by
  rw [show D2M8K2.u4391 = KTree.node D2M8K2.t4396 (nat_lit 10001762) (nat_lit 3160816433) (nat_lit 0) D2M8K2.t4397 from rfl, totK_node, tot4396, tot4397]
  decide +kernel

theorem arows4392 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4392 = true := by
  rw [show D2M8K2.u4392 = KTree.node D2M8K2.t4398 (nat_lit 10003240) (nat_lit 3829952091) (nat_lit 0) D2M8K2.t4399 from rfl, allE_node, rows4398, irow4392, rows4399]
  all_goals rfl

theorem atot4392 : totK PD2M8K2 D2M8K2.u4392 = [0, 192036550133, 776638679266, 720389106063, 115822654614, 1163840124, 0, 0] := by
  rw [show D2M8K2.u4392 = KTree.node D2M8K2.t4398 (nat_lit 10003240) (nat_lit 3829952091) (nat_lit 0) D2M8K2.t4399 from rfl, totK_node, tot4398, tot4399]
  decide +kernel

theorem arows4396 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4396 = true := by
  rw [show D2M8K2.u4396 = KTree.node D2M8K2.t4400 (nat_lit 10004926) (nat_lit 3839314143) (nat_lit 0) D2M8K2.t4401 from rfl, allE_node, rows4400, irow4396, rows4401]
  all_goals rfl

theorem atot4396 : totK PD2M8K2 D2M8K2.u4396 = [0, 179370853151, 642980641720, 766118532728, 222868006244, 11873025674, 0, 0] := by
  rw [show D2M8K2.u4396 = KTree.node D2M8K2.t4400 (nat_lit 10004926) (nat_lit 3839314143) (nat_lit 0) D2M8K2.t4401 from rfl, totK_node, tot4400, tot4401]
  decide +kernel

theorem arows4397 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4397 = true := by
  rw [show D2M8K2.u4397 = KTree.node D2M8K2.t4402 (nat_lit 10007164) (nat_lit 3734392008) (nat_lit 0) D2M8K2.t4403 from rfl, allE_node, rows4402, irow4397, rows4403]
  all_goals rfl

theorem atot4397 : totK PD2M8K2 D2M8K2.u4397 = [0, 167668652401, 721048824758, 762719794356, 170190829438, 6837044869, 0, 0] := by
  rw [show D2M8K2.u4397 = KTree.node D2M8K2.t4402 (nat_lit 10007164) (nat_lit 3734392008) (nat_lit 0) D2M8K2.t4403 from rfl, totK_node, tot4402, tot4403]
  decide +kernel

theorem arows4399 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4399 = true := by
  rw [show D2M8K2.u4399 = KTree.node D2M8K2.t4404 (nat_lit 10009000) (nat_lit 3700599928) (nat_lit 0) D2M8K2.t4405 from rfl, allE_node, rows4404, irow4399, rows4405]
  all_goals rfl

theorem atot4399 : totK PD2M8K2 D2M8K2.u4399 = [0, 320877065619, 828604622215, 562888386967, 108793764928, 2338431331, 0, 0] := by
  rw [show D2M8K2.u4399 = KTree.node D2M8K2.t4404 (nat_lit 10009000) (nat_lit 3700599928) (nat_lit 0) D2M8K2.t4405 from rfl, totK_node, tot4404, tot4405]
  decide +kernel

theorem arows4400 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4400 = true := by
  rw [show D2M8K2.u4400 = KTree.node D2M8K2.t4406 (nat_lit 10010618) (nat_lit 4277281942) (nat_lit 0) D2M8K2.t4407 from rfl, allE_node, rows4406, irow4400, rows4407]
  all_goals rfl

theorem atot4400 : totK PD2M8K2 D2M8K2.u4400 = [0, 90950819051, 717189818752, 869697309976, 132457004530, 1096156699, 0, 0] := by
  rw [show D2M8K2.u4400 = KTree.node D2M8K2.t4406 (nat_lit 10010618) (nat_lit 4277281942) (nat_lit 0) D2M8K2.t4407 from rfl, totK_node, tot4406, tot4407]
  decide +kernel

theorem arows4403 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4403 = true := by
  rw [show D2M8K2.u4403 = KTree.node D2M8K2.t4408 (nat_lit 10012558) (nat_lit 3611688590) (nat_lit 0) D2M8K2.t4409 from rfl, allE_node, rows4408, irow4403, rows4409]
  all_goals rfl

theorem atot4403 : totK PD2M8K2 D2M8K2.u4403 = [0, 325124480648, 835174786955, 553405425182, 108963637035, 3880716147, 0, 0] := by
  rw [show D2M8K2.u4403 = KTree.node D2M8K2.t4408 (nat_lit 10012558) (nat_lit 3611688590) (nat_lit 0) D2M8K2.t4409 from rfl, totK_node, tot4408, tot4409]
  decide +kernel

theorem arows4404 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4404 = true := by
  rw [show D2M8K2.u4404 = KTree.node D2M8K2.t4410 (nat_lit 10014118) (nat_lit 3787137797) (nat_lit 0) D2M8K2.t4411 from rfl, allE_node, rows4410, irow4404, rows4411]
  all_goals rfl

theorem atot4404 : totK PD2M8K2 D2M8K2.u4404 = [0, 92350536064, 568756983419, 872597639397, 261611716728, 7395066691, 0, 0] := by
  rw [show D2M8K2.u4404 = KTree.node D2M8K2.t4410 (nat_lit 10014118) (nat_lit 3787137797) (nat_lit 0) D2M8K2.t4411 from rfl, totK_node, tot4410, tot4411]
  decide +kernel

theorem arows4406 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4406 = true := by
  rw [show D2M8K2.u4406 = KTree.node D2M8K2.t4412 (nat_lit 10019474) (nat_lit 4106108950) (nat_lit 0) D2M8K2.t4413 from rfl, allE_node, rows4412, irow4406, rows4413]
  all_goals rfl

theorem atot4406 : totK PD2M8K2 D2M8K2.u4406 = [0, 0, 359732331556, 909485950280, 525559026551, 46630958459, 0, 0] := by
  rw [show D2M8K2.u4406 = KTree.node D2M8K2.t4412 (nat_lit 10019474) (nat_lit 4106108950) (nat_lit 0) D2M8K2.t4413 from rfl, totK_node, tot4412, tot4413]
  decide +kernel

theorem arows4407 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4407 = true := by
  rw [show D2M8K2.u4407 = KTree.node D2M8K2.t4414 (nat_lit 10020990) (nat_lit 3923973663) (nat_lit 0) D2M8K2.t4415 from rfl, allE_node, rows4414, irow4407, rows4415]
  all_goals rfl

theorem atot4407 : totK PD2M8K2 D2M8K2.u4407 = [0, 0, 176187340286, 653465226281, 699383512883, 267971860796, 25191558099, 0] := by
  rw [show D2M8K2.u4407 = KTree.node D2M8K2.t4414 (nat_lit 10020990) (nat_lit 3923973663) (nat_lit 0) D2M8K2.t4415 from rfl, totK_node, tot4414, tot4415]
  decide +kernel

theorem arows4413 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4413 = true := by
  rw [show D2M8K2.u4413 = KTree.node D2M8K2.t4416 (nat_lit 10022180) (nat_lit 2560426922) (nat_lit 0) D2M8K2.t4417 from rfl, allE_node, rows4416, irow4413, rows4417]
  all_goals rfl

theorem atot4413 : totK PD2M8K2 D2M8K2.u4413 = [0, 0, 160196961149, 594334199560, 751755943675, 281458873693, 11730315755, 0] := by
  rw [show D2M8K2.u4413 = KTree.node D2M8K2.t4416 (nat_lit 10022180) (nat_lit 2560426922) (nat_lit 0) D2M8K2.t4417 from rfl, totK_node, tot4416, tot4417]
  decide +kernel

theorem arows4414 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4414 = true := by
  rw [show D2M8K2.u4414 = KTree.node D2M8K2.t4418 (nat_lit 10023702) (nat_lit 2325698309) (nat_lit 0) D2M8K2.t4419 from rfl, allE_node, rows4418, irow4414, rows4419]
  all_goals rfl

theorem atot4414 : totK PD2M8K2 D2M8K2.u4414 = [0, 0, 264870521585, 867706625782, 619953939058, 58233243276, 0, 0] := by
  rw [show D2M8K2.u4414 = KTree.node D2M8K2.t4418 (nat_lit 10023702) (nat_lit 2325698309) (nat_lit 0) D2M8K2.t4419 from rfl, totK_node, tot4418, tot4419]
  decide +kernel

theorem arows4416 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4416 = true := by
  rw [show D2M8K2.u4416 = KTree.node D2M8K2.t4420 (nat_lit 10025574) (nat_lit 2199197217) (nat_lit 0) D2M8K2.t4421 from rfl, allE_node, rows4420, irow4416, rows4421]
  all_goals rfl

theorem atot4416 : totK PD2M8K2 D2M8K2.u4416 = [0, 0, 167887236175, 639338825750, 811719114430, 201926796098, 5159868635, 0] := by
  rw [show D2M8K2.u4416 = KTree.node D2M8K2.t4420 (nat_lit 10025574) (nat_lit 2199197217) (nat_lit 0) D2M8K2.t4421 from rfl, totK_node, tot4420, tot4421]
  decide +kernel

theorem arows4417 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4417 = true := by
  rw [show D2M8K2.u4417 = KTree.node D2M8K2.t4422 (nat_lit 10027471) (nat_lit 2225959971) (nat_lit 0) D2M8K2.t4423 from rfl, allE_node, rows4422, irow4417, rows4423]
  all_goals rfl

theorem atot4417 : totK PD2M8K2 D2M8K2.u4417 = [0, 0, 178057066267, 762909931830, 740535010087, 138297406948, 4031931762, 0] := by
  rw [show D2M8K2.u4417 = KTree.node D2M8K2.t4422 (nat_lit 10027471) (nat_lit 2225959971) (nat_lit 0) D2M8K2.t4423 from rfl, totK_node, tot4422, tot4423]
  decide +kernel

theorem arows4420 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4420 = true := by
  rw [show D2M8K2.u4420 = KTree.node D2M8K2.t4424 (nat_lit 10029683) (nat_lit 2481115563) (nat_lit 0) D2M8K2.t4425 from rfl, allE_node, rows4424, irow4420, rows4425]
  all_goals rfl

theorem atot4420 : totK PD2M8K2 D2M8K2.u4420 = [0, 0, 286582241214, 793259630009, 620728660019, 101986585991, 1186940923, 0] := by
  rw [show D2M8K2.u4420 = KTree.node D2M8K2.t4424 (nat_lit 10029683) (nat_lit 2481115563) (nat_lit 0) D2M8K2.t4425 from rfl, totK_node, tot4424, tot4425]
  decide +kernel

theorem arows4421 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4421 = true := by
  rw [show D2M8K2.u4421 = KTree.node D2M8K2.t4426 (nat_lit 10031362) (nat_lit 3884263210) (nat_lit 0) D2M8K2.t4427 from rfl, allE_node, rows4426, irow4421, rows4427]
  all_goals rfl

theorem atot4421 : totK PD2M8K2 D2M8K2.u4421 = [0, 0, 120735509721, 780908715364, 828042442995, 87467896883, 0, 0] := by
  rw [show D2M8K2.u4421 = KTree.node D2M8K2.t4426 (nat_lit 10031362) (nat_lit 3884263210) (nat_lit 0) D2M8K2.t4427 from rfl, totK_node, tot4426, tot4427]
  decide +kernel

theorem arows4423 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4423 = true := by
  rw [show D2M8K2.u4423 = KTree.node D2M8K2.t4428 (nat_lit 10033325) (nat_lit 2177542753) (nat_lit 0) D2M8K2.t4429 from rfl, allE_node, rows4428, irow4423, rows4429]
  all_goals rfl

theorem atot4423 : totK PD2M8K2 D2M8K2.u4423 = [0, 0, 340971228910, 860342198179, 533871663143, 89710531833, 1415142070, 0] := by
  rw [show D2M8K2.u4423 = KTree.node D2M8K2.t4428 (nat_lit 10033325) (nat_lit 2177542753) (nat_lit 0) D2M8K2.t4429 from rfl, totK_node, tot4428, tot4429]
  decide +kernel

theorem arows4424 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4424 = true := by
  rw [show D2M8K2.u4424 = KTree.node D2M8K2.t4430 (nat_lit 10035123) (nat_lit 3635052595) (nat_lit 0) D2M8K2.t4431 from rfl, allE_node, rows4430, irow4424, rows4431]
  all_goals rfl

theorem atot4424 : totK PD2M8K2 D2M8K2.u4424 = [0, 0, 71186809760, 617202866058, 901913471390, 207909300017, 2484078857, 0] := by
  rw [show D2M8K2.u4424 = KTree.node D2M8K2.t4430 (nat_lit 10035123) (nat_lit 3635052595) (nat_lit 0) D2M8K2.t4431 from rfl, totK_node, tot4430, tot4431]
  decide +kernel

theorem arows4428 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4428 = true := by
  rw [show D2M8K2.u4428 = KTree.node D2M8K2.t4432 (nat_lit 10037013) (nat_lit 1461414518) (nat_lit 0) D2M8K2.t4433 from rfl, allE_node, rows4432, irow4428, rows4433]
  all_goals rfl

theorem atot4428 : totK PD2M8K2 D2M8K2.u4428 = [0, 366691435255, 876744494366, 376906354713, 69857631563, 71937841186, 6818291842, 0] := by
  rw [show D2M8K2.u4428 = KTree.node D2M8K2.t4432 (nat_lit 10037013) (nat_lit 1461414518) (nat_lit 0) D2M8K2.t4433 from rfl, totK_node, tot4432, tot4433]
  decide +kernel

theorem arows4429 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4429 = true := by
  rw [show D2M8K2.u4429 = KTree.node D2M8K2.t4434 (nat_lit 10038655) (nat_lit 1630339313) (nat_lit 0) D2M8K2.t4435 from rfl, allE_node, rows4434, irow4429, rows4435]
  all_goals rfl

theorem atot4429 : totK PD2M8K2 D2M8K2.u4429 = [0, 120995763054, 688300678250, 849087750199, 133959552562, 1369150432, 0, 0] := by
  rw [show D2M8K2.u4429 = KTree.node D2M8K2.t4434 (nat_lit 10038655) (nat_lit 1630339313) (nat_lit 0) D2M8K2.t4435 from rfl, totK_node, tot4434, tot4435]
  decide +kernel

theorem arows4431 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4431 = true := by
  rw [show D2M8K2.u4431 = KTree.node D2M8K2.t4436 (nat_lit 10040767) (nat_lit 2382589703) (nat_lit 0) D2M8K2.t4437 from rfl, allE_node, rows4436, irow4431, rows4437]
  all_goals rfl

theorem atot4431 : totK PD2M8K2 D2M8K2.u4431 = [0, 333611568285, 919247339843, 537874321497, 44199409993, 0, 0, 0] := by
  rw [show D2M8K2.u4431 = KTree.node D2M8K2.t4436 (nat_lit 10040767) (nat_lit 2382589703) (nat_lit 0) D2M8K2.t4437 from rfl, totK_node, tot4436, tot4437]
  decide +kernel

theorem arows4432 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4432 = true := by
  rw [show D2M8K2.u4432 = KTree.node D2M8K2.t4438 (nat_lit 10042188) (nat_lit 2441652066) (nat_lit 0) D2M8K2.t4439 from rfl, allE_node, rows4438, irow4432, rows4439]
  all_goals rfl

theorem atot4432 : totK PD2M8K2 D2M8K2.u4432 = [0, 0, 390505069567, 945224652170, 452257569379, 30763396594, 0, 0] := by
  rw [show D2M8K2.u4432 = KTree.node D2M8K2.t4438 (nat_lit 10042188) (nat_lit 2441652066) (nat_lit 0) D2M8K2.t4439 from rfl, totK_node, tot4438, tot4439]
  decide +kernel

theorem arows4435 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4435 = true := by
  rw [show D2M8K2.u4435 = KTree.node D2M8K2.t4440 (nat_lit 10043526) (nat_lit 3473026599) (nat_lit 0) D2M8K2.t4441 from rfl, allE_node, rows4440, irow4435, rows4441]
  all_goals rfl

theorem atot4435 : totK PD2M8K2 D2M8K2.u4435 = [0, 324107023985, 809783531323, 557854130548, 136894197255, 6777409681, 0, 0] := by
  rw [show D2M8K2.u4435 = KTree.node D2M8K2.t4440 (nat_lit 10043526) (nat_lit 3473026599) (nat_lit 0) D2M8K2.t4441 from rfl, totK_node, tot4440, tot4441]
  decide +kernel

theorem arows4436 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4436 = true := by
  rw [show D2M8K2.u4436 = KTree.node D2M8K2.t4442 (nat_lit 10044969) (nat_lit 1888338108) (nat_lit 0) D2M8K2.t4443 from rfl, allE_node, rows4442, irow4436, rows4443]
  all_goals rfl

theorem atot4436 : totK PD2M8K2 D2M8K2.u4436 = [0, 121787798155, 653498402261, 808452989997, 211125277125, 9587713104, 0, 0] := by
  rw [show D2M8K2.u4436 = KTree.node D2M8K2.t4442 (nat_lit 10044969) (nat_lit 1888338108) (nat_lit 0) D2M8K2.t4443 from rfl, totK_node, tot4442, tot4443]
  decide +kernel

theorem arows4438 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4438 = true := by
  rw [show D2M8K2.u4438 = KTree.node D2M8K2.t4444 (nat_lit 10050210) (nat_lit 2792678300) (nat_lit 0) D2M8K2.t4445 from rfl, allE_node, rows4444, irow4438, rows4445]
  all_goals rfl

theorem atot4438 : totK PD2M8K2 D2M8K2.u4438 = [0, 259272894553, 772650331034, 646669793003, 123527616225, 3462014130, 0, 0] := by
  rw [show D2M8K2.u4438 = KTree.node D2M8K2.t4444 (nat_lit 10050210) (nat_lit 2792678300) (nat_lit 0) D2M8K2.t4445 from rfl, totK_node, tot4444, tot4445]
  decide +kernel

theorem arows4439 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4439 = true := by
  rw [show D2M8K2.u4439 = KTree.node D2M8K2.t4446 (nat_lit 10051458) (nat_lit 2896196656) (nat_lit 0) D2M8K2.t4447 from rfl, allE_node, rows4446, irow4439, rows4447]
  all_goals rfl

theorem atot4439 : totK PD2M8K2 D2M8K2.u4439 = [0, 156771832691, 744308590163, 763319645163, 111358310007, 1096505104, 0, 0] := by
  rw [show D2M8K2.u4439 = KTree.node D2M8K2.t4446 (nat_lit 10051458) (nat_lit 2896196656) (nat_lit 0) D2M8K2.t4447 from rfl, totK_node, tot4446, tot4447]
  decide +kernel

theorem arows4444 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4444 = true := by
  rw [show D2M8K2.u4444 = KTree.node D2M8K2.t4448 (nat_lit 10053771) (nat_lit 2072866109) (nat_lit 0) D2M8K2.t4449 from rfl, allE_node, rows4448, irow4444, rows4449]
  all_goals rfl

theorem atot4444 : totK PD2M8K2 D2M8K2.u4444 = [0, 261174849934, 776818163499, 633712705013, 131881486416, 3884009855, 0, 0] := by
  rw [show D2M8K2.u4444 = KTree.node D2M8K2.t4448 (nat_lit 10053771) (nat_lit 2072866109) (nat_lit 0) D2M8K2.t4449 from rfl, totK_node, tot4448, tot4449]
  decide +kernel

theorem arows4445 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4445 = true := by
  rw [show D2M8K2.u4445 = KTree.node D2M8K2.t4450 (nat_lit 10055282) (nat_lit 3265331881) (nat_lit 0) D2M8K2.t4451 from rfl, allE_node, rows4450, irow4445, rows4451]
  all_goals rfl

theorem atot4445 : totK PD2M8K2 D2M8K2.u4445 = [0, 159630077522, 690135631699, 778107957688, 166880581075, 2304167554, 0, 0] := by
  rw [show D2M8K2.u4445 = KTree.node D2M8K2.t4450 (nat_lit 10055282) (nat_lit 3265331881) (nat_lit 0) D2M8K2.t4451 from rfl, totK_node, tot4450, tot4451]
  decide +kernel

theorem arows4447 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4447 = true := by
  rw [show D2M8K2.u4447 = KTree.node D2M8K2.t4452 (nat_lit 10056970) (nat_lit 3956385772) (nat_lit 0) D2M8K2.t4453 from rfl, allE_node, rows4452, irow4447, rows4453]
  all_goals rfl

theorem atot4447 : totK PD2M8K2 D2M8K2.u4447 = [0, 0, 368700735692, 935267703114, 433416715853, 28066143138, 0, 0] := by
  rw [show D2M8K2.u4447 = KTree.node D2M8K2.t4452 (nat_lit 10056970) (nat_lit 3956385772) (nat_lit 0) D2M8K2.t4453 from rfl, totK_node, tot4452, tot4453]
  decide +kernel

theorem arows4448 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4448 = true := by
  rw [show D2M8K2.u4448 = KTree.node D2M8K2.t4454 (nat_lit 10058606) (nat_lit 2484263351) (nat_lit 0) D2M8K2.t4455 from rfl, allE_node, rows4454, irow4448, rows4455]
  all_goals rfl

theorem atot4448 : totK PD2M8K2 D2M8K2.u4448 = [0, 0, 185146314649, 756492001841, 668375073096, 92534763348, 1206465782, 0] := by
  rw [show D2M8K2.u4448 = KTree.node D2M8K2.t4454 (nat_lit 10058606) (nat_lit 2484263351) (nat_lit 0) D2M8K2.t4455 from rfl, totK_node, tot4454, tot4455]
  decide +kernel

theorem arows4451 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4451 = true := by
  rw [show D2M8K2.u4451 = KTree.node D2M8K2.t4456 (nat_lit 10061031) (nat_lit 3631119225) (nat_lit 0) D2M8K2.t4457 from rfl, allE_node, rows4456, irow4451, rows4457]
  all_goals rfl

theorem atot4451 : totK PD2M8K2 D2M8K2.u4451 = [0, 0, 333724299937, 893170293451, 553789245011, 51123610745, 0, 0] := by
  rw [show D2M8K2.u4451 = KTree.node D2M8K2.t4456 (nat_lit 10061031) (nat_lit 3631119225) (nat_lit 0) D2M8K2.t4457 from rfl, totK_node, tot4456, tot4457]
  decide +kernel

theorem arows4452 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4452 = true := by
  rw [show D2M8K2.u4452 = KTree.node D2M8K2.t4458 (nat_lit 10064028) (nat_lit 3376604385) (nat_lit 0) D2M8K2.t4459 from rfl, allE_node, rows4458, irow4452, rows4459]
  all_goals rfl

theorem atot4452 : totK PD2M8K2 D2M8K2.u4452 = [0, 0, 355784012185, 950165832875, 479020533808, 31562106747, 0, 0] := by
  rw [show D2M8K2.u4452 = KTree.node D2M8K2.t4458 (nat_lit 10064028) (nat_lit 3376604385) (nat_lit 0) D2M8K2.t4459 from rfl, totK_node, tot4458, tot4459]
  decide +kernel

theorem arows4454 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4454 = true := by
  rw [show D2M8K2.u4454 = KTree.node D2M8K2.t4460 (nat_lit 10065521) (nat_lit 1582786887) (nat_lit 0) D2M8K2.t4461 from rfl, allE_node, rows4460, irow4454, rows4461]
  all_goals rfl

theorem atot4454 : totK PD2M8K2 D2M8K2.u4454 = [0, 0, 175521683754, 766830190683, 725624984269, 113778464210, 1162935789, 0] := by
  rw [show D2M8K2.u4454 = KTree.node D2M8K2.t4460 (nat_lit 10065521) (nat_lit 1582786887) (nat_lit 0) D2M8K2.t4461 from rfl, totK_node, tot4460, tot4461]
  decide +kernel

theorem arows4455 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4455 = true := by
  rw [show D2M8K2.u4455 = KTree.node D2M8K2.t4462 (nat_lit 10070853) (nat_lit 1513477156) (nat_lit 0) D2M8K2.t4463 from rfl, allE_node, rows4462, irow4455, rows4463]
  all_goals rfl

theorem atot4455 : totK PD2M8K2 D2M8K2.u4455 = [0, 0, 235715843976, 697273799309, 620607457018, 186751792029, 11853261585, 0] := by
  rw [show D2M8K2.u4455 = KTree.node D2M8K2.t4462 (nat_lit 10070853) (nat_lit 1513477156) (nat_lit 0) D2M8K2.t4463 from rfl, totK_node, tot4462, tot4463]
  decide +kernel

theorem arows4459 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4459 = true := by
  rw [show D2M8K2.u4459 = KTree.node D2M8K2.t4464 (nat_lit 10072112) (nat_lit 3813571117) (nat_lit 0) D2M8K2.t4465 from rfl, allE_node, rows4464, irow4459, rows4465]
  all_goals rfl

theorem atot4459 : totK PD2M8K2 D2M8K2.u4459 = [0, 0, 174976021207, 784042873861, 683909259230, 88586344794, 1021600638, 0] := by
  rw [show D2M8K2.u4459 = KTree.node D2M8K2.t4464 (nat_lit 10072112) (nat_lit 3813571117) (nat_lit 0) D2M8K2.t4465 from rfl, totK_node, tot4464, tot4465]
  decide +kernel

theorem arows4460 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4460 = true := by
  rw [show D2M8K2.u4460 = KTree.node D2M8K2.t4466 (nat_lit 10074511) (nat_lit 1813807556) (nat_lit 0) D2M8K2.t4467 from rfl, allE_node, rows4466, irow4460, rows4467]
  all_goals rfl

theorem atot4460 : totK PD2M8K2 D2M8K2.u4460 = [0, 0, 259932257946, 798607243752, 593629934330, 102851197821, 3552795014, 0] := by
  rw [show D2M8K2.u4460 = KTree.node D2M8K2.t4466 (nat_lit 10074511) (nat_lit 1813807556) (nat_lit 0) D2M8K2.t4467 from rfl, totK_node, tot4466, tot4467]
  decide +kernel

theorem arows4462 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4462 = true := by
  rw [show D2M8K2.u4462 = KTree.node D2M8K2.t4468 (nat_lit 10119236) (nat_lit 3308106591) (nat_lit 0) D2M8K2.t4469 from rfl, allE_node, rows4468, irow4462, rows4469]
  all_goals rfl

theorem atot4462 : totK PD2M8K2 D2M8K2.u4462 = [0, 237285610696, 681543169731, 619383266040, 238223319926, 15906108236, 0, 0] := by
  rw [show D2M8K2.u4462 = KTree.node D2M8K2.t4468 (nat_lit 10119236) (nat_lit 3308106591) (nat_lit 0) D2M8K2.t4469 from rfl, totK_node, tot4468, tot4469]
  decide +kernel

theorem arows4463 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4463 = true := by
  rw [show D2M8K2.u4463 = KTree.node D2M8K2.t4470 (nat_lit 10120905) (nat_lit 1819679931) (nat_lit 0) D2M8K2.t4471 from rfl, allE_node, rows4470, irow4463, rows4471]
  all_goals rfl

theorem atot4463 : totK PD2M8K2 D2M8K2.u4463 = [0, 139701420044, 720039277409, 786901026582, 124454736796, 1369150432, 0, 0] := by
  rw [show D2M8K2.u4463 = KTree.node D2M8K2.t4470 (nat_lit 10120905) (nat_lit 1819679931) (nat_lit 0) D2M8K2.t4471 from rfl, totK_node, tot4470, tot4471]
  decide +kernel

theorem arows4466 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4466 = true := by
  rw [show D2M8K2.u4466 = KTree.node D2M8K2.t4472 (nat_lit 10123301) (nat_lit 2338578389) (nat_lit 0) D2M8K2.t4473 from rfl, allE_node, rows4472, irow4466, rows4473]
  all_goals rfl

theorem atot4466 : totK PD2M8K2 D2M8K2.u4466 = [0, 349108718486, 879199784570, 555356476039, 55110003864, 0, 0, 0] := by
  rw [show D2M8K2.u4466 = KTree.node D2M8K2.t4472 (nat_lit 10123301) (nat_lit 2338578389) (nat_lit 0) D2M8K2.t4473 from rfl, totK_node, tot4472, tot4473]
  decide +kernel

theorem arows4467 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4467 = true := by
  rw [show D2M8K2.u4467 = KTree.node D2M8K2.t4474 (nat_lit 10124852) (nat_lit 3068439174) (nat_lit 0) D2M8K2.t4475 from rfl, allE_node, rows4474, irow4467, rows4475]
  all_goals rfl

theorem atot4467 : totK PD2M8K2 D2M8K2.u4467 = [0, 70523670977, 542253292048, 835780102870, 348809853955, 28235592988, 0, 0] := by
  rw [show D2M8K2.u4467 = KTree.node D2M8K2.t4474 (nat_lit 10124852) (nat_lit 3068439174) (nat_lit 0) D2M8K2.t4475 from rfl, totK_node, tot4474, tot4475]
  decide +kernel

theorem arows4469 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4469 = true := by
  rw [show D2M8K2.u4469 = KTree.node D2M8K2.t4476 (nat_lit 10126161) (nat_lit 1788818434) (nat_lit 0) D2M8K2.t4477 from rfl, allE_node, rows4476, irow4469, rows4477]
  all_goals rfl

theorem atot4469 : totK PD2M8K2 D2M8K2.u4469 = [0, 227100036571, 670579815531, 675818777112, 235027163785, 9332673987, 0, 0] := by
  rw [show D2M8K2.u4469 = KTree.node D2M8K2.t4476 (nat_lit 10126161) (nat_lit 1788818434) (nat_lit 0) D2M8K2.t4477 from rfl, totK_node, tot4476, tot4477]
  decide +kernel

theorem arows4470 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4470 = true := by
  rw [show D2M8K2.u4470 = KTree.node D2M8K2.t4478 (nat_lit 10127647) (nat_lit 1670167216) (nat_lit 0) D2M8K2.t4479 from rfl, allE_node, rows4478, irow4470, rows4479]
  all_goals rfl

theorem atot4470 : totK PD2M8K2 D2M8K2.u4470 = [0, 196535592938, 773287975413, 705934448650, 113450688426, 1164319620, 0, 0] := by
  rw [show D2M8K2.u4470 = KTree.node D2M8K2.t4478 (nat_lit 10127647) (nat_lit 1670167216) (nat_lit 0) D2M8K2.t4479 from rfl, totK_node, tot4478, tot4479]
  decide +kernel

theorem arows4477 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4477 = true := by
  rw [show D2M8K2.u4477 = KTree.node D2M8K2.t4480 (nat_lit 10129369) (nat_lit 1469261372) (nat_lit 0) D2M8K2.t4481 from rfl, allE_node, rows4480, irow4477, rows4481]
  all_goals rfl

theorem atot4477 : totK PD2M8K2 D2M8K2.u4477 = [0, 187260791026, 645775371269, 731704418335, 221235752944, 11885407614, 0, 0] := by
  rw [show D2M8K2.u4477 = KTree.node D2M8K2.t4480 (nat_lit 10129369) (nat_lit 1469261372) (nat_lit 0) D2M8K2.t4481 from rfl, totK_node, tot4480, tot4481]
  decide +kernel

theorem arows4478 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4478 = true := by
  rw [show D2M8K2.u4478 = KTree.node D2M8K2.t4482 (nat_lit 10131358) (nat_lit 3070051441) (nat_lit 0) D2M8K2.t4483 from rfl, allE_node, rows4482, irow4478, rows4483]
  all_goals rfl

theorem atot4478 : totK PD2M8K2 D2M8K2.u4478 = [0, 139955743058, 718451252811, 772132105172, 168465410580, 8470662040, 0, 0] := by
  rw [show D2M8K2.u4478 = KTree.node D2M8K2.t4482 (nat_lit 10131358) (nat_lit 3070051441) (nat_lit 0) D2M8K2.t4483 from rfl, totK_node, tot4482, tot4483]
  decide +kernel

theorem arows4480 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4480 = true := by
  rw [show D2M8K2.u4480 = KTree.node D2M8K2.t4484 (nat_lit 10133476) (nat_lit 3994297237) (nat_lit 0) D2M8K2.t4485 from rfl, allE_node, rows4484, irow4480, rows4485]
  all_goals rfl

theorem atot4480 : totK PD2M8K2 D2M8K2.u4480 = [0, 342998253845, 839069921956, 516810027275, 94892612550, 3581949829, 0, 0] := by
  rw [show D2M8K2.u4480 = KTree.node D2M8K2.t4484 (nat_lit 10133476) (nat_lit 3994297237) (nat_lit 0) D2M8K2.t4485 from rfl, totK_node, tot4484, tot4485]
  decide +kernel

theorem arows4481 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4481 = true := by
  rw [show D2M8K2.u4481 = KTree.node D2M8K2.t4486 (nat_lit 10134985) (nat_lit 1361328263) (nat_lit 0) D2M8K2.t4487 from rfl, allE_node, rows4486, irow4481, rows4487]
  all_goals rfl

theorem atot4481 : totK PD2M8K2 D2M8K2.u4481 = [0, 92722701599, 696563685272, 874700137110, 143400140895, 1096505104, 0, 0] := by
  rw [show D2M8K2.u4481 = KTree.node D2M8K2.t4486 (nat_lit 10134985) (nat_lit 1361328263) (nat_lit 0) D2M8K2.t4487 from rfl, totK_node, tot4486, tot4487]
  decide +kernel

theorem arows4484 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4484 = true := by
  rw [show D2M8K2.u4484 = KTree.node D2M8K2.t4488 (nat_lit 10140650) (nat_lit 3988968956) (nat_lit 0) D2M8K2.t4489 from rfl, allE_node, rows4488, irow4484, rows4489]
  all_goals rfl

theorem atot4484 : totK PD2M8K2 D2M8K2.u4484 = [0, 0, 359405562896, 945310171150, 421714584677, 21257991002, 0, 0] := by
  rw [show D2M8K2.u4484 = KTree.node D2M8K2.t4488 (nat_lit 10140650) (nat_lit 3988968956) (nat_lit 0) D2M8K2.t4489 from rfl, totK_node, tot4488, tot4489]
  decide +kernel

theorem arows4485 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4485 = true := by
  rw [show D2M8K2.u4485 = KTree.node D2M8K2.t4490 (nat_lit 10142599) (nat_lit 2383902045) (nat_lit 0) D2M8K2.t4491 from rfl, allE_node, rows4490, irow4485, rows4491]
  all_goals rfl

theorem atot4485 : totK PD2M8K2 D2M8K2.u4485 = [0, 0, 146639780917, 738972130576, 752250979559, 106928462158, 1138244013, 0] := by
  rw [show D2M8K2.u4485 = KTree.node D2M8K2.t4490 (nat_lit 10142599) (nat_lit 2383902045) (nat_lit 0) D2M8K2.t4491 from rfl, totK_node, tot4490, tot4491]
  decide +kernel

theorem arows4487 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4487 = true := by
  rw [show D2M8K2.u4487 = KTree.node D2M8K2.t4492 (nat_lit 10144580) (nat_lit 3388110699) (nat_lit 0) D2M8K2.t4493 from rfl, allE_node, rows4492, irow4487, rows4493]
  all_goals rfl

theorem atot4487 : totK PD2M8K2 D2M8K2.u4487 = [0, 0, 390203769883, 959676947038, 437109937817, 25186188838, 0, 0] := by
  rw [show D2M8K2.u4487 = KTree.node D2M8K2.t4492 (nat_lit 10144580) (nat_lit 3388110699) (nat_lit 0) D2M8K2.t4493 from rfl, totK_node, tot4492, tot4493]
  decide +kernel

theorem arows4488 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4488 = true := by
  rw [show D2M8K2.u4488 = KTree.node D2M8K2.t4494 (nat_lit 10147597) (nat_lit 1193301329) (nat_lit 0) D2M8K2.t4495 from rfl, allE_node, rows4494, irow4488, rows4495]
  all_goals rfl

theorem atot4488 : totK PD2M8K2 D2M8K2.u4488 = [0, 0, 357494576343, 949009525807, 469136247106, 25897365295, 0, 0] := by
  rw [show D2M8K2.u4488 = KTree.node D2M8K2.t4494 (nat_lit 10147597) (nat_lit 1193301329) (nat_lit 0) D2M8K2.t4495 from rfl, totK_node, tot4494, tot4495]
  decide +kernel

theorem arows4492 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4492 = true := by
  rw [show D2M8K2.u4492 = KTree.node D2M8K2.t4496 (nat_lit 10151266) (nat_lit 3999950474) (nat_lit 0) D2M8K2.t4497 from rfl, allE_node, rows4496, irow4492, rows4497]
  all_goals rfl

theorem atot4492 : totK PD2M8K2 D2M8K2.u4492 = [0, 0, 391493486737, 952518222094, 432549699352, 24801601685, 0, 0] := by
  rw [show D2M8K2.u4492 = KTree.node D2M8K2.t4496 (nat_lit 10151266) (nat_lit 3999950474) (nat_lit 0) D2M8K2.t4497 from rfl, totK_node, tot4496, tot4497]
  decide +kernel

theorem arows4493 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4493 = true := by
  rw [show D2M8K2.u4493 = KTree.node D2M8K2.t4498 (nat_lit 10154499) (nat_lit 2919962776) (nat_lit 0) D2M8K2.t4499 from rfl, allE_node, rows4498, irow4493, rows4499]
  all_goals rfl

theorem atot4493 : totK PD2M8K2 D2M8K2.u4493 = [0, 0, 350918819336, 936179363615, 469614331281, 32335567562, 0, 0] := by
  rw [show D2M8K2.u4493 = KTree.node D2M8K2.t4498 (nat_lit 10154499) (nat_lit 2919962776) (nat_lit 0) D2M8K2.t4499 from rfl, totK_node, tot4498, tot4499]
  decide +kernel

theorem arows4495 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4495 = true := by
  rw [show D2M8K2.u4495 = KTree.node D2M8K2.t4500 (nat_lit 10156350) (nat_lit 3924396447) (nat_lit 0) D2M8K2.t4501 from rfl, allE_node, rows4500, irow4495, rows4501]
  all_goals rfl

theorem atot4495 : totK PD2M8K2 D2M8K2.u4495 = [0, 87687082016, 178372532519, 500513826496, 767177136612, 191134878293, 4977114383, 0] := by
  rw [show D2M8K2.u4495 = KTree.node D2M8K2.t4500 (nat_lit 10156350) (nat_lit 3924396447) (nat_lit 0) D2M8K2.t4501 from rfl, totK_node, tot4500, tot4501]
  decide +kernel

theorem arows4496 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4496 = true := by
  rw [show D2M8K2.u4496 = KTree.node D2M8K2.t4502 (nat_lit 10161854) (nat_lit 3090571811) (nat_lit 0) D2M8K2.t4503 from rfl, allE_node, rows4502, irow4496, rows4503]
  all_goals rfl

theorem atot4496 : totK PD2M8K2 D2M8K2.u4496 = [0, 291345310411, 874463638492, 567805720924, 52984688884, 0, 0, 0] := by
  rw [show D2M8K2.u4496 = KTree.node D2M8K2.t4502 (nat_lit 10161854) (nat_lit 3090571811) (nat_lit 0) D2M8K2.t4503 from rfl, totK_node, tot4502, tot4503]
  decide +kernel

theorem arows4499 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4499 = true := by
  rw [show D2M8K2.u4499 = KTree.node D2M8K2.t4504 (nat_lit 10163947) (nat_lit 1551938790) (nat_lit 0) D2M8K2.t4505 from rfl, allE_node, rows4504, irow4499, rows4505]
  all_goals rfl

theorem atot4499 : totK PD2M8K2 D2M8K2.u4499 = [0, 180654617217, 735621300154, 786189038234, 129072672723, 1369150432, 0, 0] := by
  rw [show D2M8K2.u4499 = KTree.node D2M8K2.t4504 (nat_lit 10163947) (nat_lit 1551938790) (nat_lit 0) D2M8K2.t4505 from rfl, totK_node, tot4504, tot4505]
  decide +kernel

theorem arows4500 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4500 = true := by
  rw [show D2M8K2.u4500 = KTree.node D2M8K2.t4506 (nat_lit 10165608) (nat_lit 3116902120) (nat_lit 0) D2M8K2.t4507 from rfl, allE_node, rows4506, irow4500, rows4507]
  all_goals rfl

theorem atot4500 : totK PD2M8K2 D2M8K2.u4500 = [0, 240472514928, 766024785782, 626451030802, 194455422016, 21380039407, 0, 0] := by
  rw [show D2M8K2.u4500 = KTree.node D2M8K2.t4506 (nat_lit 10165608) (nat_lit 3116902120) (nat_lit 0) D2M8K2.t4507 from rfl, totK_node, tot4506, tot4507]
  decide +kernel

theorem arows4502 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4502 = true := by
  rw [show D2M8K2.u4502 = KTree.node D2M8K2.t4508 (nat_lit 10167147) (nat_lit 3723877040) (nat_lit 0) D2M8K2.t4509 from rfl, allE_node, rows4508, irow4502, rows4509]
  all_goals rfl

theorem atot4502 : totK PD2M8K2 D2M8K2.u4502 = [0, 83078108543, 480842711641, 852619558420, 372705583116, 16174684836, 0, 0] := by
  rw [show D2M8K2.u4502 = KTree.node D2M8K2.t4508 (nat_lit 10167147) (nat_lit 3723877040) (nat_lit 0) D2M8K2.t4509 from rfl, totK_node, tot4508, tot4509]
  decide +kernel

theorem arows4503 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4503 = true := by
  rw [show D2M8K2.u4503 = KTree.node D2M8K2.t4510 (nat_lit 10168368) (nat_lit 3317645921) (nat_lit 0) D2M8K2.t4511 from rfl, allE_node, rows4510, irow4503, rows4511]
  all_goals rfl

theorem atot4503 : totK PD2M8K2 D2M8K2.u4503 = [0, 341402018016, 913655643867, 530251272757, 47655233800, 0, 0, 0] := by
  rw [show D2M8K2.u4503 = KTree.node D2M8K2.t4510 (nat_lit 10168368) (nat_lit 3317645921) (nat_lit 0) D2M8K2.t4511 from rfl, totK_node, tot4510, tot4511]
  decide +kernel

theorem arows4508 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4508 = true := by
  rw [show D2M8K2.u4508 = KTree.node D2M8K2.t4512 (nat_lit 10170048) (nat_lit 3382949564) (nat_lit 0) D2M8K2.t4513 from rfl, allE_node, rows4512, irow4508, rows4513]
  all_goals rfl

theorem atot4508 : totK PD2M8K2 D2M8K2.u4508 = [0, 67204494367, 522839374356, 898231551975, 283428281722, 13043783340, 0, 0] := by
  rw [show D2M8K2.u4508 = KTree.node D2M8K2.t4512 (nat_lit 10170048) (nat_lit 3382949564) (nat_lit 0) D2M8K2.t4513 from rfl, totK_node, tot4512, tot4513]
  decide +kernel

theorem arows4509 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4509 = true := by
  rw [show D2M8K2.u4509 = KTree.node D2M8K2.t4514 (nat_lit 10172095) (nat_lit 2440169442) (nat_lit 0) D2M8K2.t4515 from rfl, allE_node, rows4514, irow4509, rows4515]
  all_goals rfl

theorem atot4509 : totK PD2M8K2 D2M8K2.u4509 = [0, 263094580822, 818864373041, 657817947154, 100370836885, 1198073392, 0, 0] := by
  rw [show D2M8K2.u4509 = KTree.node D2M8K2.t4514 (nat_lit 10172095) (nat_lit 2440169442) (nat_lit 0) D2M8K2.t4515 from rfl, totK_node, tot4514, tot4515]
  decide +kernel

theorem arows4511 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4511 = true := by
  rw [show D2M8K2.u4511 = KTree.node D2M8K2.t4516 (nat_lit 10177969) (nat_lit 1511572004) (nat_lit 0) D2M8K2.t4517 from rfl, allE_node, rows4516, irow4511, rows4517]
  all_goals rfl

theorem atot4511 : totK PD2M8K2 D2M8K2.u4511 = [0, 210597626795, 727943163129, 715045419379, 172757152410, 7057208448, 0, 0] := by
  rw [show D2M8K2.u4511 = KTree.node D2M8K2.t4516 (nat_lit 10177969) (nat_lit 1511572004) (nat_lit 0) D2M8K2.t4517 from rfl, totK_node, tot4516, tot4517]
  decide +kernel

theorem arows4512 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4512 = true := by
  rw [show D2M8K2.u4512 = KTree.node D2M8K2.t4518 (nat_lit 10179419) (nat_lit 2913744014) (nat_lit 0) D2M8K2.t4519 from rfl, allE_node, rows4518, irow4512, rows4519]
  all_goals rfl

theorem atot4512 : totK PD2M8K2 D2M8K2.u4512 = [0, 229665325098, 787716187536, 676967776675, 115859626876, 1268739303, 0, 0] := by
  rw [show D2M8K2.u4512 = KTree.node D2M8K2.t4518 (nat_lit 10179419) (nat_lit 2913744014) (nat_lit 0) D2M8K2.t4519 from rfl, totK_node, tot4518, tot4519]
  decide +kernel

theorem arows4515 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4515 = true := by
  rw [show D2M8K2.u4515 = KTree.node D2M8K2.t4520 (nat_lit 10181101) (nat_lit 1332509896) (nat_lit 0) D2M8K2.t4521 from rfl, allE_node, rows4520, irow4515, rows4521]
  all_goals rfl

theorem atot4515 : totK PD2M8K2 D2M8K2.u4515 = [0, 0, 399580300255, 960843698014, 394536409198, 22149860293, 0, 0] := by
  rw [show D2M8K2.u4515 = KTree.node D2M8K2.t4520 (nat_lit 10181101) (nat_lit 1332509896) (nat_lit 0) D2M8K2.t4521 from rfl, totK_node, tot4520, tot4521]
  decide +kernel

theorem arows4516 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4516 = true := by
  rw [show D2M8K2.u4516 = KTree.node D2M8K2.t4522 (nat_lit 10182775) (nat_lit 1525798539) (nat_lit 128) D2M8K2.t4523 from rfl, allE_node, rows4522, irow4516, rows4523]
  all_goals rfl

theorem atot4516 : totK PD2M8K2 D2M8K2.u4516 = [0, 0, 261554081080, 823744785834, 598171204659, 77627309007, 1310285577, 0] := by
  rw [show D2M8K2.u4516 = KTree.node D2M8K2.t4522 (nat_lit 10182775) (nat_lit 1525798539) (nat_lit 128) D2M8K2.t4523 from rfl, totK_node, tot4522, tot4523]
  decide +kernel

theorem arows4518 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4518 = true := by
  rw [show D2M8K2.u4518 = KTree.node D2M8K2.t4524 (nat_lit 10185236) (nat_lit 3587206673) (nat_lit 0) D2M8K2.t4525 from rfl, allE_node, rows4524, irow4518, rows4525]
  all_goals rfl

theorem atot4518 : totK PD2M8K2 D2M8K2.u4518 = [0, 0, 242317027472, 815730632429, 699017233462, 71352699856, 0, 0] := by
  rw [show D2M8K2.u4518 = KTree.node D2M8K2.t4524 (nat_lit 10185236) (nat_lit 3587206673) (nat_lit 0) D2M8K2.t4525 from rfl, totK_node, tot4524, tot4525]
  decide +kernel

theorem arows4519 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4519 = true := by
  rw [show D2M8K2.u4519 = KTree.node D2M8K2.t4526 (nat_lit 10186490) (nat_lit 3995047236) (nat_lit 0) D2M8K2.t4527 from rfl, allE_node, rows4526, irow4519, rows4527]
  all_goals rfl

theorem atot4519 : totK PD2M8K2 D2M8K2.u4519 = [0, 0, 348299775840, 937842961007, 504649071214, 35149607030, 0, 0] := by
  rw [show D2M8K2.u4519 = KTree.node D2M8K2.t4526 (nat_lit 10186490) (nat_lit 3995047236) (nat_lit 0) D2M8K2.t4527 from rfl, totK_node, tot4526, tot4527]
  decide +kernel

theorem arows4523 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4523 = true := by
  rw [show D2M8K2.u4523 = KTree.node D2M8K2.t4528 (nat_lit 10189756) (nat_lit 3901800563) (nat_lit 0) D2M8K2.t4529 from rfl, allE_node, rows4528, irow4523, rows4529]
  all_goals rfl

theorem atot4523 : totK PD2M8K2 D2M8K2.u4523 = [0, 0, 251783568183, 807786136065, 633611600460, 87062947882, 1075657031, 0] := by
  rw [show D2M8K2.u4523 = KTree.node D2M8K2.t4528 (nat_lit 10189756) (nat_lit 3901800563) (nat_lit 0) D2M8K2.t4529 from rfl, totK_node, tot4528, tot4529]
  decide +kernel

theorem arows4524 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4524 = true := by
  rw [show D2M8K2.u4524 = KTree.node D2M8K2.t4530 (nat_lit 10191793) (nat_lit 1498263222) (nat_lit 0) D2M8K2.t4531 from rfl, allE_node, rows4530, irow4524, rows4531]
  all_goals rfl

theorem atot4524 : totK PD2M8K2 D2M8K2.u4524 = [0, 0, 221861097508, 755291235879, 689418893926, 131202872701, 3804183361, 0] := by
  rw [show D2M8K2.u4524 = KTree.node D2M8K2.t4530 (nat_lit 10191793) (nat_lit 1498263222) (nat_lit 0) D2M8K2.t4531 from rfl, totK_node, tot4530, tot4531]
  decide +kernel

theorem arows4526 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4526 = true := by
  rw [show D2M8K2.u4526 = KTree.node D2M8K2.t4532 (nat_lit 10193818) (nat_lit 3783495405) (nat_lit 0) D2M8K2.t4533 from rfl, allE_node, rows4532, irow4526, rows4533]
  all_goals rfl

theorem atot4526 : totK PD2M8K2 D2M8K2.u4526 = [0, 0, 180191800645, 764059361936, 749703735982, 118736707818, 1444560764, 0] := by
  rw [show D2M8K2.u4526 = KTree.node D2M8K2.t4532 (nat_lit 10193818) (nat_lit 3783495405) (nat_lit 0) D2M8K2.t4533 from rfl, totK_node, tot4532, tot4533]
  decide +kernel

theorem arows4527 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4527 = true := by
  rw [show D2M8K2.u4527 = KTree.node D2M8K2.t4534 (nat_lit 10199366) (nat_lit 3977188800) (nat_lit 0) D2M8K2.t4535 from rfl, allE_node, rows4534, irow4527, rows4535]
  all_goals rfl

theorem atot4527 : totK PD2M8K2 D2M8K2.u4527 = [0, 0, 366068348958, 945382019058, 487691353811, 31541744139, 0, 0] := by
  rw [show D2M8K2.u4527 = KTree.node D2M8K2.t4534 (nat_lit 10199366) (nat_lit 3977188800) (nat_lit 0) D2M8K2.t4535 from rfl, totK_node, tot4534, tot4535]
  decide +kernel

theorem arows4530 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4530 = true := by
  rw [show D2M8K2.u4530 = KTree.node D2M8K2.t4536 (nat_lit 10201022) (nat_lit 3561066660) (nat_lit 0) D2M8K2.t4537 from rfl, allE_node, rows4536, irow4530, rows4537]
  all_goals rfl

theorem atot4530 : totK PD2M8K2 D2M8K2.u4530 = [0, 0, 0, 501593811050, 979587594121, 271992825687, 7380459662, 0] := by
  rw [show D2M8K2.u4530 = KTree.node D2M8K2.t4536 (nat_lit 10201022) (nat_lit 3561066660) (nat_lit 0) D2M8K2.t4537 from rfl, totK_node, tot4536, tot4537]
  decide +kernel

theorem arows4531 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4531 = true := by
  rw [show D2M8K2.u4531 = KTree.node D2M8K2.t4538 (nat_lit 10202883) (nat_lit 2971472798) (nat_lit 0) D2M8K2.t4539 from rfl, allE_node, rows4538, irow4531, rows4539]
  all_goals rfl

theorem atot4531 : totK PD2M8K2 D2M8K2.u4531 = [0, 0, 345258147191, 851471565496, 455876624093, 103768939944, 10633692979, 0] := by
  rw [show D2M8K2.u4531 = KTree.node D2M8K2.t4538 (nat_lit 10202883) (nat_lit 2971472798) (nat_lit 0) D2M8K2.t4539 from rfl, totK_node, tot4538, tot4539]
  decide +kernel

theorem arows4533 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4533 = true := by
  rw [show D2M8K2.u4533 = KTree.node D2M8K2.t4540 (nat_lit 10204467) (nat_lit 3370188318) (nat_lit 0) D2M8K2.t4541 from rfl, allE_node, rows4540, irow4533, rows4541]
  all_goals rfl

theorem atot4533 : totK PD2M8K2 D2M8K2.u4533 = [0, 0, 128448588502, 703160213020, 835747303962, 120470466926, 1369150432, 0] := by
  rw [show D2M8K2.u4533 = KTree.node D2M8K2.t4540 (nat_lit 10204467) (nat_lit 3370188318) (nat_lit 0) D2M8K2.t4541 from rfl, totK_node, tot4540, tot4541]
  decide +kernel

theorem arows4534 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4534 = true := by
  rw [show D2M8K2.u4534 = KTree.node D2M8K2.t4542 (nat_lit 10209751) (nat_lit 1162407044) (nat_lit 0) D2M8K2.t4543 from rfl, allE_node, rows4542, irow4534, rows4543]
  all_goals rfl

theorem atot4534 : totK PD2M8K2 D2M8K2.u4534 = [0, 0, 364909923172, 941053617458, 466957435089, 25237145098, 0, 0] := by
  rw [show D2M8K2.u4534 = KTree.node D2M8K2.t4542 (nat_lit 10209751) (nat_lit 1162407044) (nat_lit 0) D2M8K2.t4543 from rfl, totK_node, tot4542, tot4543]
  decide +kernel

theorem arows4540 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4540 = true := by
  rw [show D2M8K2.u4540 = KTree.node D2M8K2.t4544 (nat_lit 10211911) (nat_lit 2157282000) (nat_lit 0) D2M8K2.t4545 from rfl, allE_node, rows4544, irow4540, rows4545]
  all_goals rfl

theorem atot4540 : totK PD2M8K2 D2M8K2.u4540 = [0, 0, 131635274643, 740593162697, 802194166202, 111838081290, 1164319620, 0] := by
  rw [show D2M8K2.u4540 = KTree.node D2M8K2.t4544 (nat_lit 10211911) (nat_lit 2157282000) (nat_lit 0) D2M8K2.t4545 from rfl, totK_node, tot4544, tot4545]
  decide +kernel

theorem arows4541 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4541 = true := by
  rw [show D2M8K2.u4541 = KTree.node D2M8K2.t4546 (nat_lit 10216975) (nat_lit 2317225996) (nat_lit 0) D2M8K2.t4547 from rfl, allE_node, rows4546, irow4541, rows4547]
  all_goals rfl

theorem atot4541 : totK PD2M8K2 D2M8K2.u4541 = [0, 0, 264976971630, 820808655302, 596023980747, 74823900700, 1096505104, 0] := by
  rw [show D2M8K2.u4541 = KTree.node D2M8K2.t4546 (nat_lit 10216975) (nat_lit 2317225996) (nat_lit 0) D2M8K2.t4547 from rfl, totK_node, tot4546, tot4547]
  decide +kernel

theorem arows4543 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4543 = true := by
  rw [show D2M8K2.u4543 = KTree.node D2M8K2.t4548 (nat_lit 10219475) (nat_lit 2871778485) (nat_lit 0) D2M8K2.t4549 from rfl, allE_node, rows4548, irow4543, rows4549]
  all_goals rfl

theorem atot4543 : totK PD2M8K2 D2M8K2.u4543 = [0, 0, 241962105330, 843877269830, 671444988502, 54606212490, 0, 0] := by
  rw [show D2M8K2.u4543 = KTree.node D2M8K2.t4548 (nat_lit 10219475) (nat_lit 2871778485) (nat_lit 0) D2M8K2.t4549 from rfl, totK_node, tot4548, tot4549]
  decide +kernel

theorem arows4544 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4544 = true := by
  rw [show D2M8K2.u4544 = KTree.node D2M8K2.t4550 (nat_lit 10247400) (nat_lit 2633369454) (nat_lit 0) D2M8K2.t4551 from rfl, allE_node, rows4550, irow4544, rows4551]
  all_goals rfl

theorem atot4544 : totK PD2M8K2 D2M8K2.u4544 = [0, 0, 372994836952, 908580043026, 523664230227, 48188048521, 0, 0] := by
  rw [show D2M8K2.u4544 = KTree.node D2M8K2.t4550 (nat_lit 10247400) (nat_lit 2633369454) (nat_lit 0) D2M8K2.t4551 from rfl, totK_node, tot4550, tot4551]
  decide +kernel

theorem arows4547 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4547 = true := by
  rw [show D2M8K2.u4547 = KTree.node D2M8K2.t4552 (nat_lit 10248558) (nat_lit 4025775211) (nat_lit 0) D2M8K2.t4553 from rfl, allE_node, rows4552, irow4547, rows4553]
  all_goals rfl

theorem atot4547 : totK PD2M8K2 D2M8K2.u4547 = [0, 0, 231372099065, 753709795625, 631810047294, 197249559994, 21400436502, 0] := by
  rw [show D2M8K2.u4547 = KTree.node D2M8K2.t4552 (nat_lit 10248558) (nat_lit 4025775211) (nat_lit 0) D2M8K2.t4553 from rfl, totK_node, tot4552, tot4553]
  decide +kernel

theorem arows4548 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4548 = true := by
  rw [show D2M8K2.u4548 = KTree.node D2M8K2.t4554 (nat_lit 10250014) (nat_lit 2989343405) (nat_lit 0) D2M8K2.t4555 from rfl, allE_node, rows4554, irow4548, rows4555]
  all_goals rfl

theorem atot4548 : totK PD2M8K2 D2M8K2.u4548 = [0, 0, 69708644312, 457782739546, 869671542871, 375761628081, 16099170968, 0] := by
  rw [show D2M8K2.u4548 = KTree.node D2M8K2.t4554 (nat_lit 10250014) (nat_lit 2989343405) (nat_lit 0) D2M8K2.t4555 from rfl, totK_node, tot4554, tot4555]
  decide +kernel

theorem arows4550 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4550 = true := by
  rw [show D2M8K2.u4550 = KTree.node D2M8K2.t4556 (nat_lit 10251284) (nat_lit 3165313827) (nat_lit 0) D2M8K2.t4557 from rfl, allE_node, rows4556, irow4550, rows4557]
  all_goals rfl

theorem atot4550 : totK PD2M8K2 D2M8K2.u4550 = [0, 0, 355723900741, 922761788626, 510276053666, 40052537762, 0, 0] := by
  rw [show D2M8K2.u4550 = KTree.node D2M8K2.t4556 (nat_lit 10251284) (nat_lit 3165313827) (nat_lit 0) D2M8K2.t4557 from rfl, totK_node, tot4556, tot4557]
  decide +kernel

theorem arows4551 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4551 = true := by
  rw [show D2M8K2.u4551 = KTree.node D2M8K2.t4558 (nat_lit 10253065) (nat_lit 1294604065) (nat_lit 0) D2M8K2.t4559 from rfl, allE_node, rows4558, irow4551, rows4559]
  all_goals rfl

theorem atot4551 : totK PD2M8K2 D2M8K2.u4551 = [0, 0, 90400450959, 590683072339, 882971426877, 244521011553, 9087311183, 0] := by
  rw [show D2M8K2.u4551 = KTree.node D2M8K2.t4558 (nat_lit 10253065) (nat_lit 1294604065) (nat_lit 0) D2M8K2.t4559 from rfl, totK_node, tot4558, tot4559]
  decide +kernel

theorem arows4555 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4555 = true := by
  rw [show D2M8K2.u4555 = KTree.node D2M8K2.t4560 (nat_lit 10255275) (nat_lit 3717283055) (nat_lit 0) D2M8K2.t4561 from rfl, allE_node, rows4560, irow4555, rows4561]
  all_goals rfl

theorem atot4555 : totK PD2M8K2 D2M8K2.u4555 = [0, 0, 255584141350, 869643591935, 656908935281, 77189105486, 0, 0] := by
  rw [show D2M8K2.u4555 = KTree.node D2M8K2.t4560 (nat_lit 10255275) (nat_lit 3717283055) (nat_lit 0) D2M8K2.t4561 from rfl, totK_node, tot4560, tot4561]
  decide +kernel

theorem arows4556 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4556 = true := by
  rw [show D2M8K2.u4556 = KTree.node D2M8K2.t4562 (nat_lit 10257421) (nat_lit 1328988789) (nat_lit 0) D2M8K2.t4563 from rfl, allE_node, rows4562, irow4556, rows4563]
  all_goals rfl

theorem atot4556 : totK PD2M8K2 D2M8K2.u4556 = [0, 0, 219111436540, 691463089999, 711065398735, 178542256425, 5439011083, 0] := by
  rw [show D2M8K2.u4556 = KTree.node D2M8K2.t4562 (nat_lit 10257421) (nat_lit 1328988789) (nat_lit 0) D2M8K2.t4563 from rfl, totK_node, tot4562, tot4563]
  decide +kernel

theorem arows4558 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4558 = true := by
  rw [show D2M8K2.u4558 = KTree.node D2M8K2.t4564 (nat_lit 10258708) (nat_lit 3500395180) (nat_lit 0) D2M8K2.t4565 from rfl, allE_node, rows4564, irow4558, rows4565]
  all_goals rfl

theorem atot4558 : totK PD2M8K2 D2M8K2.u4558 = [0, 0, 188540108795, 837059365533, 712421625612, 75570677181, 0, 0] := by
  rw [show D2M8K2.u4558 = KTree.node D2M8K2.t4564 (nat_lit 10258708) (nat_lit 3500395180) (nat_lit 0) D2M8K2.t4565 from rfl, totK_node, tot4564, tot4565]
  decide +kernel

theorem arows4559 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4559 = true := by
  rw [show D2M8K2.u4559 = KTree.node D2M8K2.t4566 (nat_lit 10261210) (nat_lit 3955513244) (nat_lit 0) D2M8K2.t4567 from rfl, allE_node, rows4566, irow4559, rows4567]
  all_goals rfl

theorem atot4559 : totK PD2M8K2 D2M8K2.u4559 = [0, 0, 274768322098, 792296505922, 636008959202, 125909457499, 2585032425, 0] := by
  rw [show D2M8K2.u4559 = KTree.node D2M8K2.t4566 (nat_lit 10261210) (nat_lit 3955513244) (nat_lit 0) D2M8K2.t4567 from rfl, totK_node, tot4566, tot4567]
  decide +kernel

theorem arows4562 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4562 = true := by
  rw [show D2M8K2.u4562 = KTree.node D2M8K2.t4568 (nat_lit 10262675) (nat_lit 2484861107) (nat_lit 0) D2M8K2.t4569 from rfl, allE_node, rows4568, irow4562, rows4569]
  all_goals rfl

theorem atot4562 : totK PD2M8K2 D2M8K2.u4562 = [0, 0, 141117616596, 682237610761, 807547086846, 179456272725, 2436510558, 0] := by
  rw [show D2M8K2.u4562 = KTree.node D2M8K2.t4568 (nat_lit 10262675) (nat_lit 2484861107) (nat_lit 0) D2M8K2.t4569 from rfl, totK_node, tot4568, tot4569]
  decide +kernel

theorem arows4563 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4563 = true := by
  rw [show D2M8K2.u4563 = KTree.node D2M8K2.t4570 (nat_lit 10285166) (nat_lit 2803986341) (nat_lit 0) D2M8K2.t4571 from rfl, allE_node, rows4570, irow4563, rows4571]
  all_goals rfl

theorem atot4563 : totK PD2M8K2 D2M8K2.u4563 = [0, 0, 237976468399, 701769180034, 622399260471, 191502324191, 11198162423, 0] := by
  rw [show D2M8K2.u4563 = KTree.node D2M8K2.t4570 (nat_lit 10285166) (nat_lit 2803986341) (nat_lit 0) D2M8K2.t4571 from rfl, totK_node, tot4570, tot4571]
  decide +kernel

theorem arows4565 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4565 = true := by
  rw [show D2M8K2.u4565 = KTree.node D2M8K2.t4572 (nat_lit 10286844) (nat_lit 3235948554) (nat_lit 0) D2M8K2.t4573 from rfl, allE_node, rows4572, irow4565, rows4573]
  all_goals rfl

theorem atot4565 : totK PD2M8K2 D2M8K2.u4565 = [0, 0, 156228438438, 735261152919, 751674369978, 110947131362, 1334361349, 0] := by
  rw [show D2M8K2.u4565 = KTree.node D2M8K2.t4572 (nat_lit 10286844) (nat_lit 3235948554) (nat_lit 0) D2M8K2.t4573 from rfl, totK_node, tot4572, tot4573]
  decide +kernel

theorem arows4566 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4566 = true := by
  rw [show D2M8K2.u4566 = KTree.node D2M8K2.t4574 (nat_lit 10289204) (nat_lit 3657104338) (nat_lit 0) D2M8K2.t4575 from rfl, allE_node, rows4574, irow4566, rows4575]
  all_goals rfl

theorem atot4566 : totK PD2M8K2 D2M8K2.u4566 = [0, 0, 338421404813, 897001287944, 558751339961, 50992724890, 0, 0] := by
  rw [show D2M8K2.u4566 = KTree.node D2M8K2.t4574 (nat_lit 10289204) (nat_lit 3657104338) (nat_lit 0) D2M8K2.t4575 from rfl, totK_node, tot4574, tot4575]
  decide +kernel

theorem arows4571 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4571 = true := by
  rw [show D2M8K2.u4571 = KTree.node D2M8K2.t4576 (nat_lit 10290740) (nat_lit 3068439174) (nat_lit 0) D2M8K2.t4577 from rfl, allE_node, rows4576, irow4571, rows4577]
  all_goals rfl

theorem atot4571 : totK PD2M8K2 D2M8K2.u4571 = [0, 0, 87893730914, 586678985664, 835384882094, 293116259986, 18567029682, 0] := by
  rw [show D2M8K2.u4571 = KTree.node D2M8K2.t4576 (nat_lit 10290740) (nat_lit 3068439174) (nat_lit 0) D2M8K2.t4577 from rfl, totK_node, tot4576, tot4577]
  decide +kernel

theorem arows4572 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4572 = true := by
  rw [show D2M8K2.u4572 = KTree.node D2M8K2.t4578 (nat_lit 10292161) (nat_lit 1501484711) (nat_lit 0) D2M8K2.t4579 from rfl, allE_node, rows4578, irow4572, rows4579]
  all_goals rfl

theorem atot4572 : totK PD2M8K2 D2M8K2.u4572 = [0, 0, 268639504540, 731288746077, 642417653067, 177622034441, 5521894595, 0] := by
  rw [show D2M8K2.u4572 = KTree.node D2M8K2.t4578 (nat_lit 10292161) (nat_lit 1501484711) (nat_lit 0) D2M8K2.t4579 from rfl, totK_node, tot4578, tot4579]
  decide +kernel

theorem arows4574 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4574 = true := by
  rw [show D2M8K2.u4574 = KTree.node D2M8K2.t4580 (nat_lit 10293614) (nat_lit 2609186742) (nat_lit 0) D2M8K2.t4581 from rfl, allE_node, rows4580, irow4574, rows4581]
  all_goals rfl

theorem atot4574 : totK PD2M8K2 D2M8K2.u4574 = [0, 0, 176333444930, 760919351127, 752882411883, 123564364055, 1164319620, 0] := by
  rw [show D2M8K2.u4574 = KTree.node D2M8K2.t4580 (nat_lit 10293614) (nat_lit 2609186742) (nat_lit 0) D2M8K2.t4581 from rfl, totK_node, tot4580, tot4581]
  decide +kernel

theorem arows4575 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4575 = true := by
  rw [show D2M8K2.u4575 = KTree.node D2M8K2.t4582 (nat_lit 10298887) (nat_lit 2322689491) (nat_lit 0) D2M8K2.t4583 from rfl, allE_node, rows4582, irow4575, rows4583]
  all_goals rfl

theorem atot4575 : totK PD2M8K2 D2M8K2.u4575 = [0, 0, 185954085693, 650772885190, 708166080336, 212791373184, 11885407614, 0] := by
  rw [show D2M8K2.u4575 = KTree.node D2M8K2.t4582 (nat_lit 10298887) (nat_lit 2322689491) (nat_lit 0) D2M8K2.t4583 from rfl, totK_node, tot4582, tot4583]
  decide +kernel

theorem arows4578 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4578 = true := by
  rw [show D2M8K2.u4578 = KTree.node D2M8K2.t4584 (nat_lit 10300123) (nat_lit 2175796031) (nat_lit 0) D2M8K2.t4585 from rfl, allE_node, rows4584, irow4578, rows4585]
  all_goals rfl

theorem atot4578 : totK PD2M8K2 D2M8K2.u4578 = [0, 0, 223334781399, 798468752446, 661176426382, 87100824752, 1062926506, 0] := by
  rw [show D2M8K2.u4578 = KTree.node D2M8K2.t4584 (nat_lit 10300123) (nat_lit 2175796031) (nat_lit 0) D2M8K2.t4585 from rfl, totK_node, tot4584, tot4585]
  decide +kernel

theorem arows4579 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4579 = true := by
  rw [show D2M8K2.u4579 = KTree.node D2M8K2.t4586 (nat_lit 10302444) (nat_lit 3180597961) (nat_lit 0) D2M8K2.t4587 from rfl, allE_node, rows4586, irow4579, rows4587]
  all_goals rfl

theorem atot4579 : totK PD2M8K2 D2M8K2.u4579 = [0, 0, 248642910044, 756185197385, 668318979598, 126431394172, 3783381897, 0] := by
  rw [show D2M8K2.u4579 = KTree.node D2M8K2.t4586 (nat_lit 10302444) (nat_lit 3180597961) (nat_lit 0) D2M8K2.t4587 from rfl, totK_node, tot4586, tot4587]
  decide +kernel

theorem arows4581 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4581 = true := by
  rw [show D2M8K2.u4581 = KTree.node D2M8K2.t4588 (nat_lit 10303981) (nat_lit 1053231265) (nat_lit 0) D2M8K2.t4589 from rfl, allE_node, rows4588, irow4581, rows4589]
  all_goals rfl

theorem atot4581 : totK PD2M8K2 D2M8K2.u4581 = [0, 0, 166094524244, 757567472468, 754254726611, 124842964702, 1240621948, 0] := by
  rw [show D2M8K2.u4581 = KTree.node D2M8K2.t4588 (nat_lit 10303981) (nat_lit 1053231265) (nat_lit 0) D2M8K2.t4589 from rfl, totK_node, tot4588, tot4589]
  decide +kernel

theorem arows4582 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4582 = true := by
  rw [show D2M8K2.u4582 = KTree.node D2M8K2.t4590 (nat_lit 10305814) (nat_lit 3547600099) (nat_lit 0) D2M8K2.t4591 from rfl, allE_node, rows4590, irow4582, rows4591]
  all_goals rfl

theorem atot4582 : totK PD2M8K2 D2M8K2.u4582 = [0, 0, 0, 403963381893, 951125823548, 386902411773, 17197636586, 0] := by
  rw [show D2M8K2.u4582 = KTree.node D2M8K2.t4590 (nat_lit 10305814) (nat_lit 3547600099) (nat_lit 0) D2M8K2.t4591 from rfl, totK_node, tot4590, tot4591]
  decide +kernel

theorem arows4586 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4586 = true := by
  rw [show D2M8K2.u4586 = KTree.node D2M8K2.t4592 (nat_lit 10309626) (nat_lit 3506389050) (nat_lit 0) D2M8K2.t4593 from rfl, allE_node, rows4592, irow4586, rows4593]
  all_goals rfl

theorem atot4586 : totK PD2M8K2 D2M8K2.u4586 = [0, 0, 0, 406884402222, 946010493735, 403258210007, 23369679016, 0] := by
  rw [show D2M8K2.u4586 = KTree.node D2M8K2.t4592 (nat_lit 10309626) (nat_lit 3506389050) (nat_lit 0) D2M8K2.t4593 from rfl, totK_node, tot4592, tot4593]
  decide +kernel

theorem arows4587 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4587 = true := by
  rw [show D2M8K2.u4587 = KTree.node D2M8K2.t4594 (nat_lit 10312777) (nat_lit 1492800891) (nat_lit 0) D2M8K2.t4595 from rfl, allE_node, rows4594, irow4587, rows4595]
  all_goals rfl

theorem atot4587 : totK PD2M8K2 D2M8K2.u4587 = [0, 0, 0, 406975959402, 965261432833, 400559372190, 24887012618, 0] := by
  rw [show D2M8K2.u4587 = KTree.node D2M8K2.t4594 (nat_lit 10312777) (nat_lit 1492800891) (nat_lit 0) D2M8K2.t4595 from rfl, totK_node, tot4594, tot4595]
  decide +kernel

theorem arows4589 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4589 = true := by
  rw [show D2M8K2.u4589 = KTree.node D2M8K2.t4596 (nat_lit 10314271) (nat_lit 2070511445) (nat_lit 0) D2M8K2.t4597 from rfl, allE_node, rows4596, irow4589, rows4597]
  all_goals rfl

theorem atot4589 : totK PD2M8K2 D2M8K2.u4589 = [0, 0, 0, 198818565747, 839091921299, 672905162662, 70929265418, 0] := by
  rw [show D2M8K2.u4589 = KTree.node D2M8K2.t4596 (nat_lit 10314271) (nat_lit 2070511445) (nat_lit 0) D2M8K2.t4597 from rfl, totK_node, tot4596, tot4597]
  decide +kernel

theorem arows4590 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4590 = true := by
  rw [show D2M8K2.u4590 = KTree.node D2M8K2.t4598 (nat_lit 10319718) (nat_lit 3631644964) (nat_lit 0) D2M8K2.t4599 from rfl, allE_node, rows4598, irow4590, rows4599]
  all_goals rfl

theorem atot4590 : totK PD2M8K2 D2M8K2.u4590 = [0, 0, 0, 253747210890, 734815206818, 592437703642, 152210771456, 5717851365] := by
  rw [show D2M8K2.u4590 = KTree.node D2M8K2.t4598 (nat_lit 10319718) (nat_lit 3631644964) (nat_lit 0) D2M8K2.t4599 from rfl, totK_node, tot4598, tot4599]
  decide +kernel

theorem arows4593 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4593 = true := by
  rw [show D2M8K2.u4593 = KTree.node D2M8K2.t4600 (nat_lit 10321356) (nat_lit 3512523767) (nat_lit 0) D2M8K2.t4601 from rfl, allE_node, rows4600, irow4593, rows4601]
  all_goals rfl

theorem atot4593 : totK PD2M8K2 D2M8K2.u4593 = [0, 0, 0, 153465825276, 835868625445, 660138165274, 63081321898, 0] := by
  rw [show D2M8K2.u4593 = KTree.node D2M8K2.t4600 (nat_lit 10321356) (nat_lit 3512523767) (nat_lit 0) D2M8K2.t4601 from rfl, totK_node, tot4600, tot4601]
  decide +kernel

theorem arows4594 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4594 = true := by
  rw [show D2M8K2.u4594 = KTree.node D2M8K2.t4602 (nat_lit 10323635) (nat_lit 2885562416) (nat_lit 0) D2M8K2.t4603 from rfl, allE_node, rows4602, irow4594, rows4603]
  all_goals rfl

theorem atot4594 : totK PD2M8K2 D2M8K2.u4594 = [0, 0, 0, 412181127050, 882121827328, 415323599844, 59405670996, 1330264907] := by
  rw [show D2M8K2.u4594 = KTree.node D2M8K2.t4602 (nat_lit 10323635) (nat_lit 2885562416) (nat_lit 0) D2M8K2.t4603 from rfl, totK_node, tot4602, tot4603]
  decide +kernel

theorem arows4596 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4596 = true := by
  rw [show D2M8K2.u4596 = KTree.node D2M8K2.t4604 (nat_lit 10368785) (nat_lit 2211143222) (nat_lit 0) D2M8K2.t4605 from rfl, allE_node, rows4604, irow4596, rows4605]
  all_goals rfl

theorem atot4596 : totK PD2M8K2 D2M8K2.u4596 = [0, 0, 357147610085, 858457184087, 449838119796, 92450594615, 7702325016, 0] := by
  rw [show D2M8K2.u4596 = KTree.node D2M8K2.t4604 (nat_lit 10368785) (nat_lit 2211143222) (nat_lit 0) D2M8K2.t4605 from rfl, totK_node, tot4604, tot4605]
  decide +kernel

theorem arows4597 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4597 = true := by
  rw [show D2M8K2.u4597 = KTree.node D2M8K2.t4606 (nat_lit 10370692) (nat_lit 2508863889) (nat_lit 0) D2M8K2.t4607 from rfl, allE_node, rows4606, irow4597, rows4607]
  all_goals rfl

theorem atot4597 : totK PD2M8K2 D2M8K2.u4597 = [0, 0, 121263117707, 686040221708, 849191972672, 127324053284, 1310166938, 0] := by
  rw [show D2M8K2.u4597 = KTree.node D2M8K2.t4606 (nat_lit 10370692) (nat_lit 2508863889) (nat_lit 0) D2M8K2.t4607 from rfl, totK_node, tot4606, tot4607]
  decide +kernel

theorem arows4606 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4606 = true := by
  rw [show D2M8K2.u4606 = KTree.node D2M8K2.t4608 (nat_lit 10372658) (nat_lit 4046883989) (nat_lit 0) D2M8K2.t4609 from rfl, allE_node, rows4608, irow4606, rows4609]
  all_goals rfl

theorem atot4606 : totK PD2M8K2 D2M8K2.u4606 = [0, 0, 315449516733, 926523920331, 548855156986, 49990653779, 0, 0] := by
  rw [show D2M8K2.u4606 = KTree.node D2M8K2.t4608 (nat_lit 10372658) (nat_lit 4046883989) (nat_lit 0) D2M8K2.t4609 from rfl, totK_node, tot4608, tot4609]
  decide +kernel

theorem arows4607 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4607 = true := by
  rw [show D2M8K2.u4607 = KTree.node D2M8K2.t4610 (nat_lit 10374370) (nat_lit 3447495898) (nat_lit 0) D2M8K2.t4611 from rfl, allE_node, rows4610, irow4607, rows4611]
  all_goals rfl

theorem atot4607 : totK PD2M8K2 D2M8K2.u4607 = [0, 0, 81374014488, 527153677113, 853200209821, 322971024062, 15013989272, 0] := by
  rw [show D2M8K2.u4607 = KTree.node D2M8K2.t4610 (nat_lit 10374370) (nat_lit 3447495898) (nat_lit 0) D2M8K2.t4611 from rfl, totK_node, tot4610, tot4611]
  decide +kernel

theorem arows4609 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4609 = true := by
  rw [show D2M8K2.u4609 = KTree.node D2M8K2.t4612 (nat_lit 10375742) (nat_lit 2481229240) (nat_lit 0) D2M8K2.t4613 from rfl, allE_node, rows4612, irow4609, rows4613]
  all_goals rfl

theorem atot4609 : totK PD2M8K2 D2M8K2.u4609 = [0, 0, 340020453999, 911970395934, 535174027436, 44072521451, 0, 0] := by
  rw [show D2M8K2.u4609 = KTree.node D2M8K2.t4612 (nat_lit 10375742) (nat_lit 2481229240) (nat_lit 0) D2M8K2.t4613 from rfl, totK_node, tot4612, tot4613]
  decide +kernel

theorem arows4610 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4610 = true := by
  rw [show D2M8K2.u4610 = KTree.node D2M8K2.t4614 (nat_lit 10377457) (nat_lit 1353320213) (nat_lit 0) D2M8K2.t4615 from rfl, allE_node, rows4614, irow4610, rows4615]
  all_goals rfl

theorem atot4610 : totK PD2M8K2 D2M8K2.u4610 = [0, 0, 65793408479, 508432672686, 882802512056, 281451854436, 13049727234, 0] := by
  rw [show D2M8K2.u4610 = KTree.node D2M8K2.t4614 (nat_lit 10377457) (nat_lit 1353320213) (nat_lit 0) D2M8K2.t4615 from rfl, totK_node, tot4614, tot4615]
  decide +kernel

theorem arows4613 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4613 = true := by
  rw [show D2M8K2.u4613 = KTree.node D2M8K2.t4616 (nat_lit 10379498) (nat_lit 3878590141) (nat_lit 0) D2M8K2.t4617 from rfl, allE_node, rows4616, irow4613, rows4617]
  all_goals rfl

theorem atot4613 : totK PD2M8K2 D2M8K2.u4613 = [0, 0, 260699729429, 888920630916, 631834029911, 52042722404, 0, 0] := by
  rw [show D2M8K2.u4613 = KTree.node D2M8K2.t4616 (nat_lit 10379498) (nat_lit 3878590141) (nat_lit 0) D2M8K2.t4617 from rfl, totK_node, tot4616, tot4617]
  decide +kernel

theorem arows4614 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4614 = true := by
  rw [show D2M8K2.u4614 = KTree.node D2M8K2.t4618 (nat_lit 10382093) (nat_lit 1774689751) (nat_lit 0) D2M8K2.t4619 from rfl, allE_node, rows4618, irow4614, rows4619]
  all_goals rfl

theorem atot4614 : totK PD2M8K2 D2M8K2.u4614 = [0, 0, 259800448663, 788830748481, 647111708077, 108278360002, 1334898114, 0] := by
  rw [show D2M8K2.u4614 = KTree.node D2M8K2.t4618 (nat_lit 10382093) (nat_lit 1774689751) (nat_lit 0) D2M8K2.t4619 from rfl, totK_node, tot4618, tot4619]
  decide +kernel

theorem arows4616 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4616 = true := by
  rw [show D2M8K2.u4616 = KTree.node D2M8K2.t4620 (nat_lit 10383563) (nat_lit 2664677307) (nat_lit 0) D2M8K2.t4621 from rfl, allE_node, rows4620, irow4616, rows4621]
  all_goals rfl

theorem atot4616 : totK PD2M8K2 D2M8K2.u4616 = [0, 0, 175097542693, 753051385582, 751868577268, 114574882296, 1096505104, 0] := by
  rw [show D2M8K2.u4616 = KTree.node D2M8K2.t4620 (nat_lit 10383563) (nat_lit 2664677307) (nat_lit 0) D2M8K2.t4621 from rfl, totK_node, tot4620, tot4621]
  decide +kernel

theorem arows4617 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4617 = true := by
  rw [show D2M8K2.u4617 = KTree.node D2M8K2.t4622 (nat_lit 10388985) (nat_lit 1867336925) (nat_lit 0) D2M8K2.t4623 from rfl, allE_node, rows4622, irow4617, rows4623]
  all_goals rfl

theorem atot4617 : totK PD2M8K2 D2M8K2.u4617 = [0, 0, 0, 452585916205, 964319742294, 323489005119, 9665762631, 0] := by
  rw [show D2M8K2.u4617 = KTree.node D2M8K2.t4622 (nat_lit 10388985) (nat_lit 1867336925) (nat_lit 0) D2M8K2.t4623 from rfl, totK_node, tot4622, tot4623]
  decide +kernel

theorem arows4621 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4621 = true := by
  rw [show D2M8K2.u4621 = KTree.node D2M8K2.t4624 (nat_lit 10392916) (nat_lit 3685694758) (nat_lit 0) D2M8K2.t4625 from rfl, allE_node, rows4624, irow4621, rows4625]
  all_goals rfl

theorem atot4621 : totK PD2M8K2 D2M8K2.u4621 = [0, 0, 0, 465788697184, 955969501255, 372293727537, 17666988014, 0] := by
  rw [show D2M8K2.u4621 = KTree.node D2M8K2.t4624 (nat_lit 10392916) (nat_lit 3685694758) (nat_lit 0) D2M8K2.t4625 from rfl, totK_node, tot4624, tot4625]
  decide +kernel

theorem arows4622 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4622 = true := by
  rw [show D2M8K2.u4622 = KTree.node D2M8K2.t4626 (nat_lit 10396273) (nat_lit 1504877981) (nat_lit 0) D2M8K2.t4627 from rfl, allE_node, rows4626, irow4622, rows4627]
  all_goals rfl

theorem atot4622 : totK PD2M8K2 D2M8K2.u4622 = [0, 0, 0, 395246249454, 937551218964, 404507473942, 23272095769, 0] := by
  rw [show D2M8K2.u4622 = KTree.node D2M8K2.t4626 (nat_lit 10396273) (nat_lit 1504877981) (nat_lit 0) D2M8K2.t4627 from rfl, totK_node, tot4626, tot4627]
  decide +kernel

theorem arows4624 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4624 = true := by
  rw [show D2M8K2.u4624 = KTree.node D2M8K2.t4628 (nat_lit 10400328) (nat_lit 3524105691) (nat_lit 0) D2M8K2.t4629 from rfl, allE_node, rows4628, irow4624, rows4629]
  all_goals rfl

theorem atot4624 : totK PD2M8K2 D2M8K2.u4624 = [0, 0, 0, 505693283636, 978683030594, 282057485326, 9406884954, 0] := by
  rw [show D2M8K2.u4624 = KTree.node D2M8K2.t4628 (nat_lit 10400328) (nat_lit 3524105691) (nat_lit 0) D2M8K2.t4629 from rfl, totK_node, tot4628, tot4629]
  decide +kernel

theorem arows4625 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4625 = true := by
  rw [show D2M8K2.u4625 = KTree.node D2M8K2.t4630 (nat_lit 10403694) (nat_lit 3434857360) (nat_lit 0) D2M8K2.t4631 from rfl, allE_node, rows4630, irow4625, rows4631]
  all_goals rfl

theorem atot4625 : totK PD2M8K2 D2M8K2.u4625 = [0, 0, 0, 256986531230, 896392961279, 549257508493, 42854299016, 0] := by
  rw [show D2M8K2.u4625 = KTree.node D2M8K2.t4630 (nat_lit 10403694) (nat_lit 3434857360) (nat_lit 0) D2M8K2.t4631 from rfl, totK_node, tot4630, tot4631]
  decide +kernel

theorem arows4628 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4628 = true := by
  rw [show D2M8K2.u4628 = KTree.node D2M8K2.t4632 (nat_lit 10409667) (nat_lit 1613251269) (nat_lit 0) D2M8K2.t4633 from rfl, allE_node, rows4632, irow4628, rows4633]
  all_goals rfl

theorem atot4628 : totK PD2M8K2 D2M8K2.u4628 = [0, 0, 323132269989, 661160455474, 409271381277, 314200287422, 66564545234, 1394496256] := by
  rw [show D2M8K2.u4628 = KTree.node D2M8K2.t4632 (nat_lit 10409667) (nat_lit 1613251269) (nat_lit 0) D2M8K2.t4633 from rfl, totK_node, tot4632, tot4633]
  decide +kernel

theorem arows4629 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4629 = true := by
  rw [show D2M8K2.u4629 = KTree.node D2M8K2.t4634 (nat_lit 10411880) (nat_lit 3769075671) (nat_lit 0) D2M8K2.t4635 from rfl, allE_node, rows4634, irow4629, rows4635]
  all_goals rfl

theorem atot4629 : totK PD2M8K2 D2M8K2.u4629 = [0, 0, 147286232898, 715394003071, 820076486975, 125293992802, 1369150432, 0] := by
  rw [show D2M8K2.u4629 = KTree.node D2M8K2.t4634 (nat_lit 10411880) (nat_lit 3769075671) (nat_lit 0) D2M8K2.t4635 from rfl, totK_node, tot4634, tot4635]
  decide +kernel

theorem arows4631 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4631 = true := by
  rw [show D2M8K2.u4631 = KTree.node D2M8K2.t4636 (nat_lit 10413969) (nat_lit 1529425970) (nat_lit 0) D2M8K2.t4637 from rfl, allE_node, rows4636, irow4631, rows4637]
  all_goals rfl

theorem atot4631 : totK PD2M8K2 D2M8K2.u4631 = [0, 0, 327267129077, 918478102647, 556946206961, 44472835290, 0, 0] := by
  rw [show D2M8K2.u4631 = KTree.node D2M8K2.t4636 (nat_lit 10413969) (nat_lit 1529425970) (nat_lit 0) D2M8K2.t4637 from rfl, totK_node, tot4636, tot4637]
  decide +kernel

theorem arows4632 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4632 = true := by
  rw [show D2M8K2.u4632 = KTree.node D2M8K2.t4638 (nat_lit 10415503) (nat_lit 1176831855) (nat_lit 0) D2M8K2.t4639 from rfl, allE_node, rows4638, irow4632, rows4639]
  all_goals rfl

theorem atot4632 : totK PD2M8K2 D2M8K2.u4632 = [0, 0, 0, 410692923681, 957863760965, 413860449514, 25977880579, 0] := by
  rw [show D2M8K2.u4632 = KTree.node D2M8K2.t4638 (nat_lit 10415503) (nat_lit 1176831855) (nat_lit 0) D2M8K2.t4639 from rfl, totK_node, tot4638, tot4639]
  decide +kernel

theorem arows4637 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4637 = true := by
  rw [show D2M8K2.u4637 = KTree.node D2M8K2.t4640 (nat_lit 10416884) (nat_lit 3177744962) (nat_lit 0) D2M8K2.t4641 from rfl, allE_node, rows4640, irow4637, rows4641]
  all_goals rfl

theorem atot4637 : totK PD2M8K2 D2M8K2.u4637 = [0, 0, 332662374380, 837121140735, 502982881924, 120865374333, 6784518318, 0] := by
  rw [show D2M8K2.u4637 = KTree.node D2M8K2.t4640 (nat_lit 10416884) (nat_lit 3177744962) (nat_lit 0) D2M8K2.t4641 from rfl, totK_node, tot4640, tot4641]
  decide +kernel

theorem arows4638 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4638 = true := by
  rw [show D2M8K2.u4638 = KTree.node D2M8K2.t4642 (nat_lit 10418446) (nat_lit 3943772739) (nat_lit 0) D2M8K2.t4643 from rfl, allE_node, rows4642, irow4638, rows4643]
  all_goals rfl

theorem atot4638 : totK PD2M8K2 D2M8K2.u4638 = [0, 0, 89734097483, 604116188064, 874789612066, 221955600741, 8192599454, 0] := by
  rw [show D2M8K2.u4638 = KTree.node D2M8K2.t4642 (nat_lit 10418446) (nat_lit 3943772739) (nat_lit 0) D2M8K2.t4643 from rfl, totK_node, tot4642, tot4643]
  decide +kernel

theorem arows4640 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4640 = true := by
  rw [show D2M8K2.u4640 = KTree.node D2M8K2.t4644 (nat_lit 10420784) (nat_lit 3601322459) (nat_lit 0) D2M8K2.t4645 from rfl, allE_node, rows4644, irow4640, rows4645]
  all_goals rfl

theorem atot4640 : totK PD2M8K2 D2M8K2.u4640 = [0, 0, 329128535078, 902674560062, 575982339859, 59625179468, 0, 0] := by
  rw [show D2M8K2.u4640 = KTree.node D2M8K2.t4644 (nat_lit 10420784) (nat_lit 3601322459) (nat_lit 0) D2M8K2.t4645 from rfl, totK_node, tot4644, tot4645]
  decide +kernel

theorem arows4641 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4641 = true := by
  rw [show D2M8K2.u4641 = KTree.node D2M8K2.t4646 (nat_lit 10426820) (nat_lit 3017009940) (nat_lit 0) D2M8K2.t4647 from rfl, allE_node, rows4646, irow4641, rows4647]
  all_goals rfl

theorem atot4641 : totK PD2M8K2 D2M8K2.u4641 = [0, 0, 228324931850, 752441566436, 717209488314, 139654122419, 1510868091, 0] := by
  rw [show D2M8K2.u4641 = KTree.node D2M8K2.t4646 (nat_lit 10426820) (nat_lit 3017009940) (nat_lit 0) D2M8K2.t4647 from rfl, totK_node, tot4646, tot4647]
  decide +kernel

theorem arows4644 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4644 = true := by
  rw [show D2M8K2.u4644 = KTree.node D2M8K2.t4648 (nat_lit 10428313) (nat_lit 1513790033) (nat_lit 0) D2M8K2.t4649 from rfl, allE_node, rows4648, irow4644, rows4649]
  all_goals rfl

theorem atot4644 : totK PD2M8K2 D2M8K2.u4644 = [0, 0, 209265602686, 787403342100, 702229870709, 117089085927, 1268739303, 0] := by
  rw [show D2M8K2.u4644 = KTree.node D2M8K2.t4648 (nat_lit 10428313) (nat_lit 1513790033) (nat_lit 0) D2M8K2.t4649 from rfl, totK_node, tot4648, tot4649]
  decide +kernel

theorem arows4645 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4645 = true := by
  rw [show D2M8K2.u4645 = KTree.node D2M8K2.t4650 (nat_lit 10429995) (nat_lit 3609179799) (nat_lit 0) D2M8K2.t4651 from rfl, allE_node, rows4650, irow4645, rows4651]
  all_goals rfl

theorem atot4645 : totK PD2M8K2 D2M8K2.u4645 = [0, 162906912950, 334787191007, 346305791978, 644743303767, 285021685269, 16939140301, 0] := by
  rw [show D2M8K2.u4645 = KTree.node D2M8K2.t4650 (nat_lit 10429995) (nat_lit 3609179799) (nat_lit 0) D2M8K2.t4651 from rfl, totK_node, tot4650, tot4651]
  decide +kernel

theorem arows4647 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4647 = true := by
  rw [show D2M8K2.u4647 = KTree.node D2M8K2.t4652 (nat_lit 10452267) (nat_lit 2856950078) (nat_lit 0) D2M8K2.t4653 from rfl, allE_node, rows4652, irow4647, rows4653]
  all_goals rfl

theorem atot4647 : totK PD2M8K2 D2M8K2.u4647 = [0, 258920160305, 826637540108, 606521977267, 87477307467, 1369150432, 0, 0] := by
  rw [show D2M8K2.u4647 = KTree.node D2M8K2.t4652 (nat_lit 10452267) (nat_lit 2856950078) (nat_lit 0) D2M8K2.t4653 from rfl, totK_node, tot4652, tot4653]
  decide +kernel

theorem arows4648 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4648 = true := by
  rw [show D2M8K2.u4648 = KTree.node D2M8K2.t4654 (nat_lit 10454202) (nat_lit 3833466974) (nat_lit 0) D2M8K2.t4655 from rfl, allE_node, rows4654, irow4648, rows4655]
  all_goals rfl

theorem atot4648 : totK PD2M8K2 D2M8K2.u4648 = [0, 178109623265, 758505365401, 776285992744, 105513919606, 0, 0, 0] := by
  rw [show D2M8K2.u4648 = KTree.node D2M8K2.t4654 (nat_lit 10454202) (nat_lit 3833466974) (nat_lit 0) D2M8K2.t4655 from rfl, totK_node, tot4654, tot4655]
  decide +kernel

theorem arows4652 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4652 = true := by
  rw [show D2M8K2.u4652 = KTree.node D2M8K2.t4656 (nat_lit 10462792) (nat_lit 2938759701) (nat_lit 0) D2M8K2.t4657 from rfl, allE_node, rows4656, irow4652, rows4657]
  all_goals rfl

theorem atot4652 : totK PD2M8K2 D2M8K2.u4652 = [0, 246562022843, 797053266477, 656284909072, 102675472891, 1198073392, 0, 0] := by
  rw [show D2M8K2.u4652 = KTree.node D2M8K2.t4656 (nat_lit 10462792) (nat_lit 2938759701) (nat_lit 0) D2M8K2.t4657 from rfl, totK_node, tot4656, tot4657]
  decide +kernel

theorem arows4653 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4653 = true := by
  rw [show D2M8K2.u4653 = KTree.node D2M8K2.t4658 (nat_lit 10464486) (nat_lit 3792361165) (nat_lit 0) D2M8K2.t4659 from rfl, allE_node, rows4658, irow4653, rows4659]
  all_goals rfl

theorem atot4653 : totK PD2M8K2 D2M8K2.u4653 = [0, 153671077068, 634511334296, 752695740667, 227747449672, 12052611869, 0, 0] := by
  rw [show D2M8K2.u4653 = KTree.node D2M8K2.t4658 (nat_lit 10464486) (nat_lit 3792361165) (nat_lit 0) D2M8K2.t4659 from rfl, totK_node, tot4658, tot4659]
  decide +kernel

theorem arows4655 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4655 = true := by
  rw [show D2M8K2.u4655 = KTree.node D2M8K2.t4660 (nat_lit 10465930) (nat_lit 2879695581) (nat_lit 0) D2M8K2.t4661 from rfl, allE_node, rows4660, irow4655, rows4661]
  all_goals rfl

theorem atot4655 : totK PD2M8K2 D2M8K2.u4655 = [0, 244269272035, 791475713918, 650291433927, 93456228821, 1096505104, 0, 0] := by
  rw [show D2M8K2.u4655 = KTree.node D2M8K2.t4660 (nat_lit 10465930) (nat_lit 2879695581) (nat_lit 0) D2M8K2.t4661 from rfl, totK_node, tot4660, tot4661]
  decide +kernel

theorem arows4656 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4656 = true := by
  rw [show D2M8K2.u4656 = KTree.node D2M8K2.t4662 (nat_lit 10468242) (nat_lit 3395057874) (nat_lit 0) D2M8K2.t4663 from rfl, allE_node, rows4662, irow4656, rows4663]
  all_goals rfl

theorem atot4656 : totK PD2M8K2 D2M8K2.u4656 = [0, 220228871761, 746237675587, 709491965709, 132423839711, 3884009855, 0, 0] := by
  rw [show D2M8K2.u4656 = KTree.node D2M8K2.t4662 (nat_lit 10468242) (nat_lit 3395057874) (nat_lit 0) D2M8K2.t4663 from rfl, totK_node, tot4662, tot4663]
  decide +kernel

theorem arows4659 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4659 = true := by
  rw [show D2M8K2.u4659 = KTree.node D2M8K2.t4664 (nat_lit 10469828) (nat_lit 2038720100) (nat_lit 0) D2M8K2.t4665 from rfl, allE_node, rows4664, irow4659, rows4665]
  all_goals rfl

theorem atot4659 : totK PD2M8K2 D2M8K2.u4659 = [0, 179036101606, 759974895463, 745625360000, 124736542169, 1268739303, 0, 0] := by
  rw [show D2M8K2.u4659 = KTree.node D2M8K2.t4664 (nat_lit 10469828) (nat_lit 2038720100) (nat_lit 0) D2M8K2.t4665 from rfl, totK_node, tot4664, tot4665]
  decide +kernel

theorem arows4660 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4660 = true := by
  rw [show D2M8K2.u4660 = KTree.node D2M8K2.t4666 (nat_lit 10471688) (nat_lit 3626183552) (nat_lit 0) D2M8K2.t4667 from rfl, allE_node, rows4666, irow4660, rows4667]
  all_goals rfl

theorem atot4660 : totK PD2M8K2 D2M8K2.u4660 = [0, 0, 420463941099, 985858799489, 364960390337, 15269460597, 0, 0] := by
  rw [show D2M8K2.u4660 = KTree.node D2M8K2.t4666 (nat_lit 10471688) (nat_lit 3626183552) (nat_lit 0) D2M8K2.t4667 from rfl, totK_node, tot4666, tot4667]
  decide +kernel

theorem arows4662 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4662 = true := by
  rw [show D2M8K2.u4662 = KTree.node D2M8K2.t4668 (nat_lit 10473269) (nat_lit 1819297825) (nat_lit 0) D2M8K2.t4669 from rfl, allE_node, rows4668, irow4662, rows4669]
  all_goals rfl

theorem atot4662 : totK PD2M8K2 D2M8K2.u4662 = [0, 0, 185179805431, 776013668434, 670648635000, 95366786883, 1369150432, 0] := by
  rw [show D2M8K2.u4662 = KTree.node D2M8K2.t4668 (nat_lit 10473269) (nat_lit 1819297825) (nat_lit 0) D2M8K2.t4669 from rfl, totK_node, tot4668, tot4669]
  decide +kernel

theorem arows4663 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4663 = true := by
  rw [show D2M8K2.u4663 = KTree.node D2M8K2.t4670 (nat_lit 10482416) (nat_lit 3699889077) (nat_lit 0) D2M8K2.t4671 from rfl, allE_node, rows4670, irow4663, rows4671]
  all_goals rfl

theorem atot4663 : totK PD2M8K2 D2M8K2.u4663 = [0, 0, 318215172441, 898384662048, 525425278106, 38339883738, 0, 0] := by
  rw [show D2M8K2.u4663 = KTree.node D2M8K2.t4670 (nat_lit 10482416) (nat_lit 3699889077) (nat_lit 0) D2M8K2.t4671 from rfl, totK_node, tot4670, tot4671]
  decide +kernel

theorem arows4669 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4669 = true := by
  rw [show D2M8K2.u4669 = KTree.node D2M8K2.t4672 (nat_lit 10485640) (nat_lit 2770311606) (nat_lit 0) D2M8K2.t4673 from rfl, allE_node, rows4672, irow4669, rows4673]
  all_goals rfl

theorem atot4669 : totK PD2M8K2 D2M8K2.u4669 = [0, 0, 364336823157, 965005023955, 420050483597, 18971542118, 0, 0] := by
  rw [show D2M8K2.u4669 = KTree.node D2M8K2.t4672 (nat_lit 10485640) (nat_lit 2770311606) (nat_lit 0) D2M8K2.t4673 from rfl, totK_node, tot4672, tot4673]
  decide +kernel

theorem arows4670 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4670 = true := by
  rw [show D2M8K2.u4670 = KTree.node D2M8K2.t4674 (nat_lit 10489056) (nat_lit 3603567410) (nat_lit 0) D2M8K2.t4675 from rfl, allE_node, rows4674, irow4670, rows4675]
  all_goals rfl

theorem atot4670 : totK PD2M8K2 D2M8K2.u4670 = [0, 0, 362400076691, 947380389670, 448995151201, 24683687388, 0, 0] := by
  rw [show D2M8K2.u4670 = KTree.node D2M8K2.t4674 (nat_lit 10489056) (nat_lit 3603567410) (nat_lit 0) D2M8K2.t4675 from rfl, totK_node, tot4674, tot4675]
  decide +kernel

theorem arows4672 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4672 = true := by
  rw [show D2M8K2.u4672 = KTree.node D2M8K2.t4676 (nat_lit 10490677) (nat_lit 1310860937) (nat_lit 0) D2M8K2.t4677 from rfl, allE_node, rows4676, irow4672, rows4677]
  all_goals rfl

theorem atot4672 : totK PD2M8K2 D2M8K2.u4672 = [0, 179528440046, 623197327139, 740085284784, 283783788379, 17433533548, 0, 0] := by
  rw [show D2M8K2.u4672 = KTree.node D2M8K2.t4676 (nat_lit 10490677) (nat_lit 1310860937) (nat_lit 0) D2M8K2.t4677 from rfl, totK_node, tot4676, tot4677]
  decide +kernel

theorem arows4673 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4673 = true := by
  rw [show D2M8K2.u4673 = KTree.node D2M8K2.t4678 (nat_lit 10497322) (nat_lit 3989042961) (nat_lit 0) D2M8K2.t4679 from rfl, allE_node, rows4678, irow4673, rows4679]
  all_goals rfl

theorem atot4673 : totK PD2M8K2 D2M8K2.u4673 = [0, 265578002599, 793544466713, 597249451224, 164640855136, 17186218589, 0, 0] := by
  rw [show D2M8K2.u4673 = KTree.node D2M8K2.t4678 (nat_lit 10497322) (nat_lit 3989042961) (nat_lit 0) D2M8K2.t4679 from rfl, totK_node, tot4678, tot4679]
  decide +kernel

theorem arows4676 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4676 = true := by
  rw [show D2M8K2.u4676 = KTree.node D2M8K2.t4680 (nat_lit 10498783) (nat_lit 2311445374) (nat_lit 0) D2M8K2.t4681 from rfl, allE_node, rows4680, irow4676, rows4681]
  all_goals rfl

theorem atot4676 : totK PD2M8K2 D2M8K2.u4676 = [0, 54009388675, 421837135180, 912407309493, 419636087399, 20423179516, 0, 0] := by
  rw [show D2M8K2.u4676 = KTree.node D2M8K2.t4680 (nat_lit 10498783) (nat_lit 2311445374) (nat_lit 0) D2M8K2.t4681 from rfl, totK_node, tot4680, tot4681]
  decide +kernel

theorem arows4677 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4677 = true := by
  rw [show D2M8K2.u4677 = KTree.node D2M8K2.t4682 (nat_lit 10500539) (nat_lit 2220219088) (nat_lit 0) D2M8K2.t4683 from rfl, allE_node, rows4682, irow4677, rows4683]
  all_goals rfl

theorem atot4677 : totK PD2M8K2 D2M8K2.u4677 = [0, 292907975013, 891376807752, 611350478403, 61904385307, 0, 0, 0] := by
  rw [show D2M8K2.u4677 = KTree.node D2M8K2.t4682 (nat_lit 10500539) (nat_lit 2220219088) (nat_lit 0) D2M8K2.t4683 from rfl, totK_node, tot4682, tot4683]
  decide +kernel

theorem arows4679 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4679 = true := by
  rw [show D2M8K2.u4679 = KTree.node D2M8K2.t4684 (nat_lit 10502535) (nat_lit 3461015343) (nat_lit 0) D2M8K2.t4685 from rfl, allE_node, rows4684, irow4679, rows4685]
  all_goals rfl

theorem atot4679 : totK PD2M8K2 D2M8K2.u4679 = [0, 161066439721, 662995412417, 773351769390, 219809273320, 9054182512, 0, 0] := by
  rw [show D2M8K2.u4679 = KTree.node D2M8K2.t4684 (nat_lit 10502535) (nat_lit 3461015343) (nat_lit 0) D2M8K2.t4685 from rfl, totK_node, tot4684, tot4685]
  decide +kernel

theorem arows4680 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4680 = true := by
  rw [show D2M8K2.u4680 = KTree.node D2M8K2.t4686 (nat_lit 10504179) (nat_lit 2986295984) (nat_lit 0) D2M8K2.t4687 from rfl, allE_node, rows4686, irow4680, rows4687]
  all_goals rfl

theorem atot4680 : totK PD2M8K2 D2M8K2.u4680 = [0, 265819678958, 809146603039, 630502639141, 100959724140, 1197396724, 0, 0] := by
  rw [show D2M8K2.u4680 = KTree.node D2M8K2.t4686 (nat_lit 10504179) (nat_lit 2986295984) (nat_lit 0) D2M8K2.t4687 from rfl, totK_node, tot4686, tot4687]
  decide +kernel

theorem arows4684 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4684 = true := by
  rw [show D2M8K2.u4684 = KTree.node D2M8K2.t4688 (nat_lit 10505856) (nat_lit 2308031685) (nat_lit 0) D2M8K2.t4689 from rfl, allE_node, rows4688, irow4684, rows4689]
  all_goals rfl

theorem atot4684 : totK PD2M8K2 D2M8K2.u4684 = [0, 154825709772, 636513626304, 762982544565, 229371281581, 12040273252, 0, 0] := by
  rw [show D2M8K2.u4684 = KTree.node D2M8K2.t4688 (nat_lit 10505856) (nat_lit 2308031685) (nat_lit 0) D2M8K2.t4689 from rfl, totK_node, tot4688, tot4689]
  decide +kernel

theorem arows4685 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4685 = true := by
  rw [show D2M8K2.u4685 = KTree.node D2M8K2.t4690 (nat_lit 10507264) (nat_lit 1484497042) (nat_lit 0) D2M8K2.t4691 from rfl, allE_node, rows4690, irow4685, rows4691]
  all_goals rfl

theorem atot4685 : totK PD2M8K2 D2M8K2.u4685 = [0, 257043485040, 823377304883, 630305994565, 88078102252, 1096156699, 0, 0] := by
  rw [show D2M8K2.u4685 = KTree.node D2M8K2.t4690 (nat_lit 10507264) (nat_lit 1484497042) (nat_lit 0) D2M8K2.t4691 from rfl, totK_node, tot4690, tot4691]
  decide +kernel

theorem arows4687 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4687 = true := by
  rw [show D2M8K2.u4687 = KTree.node D2M8K2.t4692 (nat_lit 10509264) (nat_lit 3539979997) (nat_lit 0) D2M8K2.t4693 from rfl, allE_node, rows4692, irow4687, rows4693]
  all_goals rfl

theorem atot4687 : totK PD2M8K2 D2M8K2.u4687 = [0, 157245094994, 712281482886, 804326662284, 163610566703, 3880716147, 0, 0] := by
  rw [show D2M8K2.u4687 = KTree.node D2M8K2.t4692 (nat_lit 10509264) (nat_lit 3539979997) (nat_lit 0) D2M8K2.t4693 from rfl, totK_node, tot4692, tot4693]
  decide +kernel

theorem arows4688 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4688 = true := by
  rw [show D2M8K2.u4688 = KTree.node D2M8K2.t4694 (nat_lit 10511142) (nat_lit 3739187072) (nat_lit 0) D2M8K2.t4695 from rfl, allE_node, rows4694, irow4688, rows4695]
  all_goals rfl

theorem atot4688 : totK PD2M8K2 D2M8K2.u4688 = [0, 260280242241, 807347538145, 644324239824, 106884198452, 1267860612, 0, 0] := by
  rw [show D2M8K2.u4688 = KTree.node D2M8K2.t4694 (nat_lit 10511142) (nat_lit 3739187072) (nat_lit 0) D2M8K2.t4695 from rfl, totK_node, tot4694, tot4695]
  decide +kernel

theorem arows4691 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4691 = true := by
  rw [show D2M8K2.u4691 = KTree.node D2M8K2.t4696 (nat_lit 10512871) (nat_lit 2194641651) (nat_lit 0) D2M8K2.t4697 from rfl, allE_node, rows4696, irow4691, rows4697]
  all_goals rfl

theorem atot4691 : totK PD2M8K2 D2M8K2.u4691 = [0, 0, 387324086581, 948633883754, 442642710458, 35478303242, 0, 0] := by
  rw [show D2M8K2.u4691 = KTree.node D2M8K2.t4696 (nat_lit 10512871) (nat_lit 2194641651) (nat_lit 0) D2M8K2.t4697 from rfl, totK_node, tot4696, tot4697]
  decide +kernel

theorem arows4692 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4692 = true := by
  rw [show D2M8K2.u4692 = KTree.node D2M8K2.t4698 (nat_lit 10517746) (nat_lit 4102572518) (nat_lit 0) D2M8K2.t4699 from rfl, allE_node, rows4698, irow4692, rows4699]
  all_goals rfl

theorem atot4692 : totK PD2M8K2 D2M8K2.u4692 = [0, 0, 349876969871, 934568139805, 522117654378, 35708359549, 0, 0] := by
  rw [show D2M8K2.u4692 = KTree.node D2M8K2.t4698 (nat_lit 10517746) (nat_lit 4102572518) (nat_lit 0) D2M8K2.t4699 from rfl, totK_node, tot4698, tot4699]
  decide +kernel

theorem arows4694 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4694 = true := by
  rw [show D2M8K2.u4694 = KTree.node D2M8K2.t4700 (nat_lit 10519229) (nat_lit 1806730160) (nat_lit 0) D2M8K2.t4701 from rfl, allE_node, rows4700, irow4694, rows4701]
  all_goals rfl

theorem atot4694 : totK PD2M8K2 D2M8K2.u4694 = [0, 0, 0, 392631227260, 941938424795, 432142494062, 30397782892, 0] := by
  rw [show D2M8K2.u4694 = KTree.node D2M8K2.t4700 (nat_lit 10519229) (nat_lit 1806730160) (nat_lit 0) D2M8K2.t4701 from rfl, totK_node, tot4700, tot4701]
  decide +kernel

theorem arows4695 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4695 = true := by
  rw [show D2M8K2.u4695 = KTree.node D2M8K2.t4702 (nat_lit 10520739) (nat_lit 3642048460) (nat_lit 0) D2M8K2.t4703 from rfl, allE_node, rows4702, irow4695, rows4703]
  all_goals rfl

theorem atot4695 : totK PD2M8K2 D2M8K2.u4695 = [0, 0, 345816497617, 829758545278, 534482615610, 123268060257, 6524090962, 0] := by
  rw [show D2M8K2.u4695 = KTree.node D2M8K2.t4702 (nat_lit 10520739) (nat_lit 3642048460) (nat_lit 0) D2M8K2.t4703 from rfl, totK_node, tot4702, tot4703]
  decide +kernel

theorem arows4700 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4700 = true := by
  rw [show D2M8K2.u4700 = KTree.node D2M8K2.t4704 (nat_lit 10522983) (nat_lit 2436066882) (nat_lit 0) D2M8K2.t4705 from rfl, allE_node, rows4704, irow4700, rows4705]
  all_goals rfl

theorem atot4700 : totK PD2M8K2 D2M8K2.u4700 = [0, 0, 105119095157, 639919402987, 867226928081, 193586644347, 5159868635, 0] := by
  rw [show D2M8K2.u4700 = KTree.node D2M8K2.t4704 (nat_lit 10522983) (nat_lit 2436066882) (nat_lit 0) D2M8K2.t4705 from rfl, totK_node, tot4704, tot4705]
  decide +kernel

theorem arows4701 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4701 = true := by
  rw [show D2M8K2.u4701 = KTree.node D2M8K2.t4706 (nat_lit 10524694) (nat_lit 2039815628) (nat_lit 0) D2M8K2.t4707 from rfl, allE_node, rows4706, irow4701, rows4707]
  all_goals rfl

theorem atot4701 : totK PD2M8K2 D2M8K2.u4701 = [0, 0, 320138404609, 904020943826, 548366851087, 47202389886, 0, 0] := by
  rw [show D2M8K2.u4701 = KTree.node D2M8K2.t4706 (nat_lit 10524694) (nat_lit 2039815628) (nat_lit 0) D2M8K2.t4707 from rfl, totK_node, tot4706, tot4707]
  decide +kernel

theorem arows4703 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4703 = true := by
  rw [show D2M8K2.u4703 = KTree.node D2M8K2.t4708 (nat_lit 10526493) (nat_lit 1561392632) (nat_lit 0) D2M8K2.t4709 from rfl, allE_node, rows4708, irow4703, rows4709]
  all_goals rfl

theorem atot4703 : totK PD2M8K2 D2M8K2.u4703 = [0, 0, 131086254231, 631694499631, 807289881596, 203498942051, 5218872685, 0] := by
  rw [show D2M8K2.u4703 = KTree.node D2M8K2.t4708 (nat_lit 10526493) (nat_lit 1561392632) (nat_lit 0) D2M8K2.t4709 from rfl, totK_node, tot4708, tot4709]
  decide +kernel

theorem arows4704 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4704 = true := by
  rw [show D2M8K2.u4704 = KTree.node D2M8K2.t4710 (nat_lit 10527956) (nat_lit 3673606522) (nat_lit 0) D2M8K2.t4711 from rfl, allE_node, rows4710, irow4704, rows4711]
  all_goals rfl

theorem atot4704 : totK PD2M8K2 D2M8K2.u4704 = [0, 0, 276009319144, 881381937460, 597501135435, 55519874488, 0, 0] := by
  rw [show D2M8K2.u4704 = KTree.node D2M8K2.t4710 (nat_lit 10527956) (nat_lit 3673606522) (nat_lit 0) D2M8K2.t4711 from rfl, totK_node, tot4710, tot4711]
  decide +kernel

theorem arows4707 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4707 = true := by
  rw [show D2M8K2.u4707 = KTree.node D2M8K2.t4712 (nat_lit 10530032) (nat_lit 3770030118) (nat_lit 0) D2M8K2.t4713 from rfl, allE_node, rows4712, irow4707, rows4713]
  all_goals rfl

theorem atot4707 : totK PD2M8K2 D2M8K2.u4707 = [0, 0, 159781670224, 720547385837, 810212427186, 141902911683, 1415142070, 0] := by
  rw [show D2M8K2.u4707 = KTree.node D2M8K2.t4712 (nat_lit 10530032) (nat_lit 3770030118) (nat_lit 0) D2M8K2.t4713 from rfl, totK_node, tot4712, tot4713]
  decide +kernel

theorem arows4708 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4708 = true := by
  rw [show D2M8K2.u4708 = KTree.node D2M8K2.t4714 (nat_lit 10531915) (nat_lit 1779442534) (nat_lit 0) D2M8K2.t4715 from rfl, allE_node, rows4714, irow4708, rows4715]
  all_goals rfl

theorem atot4708 : totK PD2M8K2 D2M8K2.u4708 = [0, 0, 252886418292, 876339690409, 634544573422, 66834222733, 0, 0] := by
  rw [show D2M8K2.u4708 = KTree.node D2M8K2.t4714 (nat_lit 10531915) (nat_lit 1779442534) (nat_lit 0) D2M8K2.t4715 from rfl, totK_node, tot4714, tot4715]
  decide +kernel

theorem arows4710 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4710 = true := by
  rw [show D2M8K2.u4710 = KTree.node D2M8K2.t4716 (nat_lit 10533812) (nat_lit 776286307) (nat_lit 0) D2M8K2.t4717 from rfl, allE_node, rows4716, irow4710, rows4717]
  all_goals rfl

theorem atot4710 : totK PD2M8K2 D2M8K2.u4710 = [0, 192215718355, 430449928107, 352822450221, 550462223523, 224968711298, 9302370699, 0] := by
  rw [show D2M8K2.u4710 = KTree.node D2M8K2.t4716 (nat_lit 10533812) (nat_lit 776286307) (nat_lit 0) D2M8K2.t4717 from rfl, totK_node, tot4716, tot4717]
  decide +kernel

theorem arows4711 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4711 = true := by
  rw [show D2M8K2.u4711 = KTree.node D2M8K2.t4718 (nat_lit 10576894) (nat_lit 3898541858) (nat_lit 0) D2M8K2.t4719 from rfl, allE_node, rows4718, irow4711, rows4719]
  all_goals rfl

theorem atot4711 : totK PD2M8K2 D2M8K2.u4711 = [0, 205349030773, 768007813479, 692326008047, 104056395522, 1369150432, 0, 0] := by
  rw [show D2M8K2.u4711 = KTree.node D2M8K2.t4718 (nat_lit 10576894) (nat_lit 3898541858) (nat_lit 0) D2M8K2.t4719 from rfl, totK_node, tot4718, tot4719]
  decide +kernel

theorem arows4715 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4715 = true := by
  rw [show D2M8K2.u4715 = KTree.node D2M8K2.t4720 (nat_lit 10579296) (nat_lit 1988803719) (nat_lit 0) D2M8K2.t4721 from rfl, allE_node, rows4720, irow4715, rows4721]
  all_goals rfl

theorem atot4715 : totK PD2M8K2 D2M8K2.u4715 = [0, 252616569578, 830944229260, 689616108300, 76549360185, 0, 0, 0] := by
  rw [show D2M8K2.u4715 = KTree.node D2M8K2.t4720 (nat_lit 10579296) (nat_lit 1988803719) (nat_lit 0) D2M8K2.t4721 from rfl, totK_node, tot4720, tot4721]
  decide +kernel

theorem arows4716 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4716 = true := by
  rw [show D2M8K2.u4716 = KTree.node D2M8K2.t4722 (nat_lit 10580527) (nat_lit 2172298818) (nat_lit 0) D2M8K2.t4723 from rfl, allE_node, rows4722, irow4716, rows4723]
  all_goals rfl

theorem atot4716 : totK PD2M8K2 D2M8K2.u4716 = [0, 174351684497, 650408575089, 693986756535, 270751310125, 25330507241, 0, 0] := by
  rw [show D2M8K2.u4716 = KTree.node D2M8K2.t4722 (nat_lit 10580527) (nat_lit 2172298818) (nat_lit 0) D2M8K2.t4723 from rfl, totK_node, tot4722, tot4723]
  decide +kernel

theorem arows4718 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4718 = true := by
  rw [show D2M8K2.u4718 = KTree.node D2M8K2.t4724 (nat_lit 10582046) (nat_lit 3868203270) (nat_lit 0) D2M8K2.t4725 from rfl, allE_node, rows4724, irow4718, rows4725]
  all_goals rfl

theorem atot4718 : totK PD2M8K2 D2M8K2.u4718 = [0, 167885818788, 585832685400, 755374307087, 297245281546, 12206425282, 0, 0] := by
  rw [show D2M8K2.u4718 = KTree.node D2M8K2.t4724 (nat_lit 10582046) (nat_lit 3868203270) (nat_lit 0) D2M8K2.t4725 from rfl, totK_node, tot4724, tot4725]
  decide +kernel

theorem arows4719 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4719 = true := by
  rw [show D2M8K2.u4719 = KTree.node D2M8K2.t4726 (nat_lit 10586964) (nat_lit 3189404005) (nat_lit 0) D2M8K2.t4727 from rfl, allE_node, rows4726, irow4719, rows4727]
  all_goals rfl

theorem atot4719 : totK PD2M8K2 D2M8K2.u4719 = [0, 278140295513, 884735854040, 616080294314, 57918642832, 0, 0, 0] := by
  rw [show D2M8K2.u4719 = KTree.node D2M8K2.t4726 (nat_lit 10586964) (nat_lit 3189404005) (nat_lit 0) D2M8K2.t4727 from rfl, totK_node, tot4726, tot4727]
  decide +kernel

theorem arows4722 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4722 = true := by
  rw [show D2M8K2.u4722 = KTree.node D2M8K2.t4728 (nat_lit 10588630) (nat_lit 2472814113) (nat_lit 0) D2M8K2.t4729 from rfl, allE_node, rows4728, irow4722, rows4729]
  all_goals rfl

theorem atot4722 : totK PD2M8K2 D2M8K2.u4722 = [0, 82383434728, 514497040827, 878040235333, 295490599822, 13250685261, 0, 0] := by
  rw [show D2M8K2.u4722 = KTree.node D2M8K2.t4728 (nat_lit 10588630) (nat_lit 2472814113) (nat_lit 0) D2M8K2.t4729 from rfl, totK_node, tot4728, tot4729]
  decide +kernel

theorem arows4723 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4723 = true := by
  rw [show D2M8K2.u4723 = KTree.node D2M8K2.t4730 (nat_lit 10590012) (nat_lit 2746392015) (nat_lit 0) D2M8K2.t4731 from rfl, allE_node, rows4730, irow4723, rows4731]
  all_goals rfl

theorem atot4723 : totK PD2M8K2 D2M8K2.u4723 = [0, 333726769081, 921591478698, 513109729180, 41569147078, 0, 0, 0] := by
  rw [show D2M8K2.u4723 = KTree.node D2M8K2.t4730 (nat_lit 10590012) (nat_lit 2746392015) (nat_lit 0) D2M8K2.t4731 from rfl, totK_node, tot4730, tot4731]
  decide +kernel

theorem arows4725 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4725 = true := by
  rw [show D2M8K2.u4725 = KTree.node D2M8K2.t4732 (nat_lit 10591870) (nat_lit 3628312335) (nat_lit 0) D2M8K2.t4733 from rfl, allE_node, rows4732, irow4725, rows4733]
  all_goals rfl

theorem atot4725 : totK PD2M8K2 D2M8K2.u4725 = [0, 87517773469, 611775939408, 870666883487, 195969652809, 4980514959, 0, 0] := by
  rw [show D2M8K2.u4725 = KTree.node D2M8K2.t4732 (nat_lit 10591870) (nat_lit 3628312335) (nat_lit 0) D2M8K2.t4733 from rfl, totK_node, tot4732, tot4733]
  decide +kernel

theorem arows4726 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4726 = true := by
  rw [show D2M8K2.u4726 = KTree.node D2M8K2.t4734 (nat_lit 10593547) (nat_lit 1809559591) (nat_lit 0) D2M8K2.t4735 from rfl, allE_node, rows4734, irow4726, rows4735]
  all_goals rfl

theorem atot4726 : totK PD2M8K2 D2M8K2.u4726 = [0, 329533111629, 900320813326, 552332445974, 49545896764, 0, 0, 0] := by
  rw [show D2M8K2.u4726 = KTree.node D2M8K2.t4734 (nat_lit 10593547) (nat_lit 1809559591) (nat_lit 0) D2M8K2.t4735 from rfl, totK_node, tot4734, tot4735]
  decide +kernel

theorem arows4733 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4733 = true := by
  rw [show D2M8K2.u4733 = KTree.node D2M8K2.t4736 (nat_lit 10595244) (nat_lit 3446338038) (nat_lit 0) D2M8K2.t4737 from rfl, allE_node, rows4736, irow4733, rows4737]
  all_goals rfl

theorem atot4733 : totK PD2M8K2 D2M8K2.u4733 = [0, 0, 407680727504, 958885976857, 386233568869, 20535456378, 0, 0] := by
  rw [show D2M8K2.u4733 = KTree.node D2M8K2.t4736 (nat_lit 10595244) (nat_lit 3446338038) (nat_lit 0) D2M8K2.t4737 from rfl, totK_node, tot4736, tot4737]
  decide +kernel

theorem arows4734 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4734 = true := by
  rw [show D2M8K2.u4734 = KTree.node D2M8K2.t4738 (nat_lit 10597176) (nat_lit 3428286285) (nat_lit 0) D2M8K2.t4739 from rfl, allE_node, rows4738, irow4734, rows4739]
  all_goals rfl

theorem atot4734 : totK PD2M8K2 D2M8K2.u4734 = [0, 0, 371744335844, 957653597544, 403597902426, 17202633404, 0, 0] := by
  rw [show D2M8K2.u4734 = KTree.node D2M8K2.t4738 (nat_lit 10597176) (nat_lit 3428286285) (nat_lit 0) D2M8K2.t4739 from rfl, totK_node, tot4738, tot4739]
  decide +kernel

theorem arows4736 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4736 = true := by
  rw [show D2M8K2.u4736 = KTree.node D2M8K2.t4740 (nat_lit 10599038) (nat_lit 1735661779) (nat_lit 0) D2M8K2.t4741 from rfl, allE_node, rows4740, irow4736, rows4741]
  all_goals rfl

theorem atot4736 : totK PD2M8K2 D2M8K2.u4736 = [0, 0, 127856504783, 699082593448, 824304507256, 125450044238, 1239866073, 0] := by
  rw [show D2M8K2.u4736 = KTree.node D2M8K2.t4740 (nat_lit 10599038) (nat_lit 1735661779) (nat_lit 0) D2M8K2.t4741 from rfl, totK_node, tot4740, tot4741]
  decide +kernel

theorem arows4737 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4737 = true := by
  rw [show D2M8K2.u4737 = KTree.node D2M8K2.t4742 (nat_lit 10600816) (nat_lit 3302483968) (nat_lit 0) D2M8K2.t4743 from rfl, allE_node, rows4742, irow4737, rows4743]
  all_goals rfl

theorem atot4737 : totK PD2M8K2 D2M8K2.u4737 = [0, 0, 380843599048, 946218326144, 455979268636, 28255216686, 0, 0] := by
  rw [show D2M8K2.u4737 = KTree.node D2M8K2.t4742 (nat_lit 10600816) (nat_lit 3302483968) (nat_lit 0) D2M8K2.t4743 from rfl, totK_node, tot4742, tot4743]
  decide +kernel

theorem arows4740 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4740 = true := by
  rw [show D2M8K2.u4740 = KTree.node D2M8K2.t4744 (nat_lit 10607503) (nat_lit 2359552723) (nat_lit 0) D2M8K2.t4745 from rfl, allE_node, rows4744, irow4740, rows4745]
  all_goals rfl

theorem atot4740 : totK PD2M8K2 D2M8K2.u4740 = [0, 0, 358226245047, 945668582516, 488735112465, 33126339569, 0, 0] := by
  rw [show D2M8K2.u4740 = KTree.node D2M8K2.t4744 (nat_lit 10607503) (nat_lit 2359552723) (nat_lit 0) D2M8K2.t4745 from rfl, totK_node, tot4744, tot4745]
  decide +kernel

theorem arows4741 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4741 = true := by
  rw [show D2M8K2.u4741 = KTree.node D2M8K2.t4746 (nat_lit 10609182) (nat_lit 3970774059) (nat_lit 0) D2M8K2.t4747 from rfl, allE_node, rows4746, irow4741, rows4747]
  all_goals rfl

theorem atot4741 : totK PD2M8K2 D2M8K2.u4741 = [0, 0, 30602484562, 503627792485, 909955101303, 282895020859, 13105450397, 0] := by
  rw [show D2M8K2.u4741 = KTree.node D2M8K2.t4746 (nat_lit 10609182) (nat_lit 3970774059) (nat_lit 0) D2M8K2.t4747 from rfl, totK_node, tot4746, tot4747]
  decide +kernel

theorem arows4743 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4743 = true := by
  rw [show D2M8K2.u4743 = KTree.node D2M8K2.t4748 (nat_lit 10610597) (nat_lit 2279533142) (nat_lit 0) D2M8K2.t4749 from rfl, allE_node, rows4748, irow4743, rows4749]
  all_goals rfl

theorem atot4743 : totK PD2M8K2 D2M8K2.u4743 = [0, 0, 381728741764, 949094599862, 433236761985, 24247689074, 0, 0] := by
  rw [show D2M8K2.u4743 = KTree.node D2M8K2.t4748 (nat_lit 10610597) (nat_lit 2279533142) (nat_lit 0) D2M8K2.t4749 from rfl, totK_node, tot4748, tot4749]
  decide +kernel

theorem arows4744 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4744 = true := by
  rw [show D2M8K2.u4744 = KTree.node D2M8K2.t4750 (nat_lit 10612550) (nat_lit 3814240438) (nat_lit 0) D2M8K2.t4751 from rfl, allE_node, rows4750, irow4744, rows4751]
  all_goals rfl

theorem atot4744 : totK PD2M8K2 D2M8K2.u4744 = [0, 0, 82821601848, 651792177235, 808132149648, 156984269846, 4720618446, 0] := by
  rw [show D2M8K2.u4744 = KTree.node D2M8K2.t4750 (nat_lit 10612550) (nat_lit 3814240438) (nat_lit 0) D2M8K2.t4751 from rfl, totK_node, tot4750, tot4751]
  decide +kernel

theorem arows4748 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4748 = true := by
  rw [show D2M8K2.u4748 = KTree.node D2M8K2.t4752 (nat_lit 10614266) (nat_lit 4212797547) (nat_lit 0) D2M8K2.t4753 from rfl, allE_node, rows4752, irow4748, rows4753]
  all_goals rfl

theorem atot4748 : totK PD2M8K2 D2M8K2.u4748 = [0, 18870634022, 351135029809, 893541875839, 518989533534, 43903073402, 0, 0] := by
  rw [show D2M8K2.u4748 = KTree.node D2M8K2.t4752 (nat_lit 10614266) (nat_lit 4212797547) (nat_lit 0) D2M8K2.t4753 from rfl, totK_node, tot4752, tot4753]
  decide +kernel

theorem arows4749 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4749 = true := by
  rw [show D2M8K2.u4749 = KTree.node D2M8K2.t4754 (nat_lit 10617820) (nat_lit 1469314069) (nat_lit 0) D2M8K2.t4755 from rfl, allE_node, rows4754, irow4749, rows4755]
  all_goals rfl

theorem atot4749 : totK PD2M8K2 D2M8K2.u4749 = [0, 358188648638, 933892598572, 451956300178, 26316183552, 0, 0, 0] := by
  rw [show D2M8K2.u4749 = KTree.node D2M8K2.t4754 (nat_lit 10617820) (nat_lit 1469314069) (nat_lit 0) D2M8K2.t4755 from rfl, totK_node, tot4754, tot4755]
  decide +kernel

theorem arows4751 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4751 = true := by
  rw [show D2M8K2.u4751 = KTree.node D2M8K2.t4756 (nat_lit 10619760) (nat_lit 3527819012) (nat_lit 0) D2M8K2.t4757 from rfl, allE_node, rows4756, irow4751, rows4757]
  all_goals rfl

theorem atot4751 : totK PD2M8K2 D2M8K2.u4751 = [0, 136979003893, 672421195965, 857994805938, 147381912091, 1369150432, 0, 0] := by
  rw [show D2M8K2.u4751 = KTree.node D2M8K2.t4756 (nat_lit 10619760) (nat_lit 3527819012) (nat_lit 0) D2M8K2.t4757 from rfl, totK_node, tot4756, tot4757]
  decide +kernel

theorem arows4752 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4752 = true := by
  rw [show D2M8K2.u4752 = KTree.node D2M8K2.t4758 (nat_lit 10621525) (nat_lit 1216467566) (nat_lit 0) D2M8K2.t4759 from rfl, allE_node, rows4758, irow4752, rows4759]
  all_goals rfl

theorem atot4752 : totK PD2M8K2 D2M8K2.u4752 = [0, 279007554561, 878532678916, 594358427489, 82595638967, 5319205844, 0, 0] := by
  rw [show D2M8K2.u4752 = KTree.node D2M8K2.t4758 (nat_lit 10621525) (nat_lit 1216467566) (nat_lit 0) D2M8K2.t4759 from rfl, totK_node, tot4758, tot4759]
  decide +kernel

theorem arows4755 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4755 = true := by
  rw [show D2M8K2.u4755 = KTree.node D2M8K2.t4760 (nat_lit 10623110) (nat_lit 3089259579) (nat_lit 0) D2M8K2.t4761 from rfl, allE_node, rows4760, irow4755, rows4761]
  all_goals rfl

theorem atot4755 : totK PD2M8K2 D2M8K2.u4755 = [0, 28553961470, 357234553877, 900459430963, 495950043277, 30550322668, 0, 0] := by
  rw [show D2M8K2.u4755 = KTree.node D2M8K2.t4760 (nat_lit 10623110) (nat_lit 3089259579) (nat_lit 0) D2M8K2.t4761 from rfl, totK_node, tot4760, tot4761]
  decide +kernel

theorem arows4756 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4756 = true := by
  rw [show D2M8K2.u4756 = KTree.node D2M8K2.t4762 (nat_lit 10624430) (nat_lit 3795001974) (nat_lit 0) D2M8K2.t4763 from rfl, allE_node, rows4762, irow4756, rows4763]
  all_goals rfl

theorem atot4756 : totK PD2M8K2 D2M8K2.u4756 = [0, 298544272889, 890496114617, 567513868717, 56600089775, 0, 0, 0] := by
  rw [show D2M8K2.u4756 = KTree.node D2M8K2.t4762 (nat_lit 10624430) (nat_lit 3795001974) (nat_lit 0) D2M8K2.t4763 from rfl, totK_node, tot4762, tot4763]
  decide +kernel

theorem arows4758 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4758 = true := by
  rw [show D2M8K2.u4758 = KTree.node D2M8K2.t4764 (nat_lit 10626824) (nat_lit 3643950755) (nat_lit 0) D2M8K2.t4765 from rfl, allE_node, rows4764, irow4758, rows4765]
  all_goals rfl

theorem atot4758 : totK PD2M8K2 D2M8K2.u4758 = [0, 171060998881, 658334963894, 748090596042, 207550506586, 11885407614, 0, 0] := by
  rw [show D2M8K2.u4758 = KTree.node D2M8K2.t4764 (nat_lit 10626824) (nat_lit 3643950755) (nat_lit 0) D2M8K2.t4765 from rfl, totK_node, tot4764, tot4765]
  decide +kernel

theorem arows4759 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4759 = true := by
  rw [show D2M8K2.u4759 = KTree.node D2M8K2.t4766 (nat_lit 10628606) (nat_lit 2974626180) (nat_lit 0) D2M8K2.t4767 from rfl, allE_node, rows4766, irow4759, rows4767]
  all_goals rfl

theorem atot4759 : totK PD2M8K2 D2M8K2.u4759 = [0, 252764219752, 796006308908, 641436892915, 106012030409, 1198073392, 0, 0] := by
  rw [show D2M8K2.u4759 = KTree.node D2M8K2.t4766 (nat_lit 10628606) (nat_lit 2974626180) (nat_lit 0) D2M8K2.t4767 from rfl, totK_node, tot4766, tot4767]
  decide +kernel

theorem arows4764 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4764 = true := by
  rw [show D2M8K2.u4764 = KTree.node D2M8K2.t4768 (nat_lit 10630321) (nat_lit 1367406749) (nat_lit 0) D2M8K2.t4769 from rfl, allE_node, rows4768, irow4764, rows4769]
  all_goals rfl

theorem atot4764 : totK PD2M8K2 D2M8K2.u4764 = [0, 172401869485, 651491947140, 730233487641, 223314040825, 12052611869, 0, 0] := by
  rw [show D2M8K2.u4764 = KTree.node D2M8K2.t4768 (nat_lit 10630321) (nat_lit 1367406749) (nat_lit 0) D2M8K2.t4769 from rfl, totK_node, tot4768, tot4769]
  decide +kernel

theorem arows4765 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4765 = true := by
  rw [show D2M8K2.u4765 = KTree.node D2M8K2.t4770 (nat_lit 10631672) (nat_lit 3506633385) (nat_lit 0) D2M8K2.t4771 from rfl, allE_node, rows4770, irow4765, rows4771]
  all_goals rfl

theorem atot4765 : totK PD2M8K2 D2M8K2.u4765 = [0, 263337885134, 829201999021, 617227495698, 83199728450, 1096505104, 0, 0] := by
  rw [show D2M8K2.u4765 = KTree.node D2M8K2.t4770 (nat_lit 10631672) (nat_lit 3506633385) (nat_lit 0) D2M8K2.t4771 from rfl, totK_node, tot4770, tot4771]
  decide +kernel

theorem arows4767 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4767 = true := by
  rw [show D2M8K2.u4767 = KTree.node D2M8K2.t4772 (nat_lit 10633606) (nat_lit 2485729109) (nat_lit 0) D2M8K2.t4773 from rfl, allE_node, rows4772, irow4767, rows4773]
  all_goals rfl

theorem atot4767 : totK PD2M8K2 D2M8K2.u4767 = [0, 0, 499412404825, 1017356043528, 274955562967, 6406394852, 0, 0] := by
  rw [show D2M8K2.u4767 = KTree.node D2M8K2.t4772 (nat_lit 10633606) (nat_lit 2485729109) (nat_lit 0) D2M8K2.t4773 from rfl, totK_node, tot4772, tot4773]
  decide +kernel

theorem arows4768 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4768 = true := by
  rw [show D2M8K2.u4768 = KTree.node D2M8K2.t4774 (nat_lit 10638972) (nat_lit 2956998195) (nat_lit 0) D2M8K2.t4775 from rfl, allE_node, rows4774, irow4768, rows4775]
  all_goals rfl

theorem atot4768 : totK PD2M8K2 D2M8K2.u4768 = [0, 0, 224736758046, 800412965932, 616112195724, 79672617609, 1138244013, 0] := by
  rw [show D2M8K2.u4768 = KTree.node D2M8K2.t4774 (nat_lit 10638972) (nat_lit 2956998195) (nat_lit 0) D2M8K2.t4775 from rfl, totK_node, tot4774, tot4775]
  decide +kernel

theorem arows4771 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4771 = true := by
  rw [show D2M8K2.u4771 = KTree.node D2M8K2.t4776 (nat_lit 10641594) (nat_lit 3434149563) (nat_lit 0) D2M8K2.t4777 from rfl, allE_node, rows4776, irow4771, rows4777]
  all_goals rfl

theorem atot4771 : totK PD2M8K2 D2M8K2.u4771 = [0, 0, 293688545313, 880120695060, 581161411056, 56629086751, 0, 0] := by
  rw [show D2M8K2.u4771 = KTree.node D2M8K2.t4776 (nat_lit 10641594) (nat_lit 3434149563) (nat_lit 0) D2M8K2.t4777 from rfl, totK_node, tot4776, tot4777]
  decide +kernel

theorem arows4772 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4772 = true := by
  rw [show D2M8K2.u4772 = KTree.node D2M8K2.t4778 (nat_lit 10644673) (nat_lit 1490658461) (nat_lit 0) D2M8K2.t4779 from rfl, allE_node, rows4778, irow4772, rows4779]
  all_goals rfl

theorem atot4772 : totK PD2M8K2 D2M8K2.u4772 = [0, 0, 364070637963, 954897020055, 469787053800, 27818890997, 0, 0] := by
  rw [show D2M8K2.u4772 = KTree.node D2M8K2.t4778 (nat_lit 10644673) (nat_lit 1490658461) (nat_lit 0) D2M8K2.t4779 from rfl, totK_node, tot4778, tot4779]
  decide +kernel

theorem arows4774 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4774 = true := by
  rw [show D2M8K2.u4774 = KTree.node D2M8K2.t4780 (nat_lit 10648282) (nat_lit 3215556067) (nat_lit 0) D2M8K2.t4781 from rfl, allE_node, rows4780, irow4774, rows4781]
  all_goals rfl

theorem atot4774 : totK PD2M8K2 D2M8K2.u4774 = [0, 0, 385791667009, 951433487511, 441376162032, 24978964003, 0, 0] := by
  rw [show D2M8K2.u4774 = KTree.node D2M8K2.t4780 (nat_lit 10648282) (nat_lit 3215556067) (nat_lit 0) D2M8K2.t4781 from rfl, totK_node, tot4780, tot4781]
  decide +kernel

theorem arows4775 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4775 = true := by
  rw [show D2M8K2.u4775 = KTree.node D2M8K2.t4782 (nat_lit 10651524) (nat_lit 3265684583) (nat_lit 0) D2M8K2.t4783 from rfl, allE_node, rows4782, irow4775, rows4783]
  all_goals rfl

theorem atot4775 : totK PD2M8K2 D2M8K2.u4775 = [0, 0, 377424191155, 941872427196, 434473559499, 24625985610, 0, 0] := by
  rw [show D2M8K2.u4775 = KTree.node D2M8K2.t4782 (nat_lit 10651524) (nat_lit 3265684583) (nat_lit 0) D2M8K2.t4783 from rfl, totK_node, tot4782, tot4783]
  decide +kernel

theorem arows4779 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4779 = true := by
  rw [show D2M8K2.u4779 = KTree.node D2M8K2.t4784 (nat_lit 10652723) (nat_lit 1520163882) (nat_lit 0) D2M8K2.t4785 from rfl, allE_node, rows4784, irow4779, rows4785]
  all_goals rfl

theorem atot4779 : totK PD2M8K2 D2M8K2.u4779 = [0, 0, 180273317021, 773374789585, 689364845360, 103558629446, 1095107716, 0] := by
  rw [show D2M8K2.u4779 = KTree.node D2M8K2.t4784 (nat_lit 10652723) (nat_lit 1520163882) (nat_lit 0) D2M8K2.t4785 from rfl, totK_node, tot4784, tot4785]
  decide +kernel

theorem arows4780 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4780 = true := by
  rw [show D2M8K2.u4780 = KTree.node D2M8K2.t4786 (nat_lit 10658461) (nat_lit 1369820453) (nat_lit 0) D2M8K2.t4787 from rfl, allE_node, rows4786, irow4780, rows4787]
  all_goals rfl

theorem atot4780 : totK PD2M8K2 D2M8K2.u4780 = [0, 255770503163, 619779288078, 452643204087, 341420710378, 104267637556, 3882006667, 0] := by
  rw [show D2M8K2.u4780 = KTree.node D2M8K2.t4786 (nat_lit 10658461) (nat_lit 1369820453) (nat_lit 0) D2M8K2.t4787 from rfl, totK_node, tot4786, tot4787]
  decide +kernel

theorem arows4782 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4782 = true := by
  rw [show D2M8K2.u4782 = KTree.node D2M8K2.t4788 (nat_lit 10660157) (nat_lit 2253302634) (nat_lit 0) D2M8K2.t4789 from rfl, allE_node, rows4788, irow4782, rows4789]
  all_goals rfl

theorem atot4782 : totK PD2M8K2 D2M8K2.u4782 = [0, 123340586977, 704613832017, 832449299478, 132624610784, 1369150432, 0, 0] := by
  rw [show D2M8K2.u4782 = KTree.node D2M8K2.t4788 (nat_lit 10660157) (nat_lit 2253302634) (nat_lit 0) D2M8K2.t4789 from rfl, totK_node, tot4788, tot4789]
  decide +kernel

theorem arows4783 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4783 = true := by
  rw [show D2M8K2.u4783 = KTree.node D2M8K2.t4790 (nat_lit 10662581) (nat_lit 2259175320) (nat_lit 0) D2M8K2.t4791 from rfl, allE_node, rows4790, irow4783, rows4791]
  all_goals rfl

theorem atot4783 : totK PD2M8K2 D2M8K2.u4783 = [0, 365434831173, 928606209863, 516890721313, 46503435847, 0, 0, 0] := by
  rw [show D2M8K2.u4783 = KTree.node D2M8K2.t4790 (nat_lit 10662581) (nat_lit 2259175320) (nat_lit 0) D2M8K2.t4791 from rfl, totK_node, tot4790, tot4791]
  decide +kernel

theorem arows4786 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4786 = true := by
  rw [show D2M8K2.u4786 = KTree.node D2M8K2.t4792 (nat_lit 10664091) (nat_lit 3765844345) (nat_lit 0) D2M8K2.t4793 from rfl, allE_node, rows4792, irow4786, rows4793]
  all_goals rfl

theorem atot4786 : totK PD2M8K2 D2M8K2.u4786 = [0, 55729936123, 490002730479, 871124870979, 385296845072, 29340748455, 0, 0] := by
  rw [show D2M8K2.u4786 = KTree.node D2M8K2.t4792 (nat_lit 10664091) (nat_lit 3765844345) (nat_lit 0) D2M8K2.t4793 from rfl, totK_node, tot4792, tot4793]
  decide +kernel

theorem arows4787 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4787 = true := by
  rw [show D2M8K2.u4787 = KTree.node D2M8K2.t4794 (nat_lit 10665486) (nat_lit 3544939789) (nat_lit 0) D2M8K2.t4795 from rfl, allE_node, rows4794, irow4787, rows4795]
  all_goals rfl

theorem atot4787 : totK PD2M8K2 D2M8K2.u4787 = [0, 241060917665, 724498648519, 660437272512, 201022478510, 8213711289, 0, 0] := by
  rw [show D2M8K2.u4787 = KTree.node D2M8K2.t4794 (nat_lit 10665486) (nat_lit 3544939789) (nat_lit 0) D2M8K2.t4795 from rfl, totK_node, tot4794, tot4795]
  decide +kernel

theorem arows4789 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4789 = true := by
  rw [show D2M8K2.u4789 = KTree.node D2M8K2.t4796 (nat_lit 10667331) (nat_lit 3691899134) (nat_lit 0) D2M8K2.t4797 from rfl, allE_node, rows4796, irow4789, rows4797]
  all_goals rfl

theorem atot4789 : totK PD2M8K2 D2M8K2.u4789 = [0, 146252562081, 638449432459, 813737351288, 212622750418, 8182332651, 0, 0] := by
  rw [show D2M8K2.u4789 = KTree.node D2M8K2.t4796 (nat_lit 10667331) (nat_lit 3691899134) (nat_lit 0) D2M8K2.t4797 from rfl, totK_node, tot4796, tot4797]
  decide +kernel

theorem arows4790 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4790 = true := by
  rw [show D2M8K2.u4790 = KTree.node D2M8K2.t4798 (nat_lit 10669644) (nat_lit 3086516778) (nat_lit 0) D2M8K2.t4799 from rfl, allE_node, rows4798, irow4790, rows4799]
  all_goals rfl

theorem atot4790 : totK PD2M8K2 D2M8K2.u4790 = [0, 363810134684, 937771835115, 484579666562, 36832313232, 0, 0, 0] := by
  rw [show D2M8K2.u4790 = KTree.node D2M8K2.t4798 (nat_lit 10669644) (nat_lit 3086516778) (nat_lit 0) D2M8K2.t4799 from rfl, totK_node, tot4798, tot4799]
  decide +kernel

end QECKChecks.D2M8K2
