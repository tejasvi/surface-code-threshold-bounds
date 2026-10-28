import QEC.Count.ChunksK3
import QEC.KChecks.D2M8K2.A24

namespace QECKChecks.D2M8K2

open QEC QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem arows10634 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10634 = true := by
  rw [show D2M8K2.u10634 = KTree.node D2M8K2.u10626 (nat_lit 23061422) (nat_lit 3338863658) (nat_lit 0) D2M8K2.u10633 from rfl, allE_node, arows10626, irow10634, arows10633]
  all_goals rfl

theorem atot10634 : totK PD2M8K2 D2M8K2.u10634 = [0, 1236106663548, 4756822539998, 5708462225595, 2366610053721, 249662074785, 4720618446, 0] := by
  rw [show D2M8K2.u10634 = KTree.node D2M8K2.u10626 (nat_lit 23061422) (nat_lit 3338863658) (nat_lit 0) D2M8K2.u10633 from rfl, totK_node, atot10626, atot10633]
  decide +kernel

theorem arows10649 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10649 = true := by
  rw [show D2M8K2.u10649 = KTree.node D2M8K2.u10641 (nat_lit 23074364) (nat_lit 3303112170) (nat_lit 0) D2M8K2.u10648 from rfl, allE_node, arows10641, irow10649, arows10648]
  all_goals rfl

theorem atot10649 : totK PD2M8K2 D2M8K2.u10649 = [0, 866248944588, 4320365154244, 6407007843213, 2523972967967, 192646974499, 1138244013, 0] := by
  rw [show D2M8K2.u10649 = KTree.node D2M8K2.u10641 (nat_lit 23074364) (nat_lit 3303112170) (nat_lit 0) D2M8K2.u10648 from rfl, totK_node, atot10641, atot10648]
  decide +kernel

theorem arows10665 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10665 = true := by
  rw [show D2M8K2.u10665 = KTree.node D2M8K2.u10657 (nat_lit 23142194) (nat_lit 3566918759) (nat_lit 0) D2M8K2.u10664 from rfl, allE_node, arows10657, irow10665, arows10664]
  all_goals rfl

theorem atot10665 : totK PD2M8K2 D2M8K2.u10665 = [0, 0, 2184300167657, 6783694212968, 4728378579374, 543468900943, 7510584435, 0] := by
  rw [show D2M8K2.u10665 = KTree.node D2M8K2.u10657 (nat_lit 23142194) (nat_lit 3566918759) (nat_lit 0) D2M8K2.u10664 from rfl, totK_node, atot10657, atot10664]
  decide +kernel

theorem arows10680 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10680 = true := by
  rw [show D2M8K2.u10680 = KTree.node D2M8K2.u10672 (nat_lit 23160610) (nat_lit 3586168257) (nat_lit 0) D2M8K2.u10679 from rfl, allE_node, arows10672, irow10680, arows10679]
  all_goals rfl

theorem atot10680 : totK PD2M8K2 D2M8K2.u10680 = [0, 0, 778786707230, 4521380587131, 6559610467143, 2048054050234, 126120188603, 1209030869] := by
  rw [show D2M8K2.u10680 = KTree.node D2M8K2.u10672 (nat_lit 23160610) (nat_lit 3586168257) (nat_lit 0) D2M8K2.u10679 from rfl, totK_node, atot10672, atot10679]
  decide +kernel

theorem arows10697 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10697 = true := by
  rw [show D2M8K2.u10697 = KTree.node D2M8K2.u10689 (nat_lit 23190951) (nat_lit 3623179397) (nat_lit 0) D2M8K2.u10696 from rfl, allE_node, arows10689, irow10697, arows10696]
  all_goals rfl

theorem atot10697 : totK PD2M8K2 D2M8K2.u10697 = [0, 0, 1658888281368, 5945559785484, 5704583767109, 1200187460154, 41475137636, 0] := by
  rw [show D2M8K2.u10697 = KTree.node D2M8K2.u10689 (nat_lit 23190951) (nat_lit 3623179397) (nat_lit 0) D2M8K2.u10696 from rfl, totK_node, atot10689, atot10696]
  decide +kernel

theorem arows10712 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10712 = true := by
  rw [show D2M8K2.u10712 = KTree.node D2M8K2.u10704 (nat_lit 23231956) (nat_lit 3772581810) (nat_lit 0) D2M8K2.u10711 from rfl, allE_node, arows10704, irow10712, arows10711]
  all_goals rfl

theorem atot10712 : totK PD2M8K2 D2M8K2.u10712 = [0, 0, 2300113105362, 6809130968051, 4683129026109, 584687289616, 13730349181, 0] := by
  rw [show D2M8K2.u10712 = KTree.node D2M8K2.u10704 (nat_lit 23231956) (nat_lit 3772581810) (nat_lit 0) D2M8K2.u10711 from rfl, totK_node, atot10704, atot10711]
  decide +kernel

theorem arows10728 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10728 = true := by
  rw [show D2M8K2.u10728 = KTree.node D2M8K2.u10720 (nat_lit 23277778) (nat_lit 4052852322) (nat_lit 0) D2M8K2.u10727 from rfl, allE_node, arows10720, irow10728, arows10727]
  all_goals rfl

theorem atot10728 : totK PD2M8K2 D2M8K2.u10728 = [0, 0, 1695729188399, 6040104001503, 5633737672007, 1070794779465, 34528040727, 0] := by
  rw [show D2M8K2.u10728 = KTree.node D2M8K2.u10720 (nat_lit 23277778) (nat_lit 4052852322) (nat_lit 0) D2M8K2.u10727 from rfl, totK_node, atot10720, atot10727]
  decide +kernel

theorem arows10743 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10743 = true := by
  rw [show D2M8K2.u10743 = KTree.node D2M8K2.u10735 (nat_lit 23313561) (nat_lit 1866620659) (nat_lit 0) D2M8K2.u10742 from rfl, allE_node, arows10735, irow10743, arows10742]
  all_goals rfl

theorem atot10743 : totK PD2M8K2 D2M8K2.u10743 = [0, 0, 1639341000235, 5926411248589, 5566377949609, 1080588667268, 36516822950, 0] := by
  rw [show D2M8K2.u10743 = KTree.node D2M8K2.u10735 (nat_lit 23313561) (nat_lit 1866620659) (nat_lit 0) D2M8K2.u10742 from rfl, totK_node, atot10735, atot10742]
  decide +kernel

theorem arows10763 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10763 = true := by
  rw [show D2M8K2.u10763 = KTree.node D2M8K2.u10755 (nat_lit 23331996) (nat_lit 1513981102) (nat_lit 32) D2M8K2.u10762 from rfl, allE_node, arows10755, irow10763, arows10762]
  all_goals rfl

theorem atot10763 : totK PD2M8K2 D2M8K2.u10763 = [0, 0, 441947594641, 3679695703890, 6814561154798, 2895358140199, 236090924497, 2233351729] := by
  rw [show D2M8K2.u10763 = KTree.node D2M8K2.u10755 (nat_lit 23331996) (nat_lit 1513981102) (nat_lit 32) D2M8K2.u10762 from rfl, totK_node, atot10755, atot10762]
  decide +kernel

theorem arows10778 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10778 = true := by
  rw [show D2M8K2.u10778 = KTree.node D2M8K2.u10770 (nat_lit 23400360) (nat_lit 3346331192) (nat_lit 0) D2M8K2.u10777 from rfl, allE_node, arows10770, irow10778, arows10777]
  all_goals rfl

theorem atot10778 : totK PD2M8K2 D2M8K2.u10778 = [0, 1713929917221, 5888858226680, 5175212924862, 1123717199935, 343743223465, 93467172928, 3882006667] := by
  rw [show D2M8K2.u10778 = KTree.node D2M8K2.u10770 (nat_lit 23400360) (nat_lit 3346331192) (nat_lit 0) D2M8K2.u10777 from rfl, totK_node, atot10770, atot10777]
  decide +kernel

theorem arows10794 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10794 = true := by
  rw [show D2M8K2.u10794 = KTree.node D2M8K2.u10786 (nat_lit 23418338) (nat_lit 4073644854) (nat_lit 0) D2M8K2.u10793 from rfl, allE_node, arows10786, irow10794, arows10793]
  all_goals rfl

theorem atot10794 : totK PD2M8K2 D2M8K2.u10794 = [0, 359043461885, 3301842791887, 6946678534045, 3370775505726, 260695370579, 1369150432, 0] := by
  rw [show D2M8K2.u10794 = KTree.node D2M8K2.u10786 (nat_lit 23418338) (nat_lit 4073644854) (nat_lit 0) D2M8K2.u10793 from rfl, totK_node, atot10786, atot10793]
  decide +kernel

theorem arows10809 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10809 = true := by
  rw [show D2M8K2.u10809 = KTree.node D2M8K2.u10801 (nat_lit 23441817) (nat_lit 1563049636) (nat_lit 0) D2M8K2.u10808 from rfl, allE_node, arows10801, irow10809, arows10808]
  all_goals rfl

theorem atot10809 : totK PD2M8K2 D2M8K2.u10809 = [0, 1643660559386, 5812229817814, 5702585989870, 1412562188015, 63097357971, 0, 0] := by
  rw [show D2M8K2.u10809 = KTree.node D2M8K2.u10801 (nat_lit 23441817) (nat_lit 1563049636) (nat_lit 0) D2M8K2.u10808 from rfl, totK_node, atot10801, atot10808]
  decide +kernel

theorem arows10826 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10826 = true := by
  rw [show D2M8K2.u10826 = KTree.node D2M8K2.u10818 (nat_lit 23459101) (nat_lit 777049550) (nat_lit 0) D2M8K2.u10825 from rfl, allE_node, arows10818, irow10826, arows10825]
  all_goals rfl

theorem atot10826 : totK PD2M8K2 D2M8K2.u10826 = [0, 265593258125, 2458359286057, 6016556300311, 4748673167508, 997360881421, 39858646648, 0] := by
  rw [show D2M8K2.u10826 = KTree.node D2M8K2.u10818 (nat_lit 23459101) (nat_lit 777049550) (nat_lit 0) D2M8K2.u10825 from rfl, totK_node, atot10818, atot10825]
  decide +kernel

theorem arows10841 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10841 = true := by
  rw [show D2M8K2.u10841 = KTree.node D2M8K2.u10833 (nat_lit 23474458) (nat_lit 2794032120) (nat_lit 0) D2M8K2.u10840 from rfl, allE_node, arows10833, irow10841, arows10840]
  all_goals rfl

theorem atot10841 : totK PD2M8K2 D2M8K2.u10841 = [0, 1104445359803, 4241755034908, 5629690265140, 3050729505512, 480860035345, 10717512769, 0] := by
  rw [show D2M8K2.u10841 = KTree.node D2M8K2.u10833 (nat_lit 23474458) (nat_lit 2794032120) (nat_lit 0) D2M8K2.u10840 from rfl, totK_node, atot10833, atot10840]
  decide +kernel

theorem arows10857 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10857 = true := by
  rw [show D2M8K2.u10857 = KTree.node D2M8K2.u10849 (nat_lit 23494903) (nat_lit 2265317970) (nat_lit 0) D2M8K2.u10856 from rfl, allE_node, arows10849, irow10857, arows10856]
  all_goals rfl

theorem atot10857 : totK PD2M8K2 D2M8K2.u10857 = [0, 553264517824, 3543846621254, 6493801920725, 3405755728683, 364440199975, 6601594569, 0] := by
  rw [show D2M8K2.u10857 = KTree.node D2M8K2.u10849 (nat_lit 23494903) (nat_lit 2265317970) (nat_lit 0) D2M8K2.u10856 from rfl, totK_node, atot10849, atot10856]
  decide +kernel

theorem arows10872 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10872 = true := by
  rw [show D2M8K2.u10872 = KTree.node D2M8K2.u10864 (nat_lit 23519531) (nat_lit 2919674126) (nat_lit 0) D2M8K2.u10871 from rfl, allE_node, arows10864, irow10872, arows10871]
  all_goals rfl

theorem atot10872 : totK PD2M8K2 D2M8K2.u10872 = [0, 1449096466084, 5370470289022, 5805366387247, 1787041596967, 106576762825, 0, 0] := by
  rw [show D2M8K2.u10872 = KTree.node D2M8K2.u10864 (nat_lit 23519531) (nat_lit 2919674126) (nat_lit 0) D2M8K2.u10871 from rfl, totK_node, atot10864, atot10871]
  decide +kernel

theorem arows10890 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10890 = true := by
  rw [show D2M8K2.u10890 = KTree.node D2M8K2.u10882 (nat_lit 23536534) (nat_lit 2772899451) (nat_lit 0) D2M8K2.u10889 from rfl, allE_node, arows10882, irow10890, arows10889]
  all_goals rfl

theorem atot10890 : totK PD2M8K2 D2M8K2.u10890 = [0, 587450886773, 3573036393930, 6371901609610, 3423714837542, 423487003978, 10873128647, 0] := by
  rw [show D2M8K2.u10890 = KTree.node D2M8K2.u10882 (nat_lit 23536534) (nat_lit 2772899451) (nat_lit 0) D2M8K2.u10889 from rfl, totK_node, atot10882, atot10889]
  decide +kernel

theorem arows10905 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10905 = true := by
  rw [show D2M8K2.u10905 = KTree.node D2M8K2.u10897 (nat_lit 23599064) (nat_lit 2821486641) (nat_lit 0) D2M8K2.u10904 from rfl, allE_node, arows10897, irow10905, arows10904]
  all_goals rfl

theorem atot10905 : totK PD2M8K2 D2M8K2.u10905 = [0, 1115800468970, 4444075790569, 5752545948502, 2707300806996, 342636457776, 8192806269, 0] := by
  rw [show D2M8K2.u10905 = KTree.node D2M8K2.u10897 (nat_lit 23599064) (nat_lit 2821486641) (nat_lit 0) D2M8K2.u10904 from rfl, totK_node, atot10897, atot10904]
  decide +kernel

theorem arows10921 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10921 = true := by
  rw [show D2M8K2.u10921 = KTree.node D2M8K2.u10913 (nat_lit 23615685) (nat_lit 781041713) (nat_lit 0) D2M8K2.u10920 from rfl, allE_node, arows10913, irow10921, arows10920]
  all_goals rfl

theorem atot10921 : totK PD2M8K2 D2M8K2.u10921 = [0, 996132207003, 4499247141547, 6180613606544, 2522094488055, 203572639977, 1310285577, 0] := by
  rw [show D2M8K2.u10921 = KTree.node D2M8K2.u10913 (nat_lit 23615685) (nat_lit 781041713) (nat_lit 0) D2M8K2.u10920 from rfl, totK_node, atot10913, atot10920]
  decide +kernel

theorem arows10936 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10936 = true := by
  rw [show D2M8K2.u10936 = KTree.node D2M8K2.u10928 (nat_lit 23631421) (nat_lit 1053827254) (nat_lit 0) D2M8K2.u10935 from rfl, allE_node, arows10928, irow10936, arows10935]
  all_goals rfl

theorem atot10936 : totK PD2M8K2 D2M8K2.u10936 = [442400928062, 1270137119403, 2280222633115, 5104320194759, 4371961440218, 848333500767, 31562413104, 0] := by
  rw [show D2M8K2.u10936 = KTree.node D2M8K2.u10928 (nat_lit 23631421) (nat_lit 1053827254) (nat_lit 0) D2M8K2.u10935 from rfl, totK_node, atot10928, atot10935]
  decide +kernel

theorem arows10953 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10953 = true := by
  rw [show D2M8K2.u10953 = KTree.node D2M8K2.u10945 (nat_lit 23900832) (nat_lit 3697930913) (nat_lit 0) D2M8K2.u10952 from rfl, allE_node, arows10945, irow10953, arows10952]
  all_goals rfl

theorem atot10953 : totK PD2M8K2 D2M8K2.u10953 = [1654538655177, 5931236140668, 5606211327951, 1100594658885, 32549666757, 0, 0, 0] := by
  rw [show D2M8K2.u10953 = KTree.node D2M8K2.u10945 (nat_lit 23900832) (nat_lit 3697930913) (nat_lit 0) D2M8K2.u10952 from rfl, totK_node, atot10945, atot10952]
  decide +kernel

theorem arows10968 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10968 = true := by
  rw [show D2M8K2.u10968 = KTree.node D2M8K2.u10960 (nat_lit 23919391) (nat_lit 2315318345) (nat_lit 0) D2M8K2.u10967 from rfl, allE_node, arows10960, irow10968, arows10967]
  all_goals rfl

theorem atot10968 : totK PD2M8K2 D2M8K2.u10968 = [384126823169, 3239343043503, 6770578633167, 3483767911574, 291689303802, 1369150432, 0, 0] := by
  rw [show D2M8K2.u10968 = KTree.node D2M8K2.u10960 (nat_lit 23919391) (nat_lit 2315318345) (nat_lit 0) D2M8K2.u10967 from rfl, totK_node, atot10960, atot10967]
  decide +kernel

theorem arows10984 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10984 = true := by
  rw [show D2M8K2.u10984 = KTree.node D2M8K2.u10976 (nat_lit 23979546) (nat_lit 2749447626) (nat_lit 0) D2M8K2.u10983 from rfl, allE_node, arows10976, irow10984, arows10983]
  all_goals rfl

theorem atot10984 : totK PD2M8K2 D2M8K2.u10984 = [1598617840249, 5828760472807, 5715922577853, 1273811673903, 51643047417, 0, 0, 0] := by
  rw [show D2M8K2.u10984 = KTree.node D2M8K2.u10976 (nat_lit 23979546) (nat_lit 2749447626) (nat_lit 0) D2M8K2.u10983 from rfl, totK_node, atot10976, atot10983]
  decide +kernel

theorem arows10999 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u10999 = true := by
  rw [show D2M8K2.u10999 = KTree.node D2M8K2.u10991 (nat_lit 23999083) (nat_lit 1397377182) (nat_lit 0) D2M8K2.u10998 from rfl, allE_node, arows10991, irow10999, arows10998]
  all_goals rfl

theorem atot10999 : totK PD2M8K2 D2M8K2.u10999 = [0, 2127899027774, 6592241393507, 4727500337668, 689072915236, 18797058808, 0, 0] := by
  rw [show D2M8K2.u10999 = KTree.node D2M8K2.u10991 (nat_lit 23999083) (nat_lit 1397377182) (nat_lit 0) D2M8K2.u10998 from rfl, totK_node, atot10991, atot10998]
  decide +kernel

theorem arows11018 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11018 = true := by
  rw [show D2M8K2.u11018 = KTree.node D2M8K2.u11010 (nat_lit 24018944) (nat_lit 3136187275) (nat_lit 0) D2M8K2.u11017 from rfl, allE_node, arows11010, irow11018, arows11017]
  all_goals rfl

theorem atot11018 : totK PD2M8K2 D2M8K2.u11018 = [1600040782559, 5746113756430, 5650883965441, 1402348238041, 70309313384, 0, 0, 0] := by
  rw [show D2M8K2.u11018 = KTree.node D2M8K2.u11010 (nat_lit 24018944) (nat_lit 3136187275) (nat_lit 0) D2M8K2.u11017 from rfl, totK_node, atot11010, atot11017]
  decide +kernel

theorem arows11033 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11033 = true := by
  rw [show D2M8K2.u11033 = KTree.node D2M8K2.u11025 (nat_lit 24036314) (nat_lit 3846786942) (nat_lit 0) D2M8K2.u11032 from rfl, allE_node, arows11025, irow11033, arows11032]
  all_goals rfl

theorem atot11033 : totK PD2M8K2 D2M8K2.u11033 = [383209705629, 3002501390746, 6397415022328, 3939870402489, 533085918353, 14345316470, 0, 0] := by
  rw [show D2M8K2.u11033 = KTree.node D2M8K2.u11025 (nat_lit 24036314) (nat_lit 3846786942) (nat_lit 0) D2M8K2.u11032 from rfl, totK_node, atot11025, atot11032]
  decide +kernel

theorem arows11049 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11049 = true := by
  rw [show D2M8K2.u11049 = KTree.node D2M8K2.u11041 (nat_lit 24057699) (nat_lit 3693876886) (nat_lit 0) D2M8K2.u11048 from rfl, allE_node, arows11041, irow11049, arows11048]
  all_goals rfl

theorem atot11049 : totK PD2M8K2 D2M8K2.u11049 = [1283860474901, 4849208873036, 5683091330046, 2304617189805, 250256406102, 4720618446, 0, 0] := by
  rw [show D2M8K2.u11049 = KTree.node D2M8K2.u11041 (nat_lit 24057699) (nat_lit 3693876886) (nat_lit 0) D2M8K2.u11048 from rfl, totK_node, atot11041, atot11048]
  decide +kernel

theorem arows11064 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11064 = true := by
  rw [show D2M8K2.u11064 = KTree.node D2M8K2.u11056 (nat_lit 24074722) (nat_lit 3727686324) (nat_lit 0) D2M8K2.u11063 from rfl, allE_node, arows11056, irow11064, arows11063]
  all_goals rfl

theorem atot11064 : totK PD2M8K2 D2M8K2.u11064 = [742679185588, 4111747721650, 6563446112838, 2742898422016, 205409351793, 1138244013, 0, 0] := by
  rw [show D2M8K2.u11064 = KTree.node D2M8K2.u11056 (nat_lit 24074722) (nat_lit 3727686324) (nat_lit 0) D2M8K2.u11063 from rfl, totK_node, atot11056, atot11063]
  decide +kernel

theorem arows11081 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11081 = true := by
  rw [show D2M8K2.u11081 = KTree.node D2M8K2.u11073 (nat_lit 24097202) (nat_lit 2035904800) (nat_lit 0) D2M8K2.u11080 from rfl, allE_node, arows11073, irow11081, arows11080]
  all_goals rfl

theorem atot11081 : totK PD2M8K2 D2M8K2.u11081 = [1224181847296, 4820473644850, 5770666446536, 2254394668021, 258012869278, 4977114383, 0, 0] := by
  rw [show D2M8K2.u11081 = KTree.node D2M8K2.u11073 (nat_lit 24097202) (nat_lit 2035904800) (nat_lit 0) D2M8K2.u11080 from rfl, totK_node, atot11073, atot11080]
  decide +kernel

theorem arows11096 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11096 = true := by
  rw [show D2M8K2.u11096 = KTree.node D2M8K2.u11088 (nat_lit 24117845) (nat_lit 1714778539) (nat_lit 0) D2M8K2.u11095 from rfl, allE_node, arows11088, irow11096, arows11095]
  all_goals rfl

theorem atot11096 : totK PD2M8K2 D2M8K2.u11096 = [427832996020, 2951526474384, 6229094245398, 4108011681828, 543598218581, 8351110384, 0, 0] := by
  rw [show D2M8K2.u11096 = KTree.node D2M8K2.u11088 (nat_lit 24117845) (nat_lit 1714778539) (nat_lit 0) D2M8K2.u11095 from rfl, totK_node, atot11088, atot11095]
  decide +kernel

theorem arows11112 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11112 = true := by
  rw [show D2M8K2.u11112 = KTree.node D2M8K2.u11104 (nat_lit 24139314) (nat_lit 3437272954) (nat_lit 0) D2M8K2.u11111 from rfl, allE_node, arows11104, irow11112, arows11111]
  all_goals rfl

theorem atot11112 : totK PD2M8K2 D2M8K2.u11112 = [0, 1696211002443, 5991412308712, 5486927363591, 1061935390181, 38899931047, 0, 0] := by
  rw [show D2M8K2.u11112 = KTree.node D2M8K2.u11104 (nat_lit 24139314) (nat_lit 3437272954) (nat_lit 0) D2M8K2.u11111 from rfl, totK_node, atot11104, atot11111]
  decide +kernel

theorem arows11127 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11127 = true := by
  rw [show D2M8K2.u11127 = KTree.node D2M8K2.u11119 (nat_lit 24156555) (nat_lit 1746260333) (nat_lit 0) D2M8K2.u11126 from rfl, allE_node, arows11119, irow11127, arows11126]
  all_goals rfl

theorem atot11127 : totK PD2M8K2 D2M8K2.u11127 = [0, 816078251927, 4189703744820, 6317630323504, 2492465940567, 235010725973, 1369150432, 0] := by
  rw [show D2M8K2.u11127 = KTree.node D2M8K2.u11119 (nat_lit 24156555) (nat_lit 1746260333) (nat_lit 0) D2M8K2.u11126 from rfl, totK_node, atot11119, atot11126]
  decide +kernel

theorem arows11145 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11145 = true := by
  rw [show D2M8K2.u11145 = KTree.node D2M8K2.u11137 (nat_lit 24222529) (nat_lit 1560988708) (nat_lit 0) D2M8K2.u11144 from rfl, allE_node, arows11137, irow11145, arows11144]
  all_goals rfl

theorem atot11145 : totK PD2M8K2 D2M8K2.u11145 = [0, 1206771856310, 5154885509644, 6184773533105, 1666937312482, 76416331592, 0, 0] := by
  rw [show D2M8K2.u11145 = KTree.node D2M8K2.u11137 (nat_lit 24222529) (nat_lit 1560988708) (nat_lit 0) D2M8K2.u11144 from rfl, totK_node, atot11137, atot11144]
  decide +kernel

theorem arows11160 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11160 = true := by
  rw [show D2M8K2.u11160 = KTree.node D2M8K2.u11152 (nat_lit 24261347) (nat_lit 2357175640) (nat_lit 0) D2M8K2.u11159 from rfl, allE_node, arows11152, irow11160, arows11159]
  all_goals rfl

theorem atot11160 : totK PD2M8K2 D2M8K2.u11160 = [0, 1794908298521, 6120696758383, 5474739125406, 1005587884483, 25319529688, 0, 0] := by
  rw [show D2M8K2.u11160 = KTree.node D2M8K2.u11152 (nat_lit 24261347) (nat_lit 2357175640) (nat_lit 0) D2M8K2.u11159 from rfl, totK_node, atot11152, atot11159]
  decide +kernel

theorem arows11176 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11176 = true := by
  rw [show D2M8K2.u11176 = KTree.node D2M8K2.u11168 (nat_lit 24279396) (nat_lit 3242035592) (nat_lit 0) D2M8K2.u11175 from rfl, allE_node, arows11168, irow11176, arows11175]
  all_goals rfl

theorem atot11176 : totK PD2M8K2 D2M8K2.u11176 = [0, 1720043342954, 5986394017164, 5547344120403, 1077565812294, 33172177045, 0, 0] := by
  rw [show D2M8K2.u11176 = KTree.node D2M8K2.u11168 (nat_lit 24279396) (nat_lit 3242035592) (nat_lit 0) D2M8K2.u11175 from rfl, totK_node, atot11168, atot11175]
  decide +kernel

theorem arows11191 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11191 = true := by
  rw [show D2M8K2.u11191 = KTree.node D2M8K2.u11183 (nat_lit 24314931) (nat_lit 1097298499) (nat_lit 0) D2M8K2.u11190 from rfl, allE_node, arows11183, irow11191, arows11190]
  all_goals rfl

theorem atot11191 : totK PD2M8K2 D2M8K2.u11191 = [0, 1680067086814, 6027836994415, 5588233994668, 1049683495114, 32557842968, 0, 0] := by
  rw [show D2M8K2.u11191 = KTree.node D2M8K2.u11183 (nat_lit 24314931) (nat_lit 1097298499) (nat_lit 0) D2M8K2.u11190 from rfl, totK_node, atot11183, atot11190]
  decide +kernel

theorem arows11208 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11208 = true := by
  rw [show D2M8K2.u11208 = KTree.node D2M8K2.u11200 (nat_lit 24357149) (nat_lit 1569048232) (nat_lit 0) D2M8K2.u11207 from rfl, allE_node, arows11200, irow11208, arows11207]
  all_goals rfl

theorem atot11208 : totK PD2M8K2 D2M8K2.u11208 = [449419051412, 2476186136832, 5519896307305, 4950772440198, 1054878726782, 33598280809, 0, 0] := by
  rw [show D2M8K2.u11208 = KTree.node D2M8K2.u11200 (nat_lit 24357149) (nat_lit 1569048232) (nat_lit 0) D2M8K2.u11207 from rfl, totK_node, atot11200, atot11207]
  decide +kernel

theorem arows11223 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11223 = true := by
  rw [show D2M8K2.u11223 = KTree.node D2M8K2.u11215 (nat_lit 24438817) (nat_lit 1249885254) (nat_lit 0) D2M8K2.u11222 from rfl, allE_node, arows11215, irow11223, arows11222]
  all_goals rfl

theorem atot11223 : totK PD2M8K2 D2M8K2.u11223 = [1592518470355, 5668846704396, 5686876028089, 1447890077655, 58314566070, 0, 0, 0] := by
  rw [show D2M8K2.u11223 = KTree.node D2M8K2.u11215 (nat_lit 24438817) (nat_lit 1249885254) (nat_lit 0) D2M8K2.u11222 from rfl, totK_node, atot11215, atot11222]
  decide +kernel

theorem arows11239 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11239 = true := by
  rw [show D2M8K2.u11239 = KTree.node D2M8K2.u11231 (nat_lit 24455166) (nat_lit 3871041292) (nat_lit 0) D2M8K2.u11238 from rfl, allE_node, arows11231, irow11239, arows11238]
  all_goals rfl

theorem atot11239 : totK PD2M8K2 D2M8K2.u11239 = [75805549015, 2102728238059, 6059827820103, 5036950411200, 1116555507572, 47300615174, 0, 0] := by
  rw [show D2M8K2.u11239 = KTree.node D2M8K2.u11231 (nat_lit 24455166) (nat_lit 3871041292) (nat_lit 0) D2M8K2.u11238 from rfl, totK_node, atot11231, atot11238]
  decide +kernel

theorem arows11254 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11254 = true := by
  rw [show D2M8K2.u11254 = KTree.node D2M8K2.u11246 (nat_lit 24469857) (nat_lit 1830521902) (nat_lit 0) D2M8K2.u11253 from rfl, allE_node, arows11246, irow11254, arows11253]
  all_goals rfl

theorem atot11254 : totK PD2M8K2 D2M8K2.u11254 = [1086769156253, 4099179487527, 5551039033855, 3215338408139, 514753484252, 10717512769, 0, 0] := by
  rw [show D2M8K2.u11254 = KTree.node D2M8K2.u11246 (nat_lit 24469857) (nat_lit 1830521902) (nat_lit 0) D2M8K2.u11253 from rfl, totK_node, atot11246, atot11253]
  decide +kernel

theorem arows11275 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11275 = true := by
  rw [show D2M8K2.u11275 = KTree.node D2M8K2.u11267 (nat_lit 24486798) (nat_lit 3904770424) (nat_lit 0) D2M8K2.u11274 from rfl, allE_node, arows11267, irow11275, arows11274]
  all_goals rfl

theorem atot11275 : totK PD2M8K2 D2M8K2.u11275 = [902357467906, 4450167904625, 6302740307088, 2515661291297, 204215319378, 1206465782, 0, 0] := by
  rw [show D2M8K2.u11275 = KTree.node D2M8K2.u11267 (nat_lit 24486798) (nat_lit 3904770424) (nat_lit 0) D2M8K2.u11274 from rfl, totK_node, atot11267, atot11274]
  decide +kernel

theorem arows11290 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11290 = true := by
  rw [show D2M8K2.u11290 = KTree.node D2M8K2.u11282 (nat_lit 24506884) (nat_lit 3728343416) (nat_lit 0) D2M8K2.u11289 from rfl, allE_node, arows11282, irow11290, arows11289]
  all_goals rfl

theorem atot11290 : totK PD2M8K2 D2M8K2.u11290 = [753971791401, 3609488303471, 5908648568028, 3516948201955, 551875020075, 17590593026, 0, 0] := by
  rw [show D2M8K2.u11290 = KTree.node D2M8K2.u11282 (nat_lit 24506884) (nat_lit 3728343416) (nat_lit 0) D2M8K2.u11289 from rfl, totK_node, atot11282, atot11289]
  decide +kernel

theorem arows11306 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11306 = true := by
  rw [show D2M8K2.u11306 = KTree.node D2M8K2.u11298 (nat_lit 24525602) (nat_lit 3100450130) (nat_lit 0) D2M8K2.u11305 from rfl, allE_node, arows11298, irow11306, arows11305]
  all_goals rfl

theorem atot11306 : totK PD2M8K2 D2M8K2.u11306 = [1239224718697, 4954843552805, 5974083036953, 2080063818428, 152976605357, 1239866073, 0, 0] := by
  rw [show D2M8K2.u11306 = KTree.node D2M8K2.u11298 (nat_lit 24525602) (nat_lit 3100450130) (nat_lit 0) D2M8K2.u11305 from rfl, totK_node, atot11298, atot11305]
  decide +kernel

theorem arows11321 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11321 = true := by
  rw [show D2M8K2.u11321 = KTree.node D2M8K2.u11313 (nat_lit 24545260) (nat_lit 3855776096) (nat_lit 0) D2M8K2.u11320 from rfl, allE_node, arows11313, irow11321, arows11320]
  all_goals rfl

theorem atot11321 : totK PD2M8K2 D2M8K2.u11321 = [433967504439, 3035468704796, 6226680377938, 4053951294092, 612011176857, 17826068843, 0, 0] := by
  rw [show D2M8K2.u11321 = KTree.node D2M8K2.u11313 (nat_lit 24545260) (nat_lit 3855776096) (nat_lit 0) D2M8K2.u11320 from rfl, totK_node, atot11313, atot11320]
  decide +kernel

theorem arows11338 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11338 = true := by
  rw [show D2M8K2.u11338 = KTree.node D2M8K2.u11330 (nat_lit 24561280) (nat_lit 3736311988) (nat_lit 0) D2M8K2.u11337 from rfl, allE_node, arows11330, irow11338, arows11337]
  all_goals rfl

theorem atot11338 : totK PD2M8K2 D2M8K2.u11338 = [1604223981162, 5720776832493, 5651091561398, 1430593552088, 64998625821, 0, 0, 0] := by
  rw [show D2M8K2.u11338 = KTree.node D2M8K2.u11330 (nat_lit 24561280) (nat_lit 3736311988) (nat_lit 0) D2M8K2.u11337 from rfl, totK_node, atot11330, atot11337]
  decide +kernel

theorem arows11353 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11353 = true := by
  rw [show D2M8K2.u11353 = KTree.node D2M8K2.u11345 (nat_lit 24580689) (nat_lit 1265816437) (nat_lit 0) D2M8K2.u11352 from rfl, allE_node, arows11345, irow11353, arows11352]
  all_goals rfl

theorem atot11353 : totK PD2M8K2 D2M8K2.u11353 = [340079057287, 2985204664277, 6681375806660, 3909868472385, 437847296527, 6115358396, 0, 0] := by
  rw [show D2M8K2.u11353 = KTree.node D2M8K2.u11345 (nat_lit 24580689) (nat_lit 1265816437) (nat_lit 0) D2M8K2.u11352 from rfl, totK_node, atot11345, atot11352]
  decide +kernel

theorem arows11369 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11369 = true := by
  rw [show D2M8K2.u11369 = KTree.node D2M8K2.u11361 (nat_lit 24604224) (nat_lit 3280921302) (nat_lit 0) D2M8K2.u11368 from rfl, allE_node, arows11361, irow11369, arows11368]
  all_goals rfl

theorem atot11369 : totK PD2M8K2 D2M8K2.u11369 = [1326121685222, 5247455343356, 5980274654515, 1851815488783, 107784716408, 0, 0, 0] := by
  rw [show D2M8K2.u11369 = KTree.node D2M8K2.u11361 (nat_lit 24604224) (nat_lit 3280921302) (nat_lit 0) D2M8K2.u11368 from rfl, totK_node, atot11361, atot11368]
  decide +kernel

theorem arows11384 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11384 = true := by
  rw [show D2M8K2.u11384 = KTree.node D2M8K2.u11376 (nat_lit 24625998) (nat_lit 3688082976) (nat_lit 0) D2M8K2.u11383 from rfl, allE_node, arows11376, irow11384, arows11383]
  all_goals rfl

theorem atot11384 : totK PD2M8K2 D2M8K2.u11384 = [0, 1995469885097, 6360691320894, 5106207240388, 919296461798, 31562413104, 0, 0] := by
  rw [show D2M8K2.u11384 = KTree.node D2M8K2.u11376 (nat_lit 24625998) (nat_lit 3688082976) (nat_lit 0) D2M8K2.u11383 from rfl, totK_node, atot11376, atot11383]
  decide +kernel

theorem arows11402 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11402 = true := by
  rw [show D2M8K2.u11402 = KTree.node D2M8K2.u11394 (nat_lit 24687451) (nat_lit 2240536079) (nat_lit 0) D2M8K2.u11401 from rfl, allE_node, arows11394, irow11402, arows11401]
  all_goals rfl

theorem atot11402 : totK PD2M8K2 D2M8K2.u11402 = [0, 1576468716494, 5654619111847, 5701566395485, 1447370586947, 57638958396, 0, 0] := by
  rw [show D2M8K2.u11402 = KTree.node D2M8K2.u11394 (nat_lit 24687451) (nat_lit 2240536079) (nat_lit 0) D2M8K2.u11401 from rfl, totK_node, atot11394, atot11401]
  decide +kernel

theorem arows11417 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11417 = true := by
  rw [show D2M8K2.u11417 = KTree.node D2M8K2.u11409 (nat_lit 24703906) (nat_lit 4137393991) (nat_lit 0) D2M8K2.u11416 from rfl, allE_node, arows11409, irow11417, arows11416]
  all_goals rfl

theorem atot11417 : totK PD2M8K2 D2M8K2.u11417 = [0, 91855302876, 2175850017220, 6050748144384, 4909041065254, 1059898764235, 47116249314, 0] := by
  rw [show D2M8K2.u11417 = KTree.node D2M8K2.u11409 (nat_lit 24703906) (nat_lit 4137393991) (nat_lit 0) D2M8K2.u11416 from rfl, totK_node, atot11409, atot11416]
  decide +kernel

theorem arows11433 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11433 = true := by
  rw [show D2M8K2.u11433 = KTree.node D2M8K2.u11425 (nat_lit 24718783) (nat_lit 1326266802) (nat_lit 0) D2M8K2.u11432 from rfl, allE_node, arows11425, irow11433, arows11432]
  all_goals rfl

theorem atot11433 : totK PD2M8K2 D2M8K2.u11433 = [0, 1105660254096, 4161597150800, 5512871235044, 3120440424770, 469467650424, 10531122277, 0] := by
  rw [show D2M8K2.u11433 = KTree.node D2M8K2.u11425 (nat_lit 24718783) (nat_lit 1326266802) (nat_lit 0) D2M8K2.u11432 from rfl, totK_node, atot11425, atot11432]
  decide +kernel

theorem arows11448 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11448 = true := by
  rw [show D2M8K2.u11448 = KTree.node D2M8K2.u11440 (nat_lit 24736062) (nat_lit 3815872651) (nat_lit 0) D2M8K2.u11447 from rfl, allE_node, arows11440, irow11448, arows11447]
  all_goals rfl

theorem atot11448 : totK PD2M8K2 D2M8K2.u11448 = [0, 887006820704, 4639013704386, 6558837000426, 2172533769849, 109560193706, 0, 0] := by
  rw [show D2M8K2.u11448 = KTree.node D2M8K2.u11440 (nat_lit 24736062) (nat_lit 3815872651) (nat_lit 0) D2M8K2.u11447 from rfl, totK_node, atot11440, atot11447]
  decide +kernel

theorem arows11465 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11465 = true := by
  rw [show D2M8K2.u11465 = KTree.node D2M8K2.u11457 (nat_lit 24759054) (nat_lit 3804178593) (nat_lit 0) D2M8K2.u11464 from rfl, allE_node, arows11457, irow11465, arows11464]
  all_goals rfl

theorem atot11465 : totK PD2M8K2 D2M8K2.u11465 = [0, 925695191772, 3961624009463, 5876986080880, 3178894082030, 391803919304, 6546549506, 0] := by
  rw [show D2M8K2.u11465 = KTree.node D2M8K2.u11457 (nat_lit 24759054) (nat_lit 3804178593) (nat_lit 0) D2M8K2.u11464 from rfl, totK_node, atot11457, atot11464]
  decide +kernel

theorem arows11480 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11480 = true := by
  rw [show D2M8K2.u11480 = KTree.node D2M8K2.u11472 (nat_lit 24776555) (nat_lit 2728640004) (nat_lit 0) D2M8K2.u11479 from rfl, allE_node, arows11472, irow11480, arows11479]
  all_goals rfl

theorem atot11480 : totK PD2M8K2 D2M8K2.u11480 = [0, 1067501318326, 4944082799525, 6320119109243, 1981904533728, 102890518112, 0, 0] := by
  rw [show D2M8K2.u11480 = KTree.node D2M8K2.u11472 (nat_lit 24776555) (nat_lit 2728640004) (nat_lit 0) D2M8K2.u11479 from rfl, totK_node, atot11472, atot11479]
  decide +kernel

theorem arows11496 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11496 = true := by
  rw [show D2M8K2.u11496 = KTree.node D2M8K2.u11488 (nat_lit 24798270) (nat_lit 3891323600) (nat_lit 0) D2M8K2.u11495 from rfl, allE_node, arows11488, irow11496, arows11495]
  all_goals rfl

theorem atot11496 : totK PD2M8K2 D2M8K2.u11496 = [0, 770655032679, 3763864272495, 6077619069791, 3327488630060, 400493900371, 6624648996, 0] := by
  rw [show D2M8K2.u11496 = KTree.node D2M8K2.u11488 (nat_lit 24798270) (nat_lit 3891323600) (nat_lit 0) D2M8K2.u11495 from rfl, totK_node, atot11488, atot11495]
  decide +kernel

theorem arows11511 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11511 = true := by
  rw [show D2M8K2.u11511 = KTree.node D2M8K2.u11503 (nat_lit 24813668) (nat_lit 2837818662) (nat_lit 0) D2M8K2.u11510 from rfl, allE_node, arows11503, irow11511, arows11510]
  all_goals rfl

theorem atot11511 : totK PD2M8K2 D2M8K2.u11511 = [0, 1267536452922, 5188356135641, 6078973723785, 1738898267811, 78591147611, 0, 0] := by
  rw [show D2M8K2.u11511 = KTree.node D2M8K2.u11503 (nat_lit 24813668) (nat_lit 2837818662) (nat_lit 0) D2M8K2.u11510 from rfl, totK_node, atot11503, atot11510]
  decide +kernel

theorem arows11530 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11530 = true := by
  rw [show D2M8K2.u11530 = KTree.node D2M8K2.u11522 (nat_lit 24837481) (nat_lit 1468395791) (nat_lit 0) D2M8K2.u11529 from rfl, allE_node, arows11522, irow11530, arows11529]
  all_goals rfl

theorem atot11530 : totK PD2M8K2 D2M8K2.u11530 = [0, 833461993264, 4019625713481, 6301793883515, 2991031662849, 263403926295, 1429815836, 0] := by
  rw [show D2M8K2.u11530 = KTree.node D2M8K2.u11522 (nat_lit 24837481) (nat_lit 1468395791) (nat_lit 0) D2M8K2.u11529 from rfl, totK_node, atot11522, atot11529]
  decide +kernel

theorem arows11545 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11545 = true := by
  rw [show D2M8K2.u11545 = KTree.node D2M8K2.u11537 (nat_lit 24861072) (nat_lit 2748920879) (nat_lit 0) D2M8K2.u11544 from rfl, allE_node, arows11537, irow11545, arows11544]
  all_goals rfl

theorem atot11545 : totK PD2M8K2 D2M8K2.u11545 = [0, 832738749245, 4234534119030, 6371717377905, 2784071070256, 222636231952, 1323630408, 0] := by
  rw [show D2M8K2.u11545 = KTree.node D2M8K2.u11537 (nat_lit 24861072) (nat_lit 2748920879) (nat_lit 0) D2M8K2.u11544 from rfl, totK_node, atot11537, atot11544]
  decide +kernel

theorem arows11561 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11561 = true := by
  rw [show D2M8K2.u11561 = KTree.node D2M8K2.u11553 (nat_lit 24884206) (nat_lit 3994809381) (nat_lit 0) D2M8K2.u11560 from rfl, allE_node, arows11553, irow11561, arows11560]
  all_goals rfl

theorem atot11561 : totK PD2M8K2 D2M8K2.u11561 = [1112982196269, 3610204128253, 3658277578670, 3069337346053, 2444076758030, 429333776462, 10866219959, 0] := by
  rw [show D2M8K2.u11561 = KTree.node D2M8K2.u11553 (nat_lit 24884206) (nat_lit 3994809381) (nat_lit 0) D2M8K2.u11560 from rfl, totK_node, atot11553, atot11560]
  decide +kernel

theorem arows11576 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11576 = true := by
  rw [show D2M8K2.u11576 = KTree.node D2M8K2.u11568 (nat_lit 24902137) (nat_lit 1438272545) (nat_lit 0) D2M8K2.u11575 from rfl, allE_node, arows11568, irow11576, arows11575]
  all_goals rfl

theorem atot11576 : totK PD2M8K2 D2M8K2.u11576 = [862794591548, 4237668757002, 6258505630795, 2591035339773, 226316596781, 1369150432, 0, 0] := by
  rw [show D2M8K2.u11576 = KTree.node D2M8K2.u11568 (nat_lit 24902137) (nat_lit 1438272545) (nat_lit 0) D2M8K2.u11575 from rfl, totK_node, atot11568, atot11575]
  decide +kernel

theorem arows11593 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11593 = true := by
  rw [show D2M8K2.u11593 = KTree.node D2M8K2.u11585 (nat_lit 24929525) (nat_lit 2212901226) (nat_lit 0) D2M8K2.u11592 from rfl, allE_node, arows11585, irow11593, arows11592]
  all_goals rfl

theorem atot11593 : totK PD2M8K2 D2M8K2.u11593 = [1045530226874, 4630768489483, 6319540659316, 2337135197871, 130008668942, 0, 0, 0] := by
  rw [show D2M8K2.u11593 = KTree.node D2M8K2.u11585 (nat_lit 24929525) (nat_lit 2212901226) (nat_lit 0) D2M8K2.u11592 from rfl, totK_node, atot11585, atot11592]
  decide +kernel

theorem arows11608 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11608 = true := by
  rw [show D2M8K2.u11608 = KTree.node D2M8K2.u11600 (nat_lit 24943461) (nat_lit 1273821565) (nat_lit 0) D2M8K2.u11607 from rfl, allE_node, arows11600, irow11608, arows11607]
  all_goals rfl

theorem atot11608 : totK PD2M8K2 D2M8K2.u11608 = [954788030929, 4255625594817, 5774153003850, 2868763287227, 637771198343, 36921873854, 0, 0] := by
  rw [show D2M8K2.u11608 = KTree.node D2M8K2.u11600 (nat_lit 24943461) (nat_lit 1273821565) (nat_lit 0) D2M8K2.u11607 from rfl, totK_node, atot11600, atot11607]
  decide +kernel

theorem arows11624 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11624 = true := by
  rw [show D2M8K2.u11624 = KTree.node D2M8K2.u11616 (nat_lit 24960417) (nat_lit 1858652781) (nat_lit 0) D2M8K2.u11623 from rfl, allE_node, arows11616, irow11624, arows11623]
  all_goals rfl

theorem atot11624 : totK PD2M8K2 D2M8K2.u11624 = [413201475250, 2464433967268, 5649064899246, 4937091473344, 959436247184, 21096254089, 0, 0] := by
  rw [show D2M8K2.u11624 = KTree.node D2M8K2.u11616 (nat_lit 24960417) (nat_lit 1858652781) (nat_lit 0) D2M8K2.u11623 from rfl, totK_node, atot11616, atot11623]
  decide +kernel

theorem arows11639 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11639 = true := by
  rw [show D2M8K2.u11639 = KTree.node D2M8K2.u11631 (nat_lit 24974544) (nat_lit 3531234453) (nat_lit 0) D2M8K2.u11638 from rfl, allE_node, arows11631, irow11639, arows11638]
  all_goals rfl

theorem atot11639 : totK PD2M8K2 D2M8K2.u11639 = [1639033896282, 5786641688968, 5659035959133, 1349594911705, 56794176367, 0, 0, 0] := by
  rw [show D2M8K2.u11639 = KTree.node D2M8K2.u11631 (nat_lit 24974544) (nat_lit 3531234453) (nat_lit 0) D2M8K2.u11638 from rfl, totK_node, atot11631, atot11638]
  decide +kernel

theorem arows11657 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11657 = true := by
  rw [show D2M8K2.u11657 = KTree.node D2M8K2.u11649 (nat_lit 24991919) (nat_lit 2777346994) (nat_lit 0) D2M8K2.u11656 from rfl, allE_node, arows11649, irow11657, arows11656]
  all_goals rfl

theorem atot11657 : totK PD2M8K2 D2M8K2.u11657 = [54703274150, 2287778704898, 6610578703962, 4561028139570, 635274562449, 16235284024, 0, 0] := by
  rw [show D2M8K2.u11657 = KTree.node D2M8K2.u11649 (nat_lit 24991919) (nat_lit 2777346994) (nat_lit 0) D2M8K2.u11656 from rfl, totK_node, atot11649, atot11656]
  decide +kernel

theorem arows11672 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11672 = true := by
  rw [show D2M8K2.u11672 = KTree.node D2M8K2.u11664 (nat_lit 25054029) (nat_lit 1322713873) (nat_lit 0) D2M8K2.u11671 from rfl, allE_node, arows11664, irow11672, arows11671]
  all_goals rfl

theorem atot11672 : totK PD2M8K2 D2M8K2.u11672 = [1506026836868, 5409400436588, 5663422716368, 1726351687197, 127156604790, 2561774784, 0, 0] := by
  rw [show D2M8K2.u11672 = KTree.node D2M8K2.u11664 (nat_lit 25054029) (nat_lit 1322713873) (nat_lit 0) D2M8K2.u11671 from rfl, totK_node, atot11664, atot11671]
  decide +kernel

theorem arows11688 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11688 = true := by
  rw [show D2M8K2.u11688 = KTree.node D2M8K2.u11680 (nat_lit 25071170) (nat_lit 3629444655) (nat_lit 0) D2M8K2.u11687 from rfl, allE_node, arows11680, irow11688, arows11687]
  all_goals rfl

theorem atot11688 : totK PD2M8K2 D2M8K2.u11688 = [527805388803, 3797195826337, 6804859378969, 3012387234776, 223356575039, 1138244013, 0, 0] := by
  rw [show D2M8K2.u11688 = KTree.node D2M8K2.u11680 (nat_lit 25071170) (nat_lit 3629444655) (nat_lit 0) D2M8K2.u11687 from rfl, totK_node, atot11680, atot11687]
  decide +kernel

theorem arows11703 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11703 = true := by
  rw [show D2M8K2.u11703 = KTree.node D2M8K2.u11695 (nat_lit 25094544) (nat_lit 1944959761) (nat_lit 0) D2M8K2.u11702 from rfl, allE_node, arows11695, irow11703, arows11702]
  all_goals rfl

theorem atot11703 : totK PD2M8K2 D2M8K2.u11703 = [1230007923653, 4742483611545, 5742129372933, 2384797040008, 279546277041, 4977114383, 0, 0] := by
  rw [show D2M8K2.u11703 = KTree.node D2M8K2.u11695 (nat_lit 25094544) (nat_lit 1944959761) (nat_lit 0) D2M8K2.u11702 from rfl, totK_node, atot11695, atot11702]
  decide +kernel

theorem arows11720 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11720 = true := by
  rw [show D2M8K2.u11720 = KTree.node D2M8K2.u11712 (nat_lit 25114532) (nat_lit 2206049803) (nat_lit 0) D2M8K2.u11719 from rfl, allE_node, arows11712, irow11720, arows11719]
  all_goals rfl

theorem atot11720 : totK PD2M8K2 D2M8K2.u11720 = [427983732745, 3155315594954, 6467851192532, 3890358972836, 442257951852, 6190125969, 0, 0] := by
  rw [show D2M8K2.u11720 = KTree.node D2M8K2.u11712 (nat_lit 25114532) (nat_lit 2206049803) (nat_lit 0) D2M8K2.u11719 from rfl, totK_node, atot11712, atot11719]
  decide +kernel

theorem arows11735 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11735 = true := by
  rw [show D2M8K2.u11735 = KTree.node D2M8K2.u11727 (nat_lit 25140195) (nat_lit 3565561496) (nat_lit 0) D2M8K2.u11734 from rfl, allE_node, arows11727, irow11735, arows11734]
  all_goals rfl

theorem atot11735 : totK PD2M8K2 D2M8K2.u11735 = [0, 1682396682190, 5972142420265, 5483543946413, 1081485891321, 38464624228, 0, 0] := by
  rw [show D2M8K2.u11735 = KTree.node D2M8K2.u11727 (nat_lit 25140195) (nat_lit 3565561496) (nat_lit 0) D2M8K2.u11734 from rfl, totK_node, atot11727, atot11734]
  decide +kernel

theorem arows11751 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11751 = true := by
  rw [show D2M8K2.u11751 = KTree.node D2M8K2.u11743 (nat_lit 25155382) (nat_lit 2984481679) (nat_lit 0) D2M8K2.u11750 from rfl, allE_node, arows11743, irow11751, arows11750]
  all_goals rfl

theorem atot11751 : totK PD2M8K2 D2M8K2.u11751 = [0, 420903066044, 3670634130882, 6994195497325, 2802011087953, 192604386134, 1275377855, 0] := by
  rw [show D2M8K2.u11751 = KTree.node D2M8K2.u11743 (nat_lit 25155382) (nat_lit 2984481679) (nat_lit 0) D2M8K2.u11750 from rfl, totK_node, atot11743, atot11750]
  decide +kernel

theorem arows11766 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11766 = true := by
  rw [show D2M8K2.u11766 = KTree.node D2M8K2.u11758 (nat_lit 25182967) (nat_lit 1136478385) (nat_lit 0) D2M8K2.u11765 from rfl, allE_node, arows11758, irow11766, arows11765]
  all_goals rfl

theorem atot11766 : totK PD2M8K2 D2M8K2.u11766 = [0, 1662642105692, 5875170619271, 5629227228235, 1334797483365, 58692360374, 0, 0] := by
  rw [show D2M8K2.u11766 = KTree.node D2M8K2.u11758 (nat_lit 25182967) (nat_lit 1136478385) (nat_lit 0) D2M8K2.u11765 from rfl, totK_node, atot11758, atot11765]
  decide +kernel

theorem arows11786 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11786 = true := by
  rw [show D2M8K2.u11786 = KTree.node D2M8K2.u11778 (nat_lit 25219078) (nat_lit 3793759291) (nat_lit 0) D2M8K2.u11785 from rfl, allE_node, arows11778, irow11786, arows11785]
  all_goals rfl

theorem atot11786 : totK PD2M8K2 D2M8K2.u11786 = [0, 1575881468494, 5727140609430, 5703106637101, 1365054724731, 56264283086, 0, 0] := by
  rw [show D2M8K2.u11786 = KTree.node D2M8K2.u11778 (nat_lit 25219078) (nat_lit 3793759291) (nat_lit 0) D2M8K2.u11785 from rfl, totK_node, atot11778, atot11785]
  decide +kernel

theorem arows11801 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11801 = true := by
  rw [show D2M8K2.u11801 = KTree.node D2M8K2.u11793 (nat_lit 25235728) (nat_lit 3391614249) (nat_lit 0) D2M8K2.u11800 from rfl, allE_node, arows11793, irow11801, arows11800]
  all_goals rfl

theorem atot11801 : totK PD2M8K2 D2M8K2.u11801 = [0, 821872840808, 4185320976927, 6360044347780, 2627947597714, 211991917808, 1206465782, 0] := by
  rw [show D2M8K2.u11801 = KTree.node D2M8K2.u11793 (nat_lit 25235728) (nat_lit 3391614249) (nat_lit 0) D2M8K2.u11800 from rfl, totK_node, atot11793, atot11800]
  decide +kernel

theorem arows11817 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11817 = true := by
  rw [show D2M8K2.u11817 = KTree.node D2M8K2.u11809 (nat_lit 25298635) (nat_lit 906574878) (nat_lit 0) D2M8K2.u11816 from rfl, allE_node, arows11809, irow11817, arows11816]
  all_goals rfl

theorem atot11817 : totK PD2M8K2 D2M8K2.u11817 = [0, 995908216475, 4173999554032, 5670532745544, 2841424686748, 478057087410, 17590593026, 0] := by
  rw [show D2M8K2.u11817 = KTree.node D2M8K2.u11809 (nat_lit 25298635) (nat_lit 906574878) (nat_lit 0) D2M8K2.u11816 from rfl, totK_node, atot11809, atot11816]
  decide +kernel

theorem arows11832 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11832 = true := by
  rw [show D2M8K2.u11832 = KTree.node D2M8K2.u11824 (nat_lit 25312709) (nat_lit 2070717969) (nat_lit 0) D2M8K2.u11831 from rfl, allE_node, arows11824, irow11832, arows11831]
  all_goals rfl

theorem atot11832 : totK PD2M8K2 D2M8K2.u11832 = [0, 1033576775427, 4792867419120, 6272153169933, 2035904626208, 124942766136, 1103454931, 0] := by
  rw [show D2M8K2.u11832 = KTree.node D2M8K2.u11824 (nat_lit 25312709) (nat_lit 2070717969) (nat_lit 0) D2M8K2.u11831 from rfl, totK_node, atot11824, atot11831]
  decide +kernel

theorem arows11849 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11849 = true := by
  rw [show D2M8K2.u11849 = KTree.node D2M8K2.u11841 (nat_lit 25340597) (nat_lit 2363340291) (nat_lit 0) D2M8K2.u11848 from rfl, allE_node, arows11841, irow11849, arows11848]
  all_goals rfl

theorem atot11849 : totK PD2M8K2 D2M8K2.u11849 = [0, 1066796385368, 4527220073851, 5984991341624, 2415051791255, 238423794339, 4779662215, 0] := by
  rw [show D2M8K2.u11849 = KTree.node D2M8K2.u11841 (nat_lit 25340597) (nat_lit 2363340291) (nat_lit 0) D2M8K2.u11848 from rfl, totK_node, atot11841, atot11848]
  decide +kernel

theorem arows11864 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11864 = true := by
  rw [show D2M8K2.u11864 = KTree.node D2M8K2.u11856 (nat_lit 25381754) (nat_lit 3431825529) (nat_lit 0) D2M8K2.u11863 from rfl, allE_node, arows11856, irow11864, arows11863]
  all_goals rfl

theorem atot11864 : totK PD2M8K2 D2M8K2.u11864 = [1107237586083, 4135083450127, 5257952718460, 3147871261776, 705283726558, 31566124419, 0, 0] := by
  rw [show D2M8K2.u11864 = KTree.node D2M8K2.u11856 (nat_lit 25381754) (nat_lit 3431825529) (nat_lit 0) D2M8K2.u11863 from rfl, totK_node, atot11856, atot11863]
  decide +kernel

theorem arows11880 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11880 = true := by
  rw [show D2M8K2.u11880 = KTree.node D2M8K2.u11872 (nat_lit 25399667) (nat_lit 2907377834) (nat_lit 0) D2M8K2.u11879 from rfl, allE_node, arows11872, irow11880, arows11879]
  all_goals rfl

theorem atot11880 : totK PD2M8K2 D2M8K2.u11880 = [868734085926, 4293040540966, 6263387701391, 2543087434861, 227186564750, 1369150432, 0, 0] := by
  rw [show D2M8K2.u11880 = KTree.node D2M8K2.u11872 (nat_lit 25399667) (nat_lit 2907377834) (nat_lit 0) D2M8K2.u11879 from rfl, totK_node, atot11872, atot11879]
  decide +kernel

theorem arows11895 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11895 = true := by
  rw [show D2M8K2.u11895 = KTree.node D2M8K2.u11887 (nat_lit 25427029) (nat_lit 1190366505) (nat_lit 0) D2M8K2.u11894 from rfl, allE_node, arows11887, irow11895, arows11894]
  all_goals rfl

theorem atot11895 : totK PD2M8K2 D2M8K2.u11895 = [1097924280505, 4646608616865, 6271677883798, 2360512318448, 127963526295, 0, 0, 0] := by
  rw [show D2M8K2.u11895 = KTree.node D2M8K2.u11887 (nat_lit 25427029) (nat_lit 1190366505) (nat_lit 0) D2M8K2.u11894 from rfl, totK_node, atot11887, atot11894]
  decide +kernel

theorem arows11913 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11913 = true := by
  rw [show D2M8K2.u11913 = KTree.node D2M8K2.u11905 (nat_lit 25440723) (nat_lit 2552012328) (nat_lit 0) D2M8K2.u11912 from rfl, allE_node, arows11905, irow11913, arows11912]
  all_goals rfl

theorem atot11913 : totK PD2M8K2 D2M8K2.u11913 = [902617039367, 4226201660995, 5830105359566, 2874741363246, 637807361933, 36921873854, 0, 0] := by
  rw [show D2M8K2.u11913 = KTree.node D2M8K2.u11905 (nat_lit 25440723) (nat_lit 2552012328) (nat_lit 0) D2M8K2.u11912 from rfl, totK_node, atot11905, atot11912]
  decide +kernel

theorem arows11928 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11928 = true := by
  rw [show D2M8K2.u11928 = KTree.node D2M8K2.u11920 (nat_lit 25457976) (nat_lit 3282481759) (nat_lit 0) D2M8K2.u11927 from rfl, allE_node, arows11920, irow11928, arows11927]
  all_goals rfl

theorem atot11928 : totK PD2M8K2 D2M8K2.u11928 = [413264604107, 2418376000185, 5661410752191, 4957371360208, 959628990746, 21096254089, 0, 0] := by
  rw [show D2M8K2.u11928 = KTree.node D2M8K2.u11920 (nat_lit 25457976) (nat_lit 3282481759) (nat_lit 0) D2M8K2.u11927 from rfl, totK_node, atot11920, atot11927]
  decide +kernel

theorem arows11944 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11944 = true := by
  rw [show D2M8K2.u11944 = KTree.node D2M8K2.u11936 (nat_lit 25517000) (nat_lit 3744693544) (nat_lit 0) D2M8K2.u11943 from rfl, allE_node, arows11936, irow11944, arows11943]
  all_goals rfl

theorem atot11944 : totK PD2M8K2 D2M8K2.u11944 = [1602519801222, 5764375872037, 5709063938291, 1366783817456, 56992249974, 0, 0, 0] := by
  rw [show D2M8K2.u11944 = KTree.node D2M8K2.u11936 (nat_lit 25517000) (nat_lit 3744693544) (nat_lit 0) D2M8K2.u11943 from rfl, totK_node, atot11936, atot11943]
  decide +kernel

theorem arows11959 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11959 = true := by
  rw [show D2M8K2.u11959 = KTree.node D2M8K2.u11951 (nat_lit 25530923) (nat_lit 2919674126) (nat_lit 0) D2M8K2.u11958 from rfl, allE_node, arows11951, irow11959, arows11958]
  all_goals rfl

theorem atot11959 : totK PD2M8K2 D2M8K2.u11959 = [91570829045, 2384846158992, 6607237785692, 4517520211296, 616472842906, 15398727635, 0, 0] := by
  rw [show D2M8K2.u11959 = KTree.node D2M8K2.u11951 (nat_lit 25530923) (nat_lit 2919674126) (nat_lit 0) D2M8K2.u11958 from rfl, totK_node, atot11951, atot11958]
  decide +kernel

theorem arows11976 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11976 = true := by
  rw [show D2M8K2.u11976 = KTree.node D2M8K2.u11968 (nat_lit 25551438) (nat_lit 3996945471) (nat_lit 0) D2M8K2.u11975 from rfl, allE_node, arows11968, irow11976, arows11975]
  all_goals rfl

theorem atot11976 : totK PD2M8K2 D2M8K2.u11976 = [1477634143990, 5295664825391, 5604822834745, 1865740921592, 170705391719, 3667207281, 0, 0] := by
  rw [show D2M8K2.u11976 = KTree.node D2M8K2.u11968 (nat_lit 25551438) (nat_lit 3996945471) (nat_lit 0) D2M8K2.u11975 from rfl, totK_node, atot11968, atot11975]
  decide +kernel

theorem arows11991 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u11991 = true := by
  rw [show D2M8K2.u11991 = KTree.node D2M8K2.u11983 (nat_lit 25568641) (nat_lit 1560988708) (nat_lit 0) D2M8K2.u11990 from rfl, allE_node, arows11983, irow11991, arows11990]
  all_goals rfl

theorem atot11991 : totK PD2M8K2 D2M8K2.u11991 = [552723083876, 3844583753742, 6776571190443, 2977238082896, 222413280583, 1138244013, 0, 0] := by
  rw [show D2M8K2.u11991 = KTree.node D2M8K2.u11983 (nat_lit 25568641) (nat_lit 1560988708) (nat_lit 0) D2M8K2.u11990 from rfl, totK_node, atot11983, atot11990]
  decide +kernel

theorem arows12007 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12007 = true := by
  rw [show D2M8K2.u12007 = KTree.node D2M8K2.u11999 (nat_lit 25592037) (nat_lit 1333830147) (nat_lit 0) D2M8K2.u12006 from rfl, allE_node, arows11999, irow12007, arows12006]
  all_goals rfl

theorem atot12007 : totK PD2M8K2 D2M8K2.u12007 = [1230295041496, 4752416456173, 5752142622670, 2387114279665, 277144897399, 4977114383, 0, 0] := by
  rw [show D2M8K2.u12007 = KTree.node D2M8K2.u11999 (nat_lit 25592037) (nat_lit 1333830147) (nat_lit 0) D2M8K2.u12006 from rfl, totK_node, atot11999, atot12006]
  decide +kernel

theorem arows12022 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12022 = true := by
  rw [show D2M8K2.u12022 = KTree.node D2M8K2.u12014 (nat_lit 25611688) (nat_lit 2730668811) (nat_lit 0) D2M8K2.u12021 from rfl, allE_node, arows12014, irow12022, arows12021]
  all_goals rfl

theorem atot12022 : totK PD2M8K2 D2M8K2.u12022 = [428021878965, 3161111938436, 6469456112124, 3867571465294, 445490839001, 6241690223, 0, 0] := by
  rw [show D2M8K2.u12022 = KTree.node D2M8K2.u12014 (nat_lit 25611688) (nat_lit 2730668811) (nat_lit 0) D2M8K2.u12021 from rfl, totK_node, atot12014, atot12021]
  decide +kernel

theorem arows12041 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12041 = true := by
  rw [show D2M8K2.u12041 = KTree.node D2M8K2.u12033 (nat_lit 25637960) (nat_lit 3780826017) (nat_lit 0) D2M8K2.u12040 from rfl, allE_node, arows12033, irow12041, arows12040]
  all_goals rfl

theorem atot12041 : totK PD2M8K2 D2M8K2.u12041 = [0, 1739697136867, 6060238230259, 5387575750730, 1050491526367, 37474636626, 0, 0] := by
  rw [show D2M8K2.u12041 = KTree.node D2M8K2.u12033 (nat_lit 25637960) (nat_lit 3780826017) (nat_lit 0) D2M8K2.u12040 from rfl, totK_node, atot12033, atot12040]
  decide +kernel

theorem arows12056 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12056 = true := by
  rw [show D2M8K2.u12056 = KTree.node D2M8K2.u12048 (nat_lit 25652326) (nat_lit 2331750345) (nat_lit 0) D2M8K2.u12055 from rfl, allE_node, arows12048, irow12056, arows12055]
  all_goals rfl

theorem atot12056 : totK PD2M8K2 D2M8K2.u12056 = [0, 382749107306, 3631563729186, 7026511351353, 2826954071779, 189488999057, 1310517177, 0] := by
  rw [show D2M8K2.u12056 = KTree.node D2M8K2.u12048 (nat_lit 25652326) (nat_lit 2331750345) (nat_lit 0) D2M8K2.u12055 from rfl, totK_node, atot12048, atot12055]
  decide +kernel

theorem arows12072 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12072 = true := by
  rw [show D2M8K2.u12072 = KTree.node D2M8K2.u12064 (nat_lit 25681010) (nat_lit 4011908747) (nat_lit 0) D2M8K2.u12071 from rfl, allE_node, arows12064, irow12072, arows12071]
  all_goals rfl

theorem atot12072 : totK PD2M8K2 D2M8K2.u12072 = [0, 1611092455192, 5765634254989, 5688636166877, 1423330591614, 64916807208, 0, 0] := by
  rw [show D2M8K2.u12072 = KTree.node D2M8K2.u12064 (nat_lit 25681010) (nat_lit 4011908747) (nat_lit 0) D2M8K2.u12071 from rfl, totK_node, atot12064, atot12071]
  decide +kernel

theorem arows12087 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12087 = true := by
  rw [show D2M8K2.u12087 = KTree.node D2M8K2.u12079 (nat_lit 25757372) (nat_lit 2579146057) (nat_lit 0) D2M8K2.u12086 from rfl, allE_node, arows12079, irow12087, arows12086]
  all_goals rfl

theorem atot12087 : totK PD2M8K2 D2M8K2.u12087 = [0, 1667274022264, 5776737361535, 5569001143258, 1356002456143, 54425607585, 0, 0] := by
  rw [show D2M8K2.u12087 = KTree.node D2M8K2.u12079 (nat_lit 25757372) (nat_lit 2579146057) (nat_lit 0) D2M8K2.u12086 from rfl, totK_node, atot12079, atot12086]
  decide +kernel

theorem arows12104 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12104 = true := by
  rw [show D2M8K2.u12104 = KTree.node D2M8K2.u12096 (nat_lit 25773828) (nat_lit 3199373178) (nat_lit 0) D2M8K2.u12103 from rfl, allE_node, arows12096, irow12104, arows12103]
  all_goals rfl

theorem atot12104 : totK PD2M8K2 D2M8K2.u12104 = [0, 822030395565, 4218247684405, 6370738964317, 2589933022782, 208343219073, 1217496766, 0] := by
  rw [show D2M8K2.u12104 = KTree.node D2M8K2.u12096 (nat_lit 25773828) (nat_lit 3199373178) (nat_lit 0) D2M8K2.u12103 from rfl, totK_node, atot12096, atot12103]
  decide +kernel

theorem arows12119 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12119 = true := by
  rw [show D2M8K2.u12119 = KTree.node D2M8K2.u12111 (nat_lit 25793595) (nat_lit 3755335418) (nat_lit 0) D2M8K2.u12118 from rfl, allE_node, arows12111, irow12119, arows12118]
  all_goals rfl

theorem atot12119 : totK PD2M8K2 D2M8K2.u12119 = [0, 824634681466, 3845510491237, 5865413576266, 3131108095399, 504115774420, 17736366219, 0] := by
  rw [show D2M8K2.u12119 = KTree.node D2M8K2.u12111 (nat_lit 25793595) (nat_lit 3755335418) (nat_lit 0) D2M8K2.u12118 from rfl, totK_node, atot12111, atot12118]
  decide +kernel

theorem arows12135 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12135 = true := by
  rw [show D2M8K2.u12135 = KTree.node D2M8K2.u12127 (nat_lit 25809725) (nat_lit 2292550597) (nat_lit 0) D2M8K2.u12134 from rfl, allE_node, arows12127, irow12135, arows12134]
  all_goals rfl

theorem atot12135 : totK PD2M8K2 D2M8K2.u12135 = [0, 1206587746932, 4993049340694, 6019060542396, 1932631605557, 125057477178, 1138244013, 0] := by
  rw [show D2M8K2.u12135 = KTree.node D2M8K2.u12127 (nat_lit 25809725) (nat_lit 2292550597) (nat_lit 0) D2M8K2.u12134 from rfl, totK_node, atot12127, atot12134]
  decide +kernel

theorem arows12150 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12150 = true := by
  rw [show D2M8K2.u12150 = KTree.node D2M8K2.u12142 (nat_lit 25833196) (nat_lit 2622740099) (nat_lit 0) D2M8K2.u12149 from rfl, allE_node, arows12142, irow12150, arows12149]
  all_goals rfl

theorem atot12150 : totK PD2M8K2 D2M8K2.u12150 = [0, 803610989290, 4195756407255, 6334164164232, 2626966372356, 246888719624, 4914284239, 0] := by
  rw [show D2M8K2.u12150 = KTree.node D2M8K2.u12142 (nat_lit 25833196) (nat_lit 2622740099) (nat_lit 0) D2M8K2.u12149 from rfl, totK_node, atot12142, atot12149]
  decide +kernel

theorem arows12168 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12168 = true := by
  rw [show D2M8K2.u12168 = KTree.node D2M8K2.u12160 (nat_lit 25857059) (nat_lit 2964126074) (nat_lit 0) D2M8K2.u12167 from rfl, allE_node, arows12160, irow12168, arows12167]
  all_goals rfl

theorem atot12168 : totK PD2M8K2 D2M8K2.u12168 = [845908722094, 3702956481287, 5454916663886, 3507848780689, 850793049872, 40784780176, 0, 0] := by
  rw [show D2M8K2.u12168 = KTree.node D2M8K2.u12160 (nat_lit 25857059) (nat_lit 2964126074) (nat_lit 0) D2M8K2.u12167 from rfl, totK_node, atot12160, atot12167]
  decide +kernel

theorem arows12183 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12183 = true := by
  rw [show D2M8K2.u12183 = KTree.node D2M8K2.u12175 (nat_lit 25894977) (nat_lit 1817585069) (nat_lit 0) D2M8K2.u12182 from rfl, allE_node, arows12175, irow12183, arows12182]
  all_goals rfl

theorem atot12183 : totK PD2M8K2 D2M8K2.u12183 = [1158032202015, 4720469405101, 5897641415235, 2226293938800, 208227527301, 1369150432, 0, 0] := by
  rw [show D2M8K2.u12183 = KTree.node D2M8K2.u12175 (nat_lit 25894977) (nat_lit 1817585069) (nat_lit 0) D2M8K2.u12182 from rfl, totK_node, atot12175, atot12182]
  decide +kernel

theorem arows12199 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12199 = true := by
  rw [show D2M8K2.u12199 = KTree.node D2M8K2.u12191 (nat_lit 25918045) (nat_lit 1202266592) (nat_lit 0) D2M8K2.u12198 from rfl, allE_node, arows12191, irow12199, arows12198]
  all_goals rfl

theorem atot12199 : totK PD2M8K2 D2M8K2.u12199 = [857647101323, 4303673832837, 6529913591119, 2599544784825, 138171925814, 0, 0, 0] := by
  rw [show D2M8K2.u12199 = KTree.node D2M8K2.u12191 (nat_lit 25918045) (nat_lit 1202266592) (nat_lit 0) D2M8K2.u12198 from rfl, totK_node, atot12191, atot12198]
  decide +kernel

theorem arows12214 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12214 = true := by
  rw [show D2M8K2.u12214 = KTree.node D2M8K2.u12206 (nat_lit 25935776) (nat_lit 3568131126) (nat_lit 0) D2M8K2.u12213 from rfl, allE_node, arows12206, irow12214, arows12213]
  all_goals rfl

theorem atot12214 : totK PD2M8K2 D2M8K2.u12214 = [1169267471077, 4893165832783, 6018895355737, 2148916969810, 279381010545, 21385604922, 0, 0] := by
  rw [show D2M8K2.u12214 = KTree.node D2M8K2.u12206 (nat_lit 25935776) (nat_lit 3568131126) (nat_lit 0) D2M8K2.u12213 from rfl, totK_node, atot12206, atot12213]
  decide +kernel

theorem arows12231 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12231 = true := by
  rw [show D2M8K2.u12231 = KTree.node D2M8K2.u12223 (nat_lit 25953218) (nat_lit 4098011033) (nat_lit 0) D2M8K2.u12230 from rfl, allE_node, arows12223, irow12231, arows12230]
  all_goals rfl

theorem atot12231 : totK PD2M8K2 D2M8K2.u12231 = [0, 1578656351076, 5815085458781, 5779641630945, 1235993619609, 29814231179, 0, 0] := by
  rw [show D2M8K2.u12231 = KTree.node D2M8K2.u12223 (nat_lit 25953218) (nat_lit 4098011033) (nat_lit 0) D2M8K2.u12230 from rfl, totK_node, atot12223, atot12230]
  decide +kernel

theorem arows12246 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12246 = true := by
  rw [show D2M8K2.u12246 = KTree.node D2M8K2.u12238 (nat_lit 25967959) (nat_lit 1087780773) (nat_lit 0) D2M8K2.u12245 from rfl, allE_node, arows12238, irow12246, arows12245]
  all_goals rfl

theorem atot12246 : totK PD2M8K2 D2M8K2.u12246 = [1689069297834, 5800193486554, 5427147264128, 1387285457682, 145079137852, 6818291842, 0, 0] := by
  rw [show D2M8K2.u12246 = KTree.node D2M8K2.u12238 (nat_lit 25967959) (nat_lit 1087780773) (nat_lit 0) D2M8K2.u12245 from rfl, totK_node, atot12238, atot12245]
  decide +kernel

theorem arows12262 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12262 = true := by
  rw [show D2M8K2.u12262 = KTree.node D2M8K2.u12254 (nat_lit 25986153) (nat_lit 1794225861) (nat_lit 0) D2M8K2.u12261 from rfl, allE_node, arows12254, irow12262, arows12261]
  all_goals rfl

theorem atot12262 : totK PD2M8K2 D2M8K2.u12262 = [326127760768, 2985590093640, 6538619554316, 3889371411324, 518506512853, 14222663156, 0, 0] := by
  rw [show D2M8K2.u12262 = KTree.node D2M8K2.u12254 (nat_lit 25986153) (nat_lit 1794225861) (nat_lit 0) D2M8K2.u12261 from rfl, totK_node, atot12254, atot12261]
  decide +kernel

theorem arows12277 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12277 = true := by
  rw [show D2M8K2.u12277 = KTree.node D2M8K2.u12269 (nat_lit 26007093) (nat_lit 1725726711) (nat_lit 0) D2M8K2.u12276 from rfl, allE_node, arows12269, irow12277, arows12276]
  all_goals rfl

theorem atot12277 : totK PD2M8K2 D2M8K2.u12277 = [1264545748194, 4821382578241, 5731698577865, 2311648153993, 242203429950, 4574395652, 0, 0] := by
  rw [show D2M8K2.u12277 = KTree.node D2M8K2.u12269 (nat_lit 26007093) (nat_lit 1725726711) (nat_lit 0) D2M8K2.u12276 from rfl, totK_node, atot12269, atot12276]
  decide +kernel

theorem arows12300 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12300 = true := by
  rw [show D2M8K2.u12300 = KTree.node D2M8K2.u12292 (nat_lit 26024308) (nat_lit 4029359719) (nat_lit 0) D2M8K2.u12299 from rfl, allE_node, arows12292, irow12300, arows12299]
  all_goals rfl

theorem atot12300 : totK PD2M8K2 D2M8K2.u12300 = [751134355286, 3975679287888, 6374359166169, 2997059857244, 272978150990, 2410950632, 0, 0] := by
  rw [show D2M8K2.u12300 = KTree.node D2M8K2.u12292 (nat_lit 26024308) (nat_lit 4029359719) (nat_lit 0) D2M8K2.u12299 from rfl, totK_node, atot12292, atot12299]
  decide +kernel

theorem arows12315 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12315 = true := by
  rw [show D2M8K2.u12315 = KTree.node D2M8K2.u12307 (nat_lit 26045286) (nat_lit 3866735348) (nat_lit 0) D2M8K2.u12314 from rfl, allE_node, arows12307, irow12315, arows12314]
  all_goals rfl

theorem atot12315 : totK PD2M8K2 D2M8K2.u12315 = [969118401780, 4015992816255, 5696047337409, 3154796886486, 497466604798, 16654984284, 0, 0] := by
  rw [show D2M8K2.u12315 = KTree.node D2M8K2.u12307 (nat_lit 26045286) (nat_lit 3866735348) (nat_lit 0) D2M8K2.u12314 from rfl, totK_node, atot12307, atot12314]
  decide +kernel

theorem arows12331 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12331 = true := by
  rw [show D2M8K2.u12331 = KTree.node D2M8K2.u12323 (nat_lit 26058379) (nat_lit 1582372634) (nat_lit 0) D2M8K2.u12330 from rfl, allE_node, arows12323, irow12331, arows12330]
  all_goals rfl

theorem atot12331 : totK PD2M8K2 D2M8K2.u12331 = [1160434894226, 4868286615952, 6062796387725, 2125631486343, 164303560963, 1138244013, 0, 0] := by
  rw [show D2M8K2.u12331 = KTree.node D2M8K2.u12323 (nat_lit 26058379) (nat_lit 1582372634) (nat_lit 0) D2M8K2.u12330 from rfl, totK_node, atot12323, atot12330]
  decide +kernel

theorem arows12346 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12346 = true := by
  rw [show D2M8K2.u12346 = KTree.node D2M8K2.u12338 (nat_lit 26080144) (nat_lit 3315343775) (nat_lit 0) D2M8K2.u12345 from rfl, allE_node, arows12338, irow12346, arows12345]
  all_goals rfl

theorem atot12346 : totK PD2M8K2 D2M8K2.u12346 = [0, 2380503445112, 6982197856533, 4476369495693, 506016655808, 6346264815, 0, 0] := by
  rw [show D2M8K2.u12346 = KTree.node D2M8K2.u12338 (nat_lit 26080144) (nat_lit 3315343775) (nat_lit 0) D2M8K2.u12345 from rfl, totK_node, atot12338, atot12345]
  decide +kernel

theorem arows12363 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12363 = true := by
  rw [show D2M8K2.u12363 = KTree.node D2M8K2.u12355 (nat_lit 26142492) (nat_lit 3076423465) (nat_lit 0) D2M8K2.u12362 from rfl, allE_node, arows12355, irow12363, arows12362]
  all_goals rfl

theorem atot12363 : totK PD2M8K2 D2M8K2.u12363 = [0, 1153396545534, 4932533095020, 6041075994053, 1863017474104, 141940332389, 1209030869, 0] := by
  rw [show D2M8K2.u12363 = KTree.node D2M8K2.u12355 (nat_lit 26142492) (nat_lit 3076423465) (nat_lit 0) D2M8K2.u12362 from rfl, totK_node, atot12355, atot12362]
  decide +kernel

theorem arows12378 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12378 = true := by
  rw [show D2M8K2.u12378 = KTree.node D2M8K2.u12370 (nat_lit 26173160) (nat_lit 3473373853) (nat_lit 0) D2M8K2.u12377 from rfl, allE_node, arows12370, irow12378, arows12377]
  all_goals rfl

theorem atot12378 : totK PD2M8K2 D2M8K2.u12378 = [0, 922947936326, 4748028011111, 6527591201545, 2061922436861, 101230398143, 0, 0] := by
  rw [show D2M8K2.u12378 = KTree.node D2M8K2.u12370 (nat_lit 26173160) (nat_lit 3473373853) (nat_lit 0) D2M8K2.u12377 from rfl, totK_node, atot12370, atot12377]
  decide +kernel

theorem arows12394 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12394 = true := by
  rw [show D2M8K2.u12394 = KTree.node D2M8K2.u12386 (nat_lit 26186718) (nat_lit 3291842040) (nat_lit 0) D2M8K2.u12393 from rfl, allE_node, arows12386, irow12394, arows12393]
  all_goals rfl

theorem atot12394 : totK PD2M8K2 D2M8K2.u12394 = [0, 1824146698840, 6177308715705, 5467933631816, 996861681015, 26961698892, 0, 0] := by
  rw [show D2M8K2.u12394 = KTree.node D2M8K2.u12386 (nat_lit 26186718) (nat_lit 3291842040) (nat_lit 0) D2M8K2.u12393 from rfl, totK_node, atot12386, atot12393]
  decide +kernel

theorem arows12409 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12409 = true := by
  rw [show D2M8K2.u12409 = KTree.node D2M8K2.u12401 (nat_lit 26224821) (nat_lit 1736237503) (nat_lit 0) D2M8K2.u12408 from rfl, allE_node, arows12401, irow12409, arows12408]
  all_goals rfl

theorem atot12409 : totK PD2M8K2 D2M8K2.u12409 = [0, 1691249784923, 5947384997633, 5560913413220, 1177104988267, 37925126632, 0, 0] := by
  rw [show D2M8K2.u12409 = KTree.node D2M8K2.u12401 (nat_lit 26224821) (nat_lit 1736237503) (nat_lit 0) D2M8K2.u12408 from rfl, totK_node, atot12401, atot12408]
  decide +kernel

theorem arows12427 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12427 = true := by
  rw [show D2M8K2.u12427 = KTree.node D2M8K2.u12419 (nat_lit 26263822) (nat_lit 3576990185) (nat_lit 0) D2M8K2.u12426 from rfl, allE_node, arows12419, irow12427, arows12426]
  all_goals rfl

theorem atot12427 : totK PD2M8K2 D2M8K2.u12427 = [0, 1605527838359, 5891828906329, 5760189067121, 1186774047190, 35738146775, 0, 0] := by
  rw [show D2M8K2.u12427 = KTree.node D2M8K2.u12419 (nat_lit 26263822) (nat_lit 3576990185) (nat_lit 0) D2M8K2.u12426 from rfl, totK_node, atot12419, atot12426]
  decide +kernel

theorem arows12442 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12442 = true := by
  rw [show D2M8K2.u12442 = KTree.node D2M8K2.u12434 (nat_lit 26299296) (nat_lit 3539594534) (nat_lit 0) D2M8K2.u12441 from rfl, allE_node, arows12434, irow12442, arows12441]
  all_goals rfl

theorem atot12442 : totK PD2M8K2 D2M8K2.u12442 = [0, 1676694767601, 5891595211361, 5571275391313, 1177037411880, 42834225666, 0, 0] := by
  rw [show D2M8K2.u12442 = KTree.node D2M8K2.u12434 (nat_lit 26299296) (nat_lit 3539594534) (nat_lit 0) D2M8K2.u12441 from rfl, totK_node, atot12434, atot12441]
  decide +kernel

theorem arows12458 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12458 = true := by
  rw [show D2M8K2.u12458 = KTree.node D2M8K2.u12450 (nat_lit 26316349) (nat_lit 1179408804) (nat_lit 0) D2M8K2.u12457 from rfl, allE_node, arows12450, irow12458, arows12457]
  all_goals rfl

theorem atot12458 : totK PD2M8K2 D2M8K2.u12458 = [0, 444116253521, 3782229813434, 6954309862857, 2817681723773, 216019481670, 1138244013, 0] := by
  rw [show D2M8K2.u12458 = KTree.node D2M8K2.u12450 (nat_lit 26316349) (nat_lit 1179408804) (nat_lit 0) D2M8K2.u12457 from rfl, totK_node, atot12450, atot12457]
  decide +kernel

theorem arows12473 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12473 = true := by
  rw [show D2M8K2.u12473 = KTree.node D2M8K2.u12465 (nat_lit 26881949) (nat_lit 2289224539) (nat_lit 0) D2M8K2.u12472 from rfl, allE_node, arows12465, irow12473, arows12472]
  all_goals rfl

theorem atot12473 : totK PD2M8K2 D2M8K2.u12473 = [0, 1517624020597, 5238298335264, 5404831591176, 1883178650415, 236171077273, 4977114383, 0] := by
  rw [show D2M8K2.u12473 = KTree.node D2M8K2.u12465 (nat_lit 26881949) (nat_lit 2289224539) (nat_lit 0) D2M8K2.u12472 from rfl, totK_node, atot12465, atot12472]
  decide +kernel

theorem arows12490 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12490 = true := by
  rw [show D2M8K2.u12490 = KTree.node D2M8K2.u12482 (nat_lit 26895494) (nat_lit 3161144398) (nat_lit 0) D2M8K2.u12489 from rfl, allE_node, arows12482, irow12490, arows12489]
  all_goals rfl

theorem atot12490 : totK PD2M8K2 D2M8K2.u12490 = [0, 579315562642, 3796318624862, 6638490240663, 2893919245122, 246044406266, 1369150432, 0] := by
  rw [show D2M8K2.u12490 = KTree.node D2M8K2.u12482 (nat_lit 26895494) (nat_lit 3161144398) (nat_lit 0) D2M8K2.u12489 from rfl, totK_node, atot12482, atot12489]
  decide +kernel

theorem arows12505 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12505 = true := by
  rw [show D2M8K2.u12505 = KTree.node D2M8K2.u12497 (nat_lit 26960901) (nat_lit 1505766429) (nat_lit 0) D2M8K2.u12504 from rfl, allE_node, arows12497, irow12505, arows12504]
  all_goals rfl

theorem atot12505 : totK PD2M8K2 D2M8K2.u12505 = [0, 1352442604588, 5288242509421, 5947878568953, 1718906372505, 75792261912, 0, 0] := by
  rw [show D2M8K2.u12505 = KTree.node D2M8K2.u12497 (nat_lit 26960901) (nat_lit 1505766429) (nat_lit 0) D2M8K2.u12504 from rfl, totK_node, atot12497, atot12504]
  decide +kernel

theorem arows12521 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12521 = true := by
  rw [show D2M8K2.u12521 = KTree.node D2M8K2.u12513 (nat_lit 26978550) (nat_lit 3701611869) (nat_lit 0) D2M8K2.u12520 from rfl, allE_node, arows12513, irow12521, arows12520]
  all_goals rfl

theorem atot12521 : totK PD2M8K2 D2M8K2.u12521 = [0, 630302058830, 3592663958361, 6270129832716, 3267837472503, 438001639172, 14222663156, 0] := by
  rw [show D2M8K2.u12521 = KTree.node D2M8K2.u12513 (nat_lit 26978550) (nat_lit 3701611869) (nat_lit 0) D2M8K2.u12520 from rfl, totK_node, atot12513, atot12520]
  decide +kernel

theorem arows12536 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12536 = true := by
  rw [show D2M8K2.u12536 = KTree.node D2M8K2.u12528 (nat_lit 26999907) (nat_lit 1832391924) (nat_lit 0) D2M8K2.u12535 from rfl, allE_node, arows12528, irow12536, arows12535]
  all_goals rfl

theorem atot12536 : totK PD2M8K2 D2M8K2.u12536 = [0, 1187821146392, 4699595483927, 5869433818965, 2380738511418, 224111833866, 4574395652, 0] := by
  rw [show D2M8K2.u12536 = KTree.node D2M8K2.u12528 (nat_lit 26999907) (nat_lit 1832391924) (nat_lit 0) D2M8K2.u12535 from rfl, totK_node, atot12528, atot12535]
  decide +kernel

theorem arows12555 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12555 = true := by
  rw [show D2M8K2.u12555 = KTree.node D2M8K2.u12547 (nat_lit 27017864) (nat_lit 2604830980) (nat_lit 0) D2M8K2.u12554 from rfl, allE_node, arows12547, irow12555, arows12554]
  all_goals rfl

theorem atot12555 : totK PD2M8K2 D2M8K2.u12555 = [0, 795429341796, 4222576016191, 6467428159277, 2649069367604, 198675342232, 1239866073, 0] := by
  rw [show D2M8K2.u12555 = KTree.node D2M8K2.u12547 (nat_lit 27017864) (nat_lit 2604830980) (nat_lit 0) D2M8K2.u12554 from rfl, totK_node, atot12547, atot12554]
  decide +kernel

theorem arows12570 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12570 = true := by
  rw [show D2M8K2.u12570 = KTree.node D2M8K2.u12562 (nat_lit 27037921) (nat_lit 1397980242) (nat_lit 0) D2M8K2.u12569 from rfl, allE_node, arows12562, irow12570, arows12569]
  all_goals rfl

theorem atot12570 : totK PD2M8K2 D2M8K2.u12570 = [0, 852664324323, 3812239411698, 5835580860380, 3237630736310, 495340267932, 17826068843, 0] := by
  rw [show D2M8K2.u12570 = KTree.node D2M8K2.u12562 (nat_lit 27037921) (nat_lit 1397980242) (nat_lit 0) D2M8K2.u12569 from rfl, totK_node, atot12562, atot12569]
  decide +kernel

theorem arows12586 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12586 = true := by
  rw [show D2M8K2.u12586 = KTree.node D2M8K2.u12578 (nat_lit 27053707) (nat_lit 1582372634) (nat_lit 0) D2M8K2.u12585 from rfl, allE_node, arows12578, irow12586, arows12585]
  all_goals rfl

theorem atot12586 : totK PD2M8K2 D2M8K2.u12586 = [0, 1177876207315, 4857443720821, 6033361232224, 2096018265026, 157543576728, 1138244013, 0] := by
  rw [show D2M8K2.u12586 = KTree.node D2M8K2.u12578 (nat_lit 27053707) (nat_lit 1582372634) (nat_lit 0) D2M8K2.u12585 from rfl, totK_node, atot12578, atot12585]
  decide +kernel

theorem arows12601 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12601 = true := by
  rw [show D2M8K2.u12601 = KTree.node D2M8K2.u12593 (nat_lit 27076125) (nat_lit 1555880650) (nat_lit 0) D2M8K2.u12600 from rfl, allE_node, arows12593, irow12601, arows12600]
  all_goals rfl

theorem atot12601 : totK PD2M8K2 D2M8K2.u12601 = [0, 822629260889, 4100843517003, 6252115489665, 2812047320180, 299211824845, 4977114383, 0] := by
  rw [show D2M8K2.u12601 = KTree.node D2M8K2.u12593 (nat_lit 27076125) (nat_lit 1555880650) (nat_lit 0) D2M8K2.u12600 from rfl, totK_node, atot12593, atot12600]
  decide +kernel

theorem arows12618 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12618 = true := by
  rw [show D2M8K2.u12618 = KTree.node D2M8K2.u12610 (nat_lit 27100926) (nat_lit 3264598146) (nat_lit 0) D2M8K2.u12617 from rfl, allE_node, arows12610, irow12618, arows12617]
  all_goals rfl

theorem atot12618 : totK PD2M8K2 D2M8K2.u12618 = [0, 829385582427, 4256810548225, 6430974262350, 2608676572975, 189327751019, 1310285577, 0] := by
  rw [show D2M8K2.u12618 = KTree.node D2M8K2.u12610 (nat_lit 27100926) (nat_lit 3264598146) (nat_lit 0) D2M8K2.u12617 from rfl, totK_node, atot12610, atot12617]
  decide +kernel

theorem arows12633 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12633 = true := by
  rw [show D2M8K2.u12633 = KTree.node D2M8K2.u12625 (nat_lit 27130208) (nat_lit 3695991641) (nat_lit 0) D2M8K2.u12632 from rfl, allE_node, arows12625, irow12633, arows12632]
  all_goals rfl

theorem atot12633 : totK PD2M8K2 D2M8K2.u12633 = [0, 0, 2059835872351, 6427610875174, 4904813273660, 769093717683, 27353188246, 0] := by
  rw [show D2M8K2.u12633 = KTree.node D2M8K2.u12625 (nat_lit 27130208) (nat_lit 3695991641) (nat_lit 0) D2M8K2.u12632 from rfl, totK_node, atot12625, atot12632]
  decide +kernel

theorem arows12649 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12649 = true := by
  rw [show D2M8K2.u12649 = KTree.node D2M8K2.u12641 (nat_lit 27144955) (nat_lit 2207755931) (nat_lit 0) D2M8K2.u12648 from rfl, allE_node, arows12641, irow12649, arows12648]
  all_goals rfl

theorem atot12649 : totK PD2M8K2 D2M8K2.u12649 = [0, 0, 581144831316, 4290245172364, 6745763226902, 2272305743725, 167598193917, 1369150432] := by
  rw [show D2M8K2.u12649 = KTree.node D2M8K2.u12641 (nat_lit 27144955) (nat_lit 2207755931) (nat_lit 0) D2M8K2.u12648 from rfl, totK_node, atot12641, atot12648]
  decide +kernel

theorem arows12664 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12664 = true := by
  rw [show D2M8K2.u12664 = KTree.node D2M8K2.u12656 (nat_lit 27214353) (nat_lit 1698264991) (nat_lit 0) D2M8K2.u12663 from rfl, allE_node, arows12656, irow12664, arows12663]
  all_goals rfl

theorem atot12664 : totK PD2M8K2 D2M8K2.u12664 = [0, 0, 2126883800886, 6534227431724, 4903179431533, 726961203714, 19336147013, 0] := by
  rw [show D2M8K2.u12664 = KTree.node D2M8K2.u12656 (nat_lit 27214353) (nat_lit 1698264991) (nat_lit 0) D2M8K2.u12663 from rfl, totK_node, atot12656, atot12663]
  decide +kernel

theorem arows12682 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12682 = true := by
  rw [show D2M8K2.u12682 = KTree.node D2M8K2.u12674 (nat_lit 27260215) (nat_lit 2341639094) (nat_lit 0) D2M8K2.u12681 from rfl, allE_node, arows12674, irow12682, arows12681]
  all_goals rfl

theorem atot12682 : totK PD2M8K2 D2M8K2.u12682 = [0, 0, 2101878122817, 6517728090292, 4967257656669, 736497010239, 19457511165, 0] := by
  rw [show D2M8K2.u12682 = KTree.node D2M8K2.u12674 (nat_lit 27260215) (nat_lit 2341639094) (nat_lit 0) D2M8K2.u12681 from rfl, totK_node, atot12674, atot12681]
  decide +kernel

theorem arows12697 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12697 = true := by
  rw [show D2M8K2.u12697 = KTree.node D2M8K2.u12689 (nat_lit 27297802) (nat_lit 3766697694) (nat_lit 0) D2M8K2.u12696 from rfl, allE_node, arows12689, irow12697, arows12696]
  all_goals rfl

theorem atot12697 : totK PD2M8K2 D2M8K2.u12697 = [0, 0, 1716073696830, 6087771446271, 5479979741548, 952303187216, 30042983545, 0] := by
  rw [show D2M8K2.u12697 = KTree.node D2M8K2.u12689 (nat_lit 27297802) (nat_lit 3766697694) (nat_lit 0) D2M8K2.u12696 from rfl, totK_node, atot12689, atot12696]
  decide +kernel

theorem arows12713 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12713 = true := by
  rw [show D2M8K2.u12713 = KTree.node D2M8K2.u12705 (nat_lit 27341856) (nat_lit 3694794597) (nat_lit 0) D2M8K2.u12712 from rfl, allE_node, arows12705, irow12713, arows12712]
  all_goals rfl

theorem atot12713 : totK PD2M8K2 D2M8K2.u12713 = [0, 515225544756, 3405538500686, 6484730603899, 3661701816160, 397811540467, 5253160287, 0] := by
  rw [show D2M8K2.u12713 = KTree.node D2M8K2.u12705 (nat_lit 27341856) (nat_lit 3694794597) (nat_lit 0) D2M8K2.u12712 from rfl, totK_node, atot12705, atot12712]
  decide +kernel

theorem arows12728 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12728 = true := by
  rw [show D2M8K2.u12728 = KTree.node D2M8K2.u12720 (nat_lit 27426876) (nat_lit 3022000128) (nat_lit 0) D2M8K2.u12727 from rfl, allE_node, arows12720, irow12728, arows12727]
  all_goals rfl

theorem atot12728 : totK PD2M8K2 D2M8K2.u12728 = [0, 1602517526026, 5773954891680, 5739198896085, 1272298530119, 37187387253, 0, 0] := by
  rw [show D2M8K2.u12728 = KTree.node D2M8K2.u12720 (nat_lit 27426876) (nat_lit 3022000128) (nat_lit 0) D2M8K2.u12727 from rfl, totK_node, atot12720, atot12727]
  decide +kernel

theorem arows12745 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12745 = true := by
  rw [show D2M8K2.u12745 = KTree.node D2M8K2.u12737 (nat_lit 27443188) (nat_lit 3769913827) (nat_lit 0) D2M8K2.u12744 from rfl, allE_node, arows12737, irow12745, arows12744]
  all_goals rfl

theorem atot12745 : totK PD2M8K2 D2M8K2.u12745 = [0, 0, 1703847411936, 6003086245182, 5543349977826, 1186216134773, 47300615174, 0] := by
  rw [show D2M8K2.u12745 = KTree.node D2M8K2.u12737 (nat_lit 27443188) (nat_lit 3769913827) (nat_lit 0) D2M8K2.u12744 from rfl, totK_node, atot12737, atot12744]
  decide +kernel

theorem arows12760 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12760 = true := by
  rw [show D2M8K2.u12760 = KTree.node D2M8K2.u12752 (nat_lit 27458756) (nat_lit 3270063782) (nat_lit 0) D2M8K2.u12759 from rfl, allE_node, arows12752, irow12760, arows12759]
  all_goals rfl

theorem atot12760 : totK PD2M8K2 D2M8K2.u12760 = [0, 1192307120528, 4639396084570, 5634551750691, 2573519312976, 415190786896, 10717512769, 0] := by
  rw [show D2M8K2.u12760 = KTree.node D2M8K2.u12752 (nat_lit 27458756) (nat_lit 3270063782) (nat_lit 0) D2M8K2.u12759 from rfl, totK_node, atot12752, atot12759]
  decide +kernel

theorem arows12776 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12776 = true := by
  rw [show D2M8K2.u12776 = KTree.node D2M8K2.u12768 (nat_lit 27475279) (nat_lit 2389817115) (nat_lit 0) D2M8K2.u12775 from rfl, allE_node, arows12768, irow12776, arows12775]
  all_goals rfl

theorem atot12776 : totK PD2M8K2 D2M8K2.u12776 = [0, 800359954272, 4032953746508, 6212490364587, 2922632042589, 385749030861, 13016197374, 0] := by
  rw [show D2M8K2.u12776 = KTree.node D2M8K2.u12768 (nat_lit 27475279) (nat_lit 2389817115) (nat_lit 0) D2M8K2.u12775 from rfl, totK_node, atot12768, atot12775]
  decide +kernel

theorem arows12791 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12791 = true := by
  rw [show D2M8K2.u12791 = KTree.node D2M8K2.u12783 (nat_lit 27498566) (nat_lit 3932429398) (nat_lit 0) D2M8K2.u12790 from rfl, allE_node, arows12783, irow12791, arows12790]
  all_goals rfl

theorem atot12791 : totK PD2M8K2 D2M8K2.u12791 = [0, 1192675812848, 4679950424848, 5825807888325, 2480580124970, 257325957108, 4574395652, 0] := by
  rw [show D2M8K2.u12791 = KTree.node D2M8K2.u12783 (nat_lit 27498566) (nat_lit 3932429398) (nat_lit 0) D2M8K2.u12790 from rfl, totK_node, atot12783, atot12790]
  decide +kernel

theorem arows12811 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12811 = true := by
  rw [show D2M8K2.u12811 = KTree.node D2M8K2.u12803 (nat_lit 27515215) (nat_lit 1792094332) (nat_lit 0) D2M8K2.u12810 from rfl, allE_node, arows12803, irow12811, arows12810]
  all_goals rfl

theorem atot12811 : totK PD2M8K2 D2M8K2.u12811 = [0, 800520697250, 4393021312910, 6647533746832, 2472674377179, 138947206516, 0, 0] := by
  rw [show D2M8K2.u12811 = KTree.node D2M8K2.u12803 (nat_lit 27515215) (nat_lit 1792094332) (nat_lit 0) D2M8K2.u12810 from rfl, totK_node, atot12803, atot12810]
  decide +kernel

theorem arows12826 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12826 = true := by
  rw [show D2M8K2.u12826 = KTree.node D2M8K2.u12818 (nat_lit 27538002) (nat_lit 2647010800) (nat_lit 0) D2M8K2.u12825 from rfl, allE_node, arows12818, irow12826, arows12825]
  all_goals rfl

theorem atot12826 : totK PD2M8K2 D2M8K2.u12826 = [0, 937172614982, 3905627054430, 5697665312755, 3270626797623, 537648463413, 17826068843, 0] := by
  rw [show D2M8K2.u12826 = KTree.node D2M8K2.u12818 (nat_lit 27538002) (nat_lit 2647010800) (nat_lit 0) D2M8K2.u12825 from rfl, totK_node, atot12818, atot12825]
  decide +kernel

theorem arows12842 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12842 = true := by
  rw [show D2M8K2.u12842 = KTree.node D2M8K2.u12834 (nat_lit 27551606) (nat_lit 3982414624) (nat_lit 0) D2M8K2.u12841 from rfl, allE_node, arows12834, irow12842, arows12841]
  all_goals rfl

theorem atot12842 : totK PD2M8K2 D2M8K2.u12842 = [0, 1101018870619, 4968469326608, 6304231892622, 1920595371966, 101076864353, 0, 0] := by
  rw [show D2M8K2.u12842 = KTree.node D2M8K2.u12834 (nat_lit 27551606) (nat_lit 3982414624) (nat_lit 0) D2M8K2.u12841 from rfl, totK_node, atot12834, atot12841]
  decide +kernel

theorem arows12857 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12857 = true := by
  rw [show D2M8K2.u12857 = KTree.node D2M8K2.u12849 (nat_lit 27582674) (nat_lit 4138950161) (nat_lit 0) D2M8K2.u12856 from rfl, allE_node, arows12849, irow12857, arows12856]
  all_goals rfl

theorem atot12857 : totK PD2M8K2 D2M8K2.u12857 = [0, 833461993264, 4006819455851, 6247854119344, 3023834997801, 320308672095, 4977114383, 0] := by
  rw [show D2M8K2.u12857 = KTree.node D2M8K2.u12849 (nat_lit 27582674) (nat_lit 4138950161) (nat_lit 0) D2M8K2.u12856 from rfl, totK_node, atot12849, atot12856]
  decide +kernel

theorem arows12874 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12874 = true := by
  rw [show D2M8K2.u12874 = KTree.node D2M8K2.u12866 (nat_lit 27598729) (nat_lit 1402944765) (nat_lit 0) D2M8K2.u12873 from rfl, allE_node, arows12866, irow12874, arows12873]
  all_goals rfl

theorem atot12874 : totK PD2M8K2 D2M8K2.u12874 = [0, 832738749245, 4190505463745, 6376985650987, 2852196334843, 250485966459, 1435164049, 0] := by
  rw [show D2M8K2.u12874 = KTree.node D2M8K2.u12866 (nat_lit 27598729) (nat_lit 1402944765) (nat_lit 0) D2M8K2.u12873 from rfl, totK_node, atot12866, atot12873]
  decide +kernel

theorem arows12889 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12889 = true := by
  rw [show D2M8K2.u12889 = KTree.node D2M8K2.u12881 (nat_lit 27870555) (nat_lit 2255560861) (nat_lit 0) D2M8K2.u12888 from rfl, allE_node, arows12881, irow12889, arows12888]
  all_goals rfl

theorem atot12889 : totK PD2M8K2 D2M8K2.u12889 = [0, 1181413159188, 4476577986568, 5522957182827, 2749680951485, 437028730754, 11741670991, 0] := by
  rw [show D2M8K2.u12889 = KTree.node D2M8K2.u12881 (nat_lit 27870555) (nat_lit 2255560861) (nat_lit 0) D2M8K2.u12888 from rfl, totK_node, atot12881, atot12888]
  decide +kernel

theorem arows12905 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12905 = true := by
  rw [show D2M8K2.u12905 = KTree.node D2M8K2.u12897 (nat_lit 27888774) (nat_lit 2604779153) (nat_lit 0) D2M8K2.u12904 from rfl, allE_node, arows12897, irow12905, arows12904]
  all_goals rfl

theorem atot12905 : totK PD2M8K2 D2M8K2.u12905 = [0, 794363628629, 4142906143852, 6403990666004, 2619142323507, 212356646760, 1369150432, 0] := by
  rw [show D2M8K2.u12905 = KTree.node D2M8K2.u12897 (nat_lit 27888774) (nat_lit 2604779153) (nat_lit 0) D2M8K2.u12904 from rfl, totK_node, atot12897, atot12904]
  decide +kernel

theorem arows12920 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12920 = true := by
  rw [show D2M8K2.u12920 = KTree.node D2M8K2.u12912 (nat_lit 27916436) (nat_lit 2922030634) (nat_lit 0) D2M8K2.u12919 from rfl, allE_node, arows12912, irow12920, arows12919]
  all_goals rfl

theorem atot12920 : totK PD2M8K2 D2M8K2.u12920 = [0, 1198987638623, 4948350400823, 6187199802394, 2051730769163, 95953454140, 0, 0] := by
  rw [show D2M8K2.u12920 = KTree.node D2M8K2.u12912 (nat_lit 27916436) (nat_lit 2922030634) (nat_lit 0) D2M8K2.u12919 from rfl, totK_node, atot12912, atot12919]
  decide +kernel

theorem arows12938 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12938 = true := by
  rw [show D2M8K2.u12938 = KTree.node D2M8K2.u12930 (nat_lit 27930395) (nat_lit 2322485156) (nat_lit 0) D2M8K2.u12937 from rfl, allE_node, arows12930, irow12938, arows12937]
  all_goals rfl

theorem atot12938 : totK PD2M8K2 D2M8K2.u12938 = [0, 801330619180, 3971992006513, 6165442067527, 3107951447369, 470874586924, 15089109266, 0] := by
  rw [show D2M8K2.u12938 = KTree.node D2M8K2.u12930 (nat_lit 27930395) (nat_lit 2322485156) (nat_lit 0) D2M8K2.u12937 from rfl, totK_node, atot12930, atot12937]
  decide +kernel

theorem arows12953 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12953 = true := by
  rw [show D2M8K2.u12953 = KTree.node D2M8K2.u12945 (nat_lit 27949659) (nat_lit 3623267831) (nat_lit 0) D2M8K2.u12952 from rfl, allE_node, arows12945, irow12953, arows12952]
  all_goals rfl

theorem atot12953 : totK PD2M8K2 D2M8K2.u12953 = [0, 836818553836, 3931123689593, 5961440561002, 3300062847163, 454144752420, 6575010705, 0] := by
  rw [show D2M8K2.u12953 = KTree.node D2M8K2.u12945 (nat_lit 27949659) (nat_lit 3623267831) (nat_lit 0) D2M8K2.u12952 from rfl, totK_node, atot12945, atot12952]
  decide +kernel

theorem arows12969 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12969 = true := by
  rw [show D2M8K2.u12969 = KTree.node D2M8K2.u12961 (nat_lit 27967833) (nat_lit 1724618156) (nat_lit 0) D2M8K2.u12968 from rfl, allE_node, arows12961, irow12969, arows12968]
  all_goals rfl

theorem atot12969 : totK PD2M8K2 D2M8K2.u12969 = [0, 1270120091846, 5093791076454, 6039631004320, 1837694843370, 86541703098, 0, 0] := by
  rw [show D2M8K2.u12969 = KTree.node D2M8K2.u12961 (nat_lit 27967833) (nat_lit 1724618156) (nat_lit 0) D2M8K2.u12968 from rfl, totK_node, atot12961, atot12968]
  decide +kernel

theorem arows12984 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u12984 = true := by
  rw [show D2M8K2.u12984 = KTree.node D2M8K2.u12976 (nat_lit 27987023) (nat_lit 2088782614) (nat_lit 0) D2M8K2.u12983 from rfl, allE_node, arows12976, irow12984, arows12983]
  all_goals rfl

theorem atot12984 : totK PD2M8K2 D2M8K2.u12984 = [0, 407046338387, 2807429479108, 6135528675403, 4192673037368, 640040602026, 18797058808, 0] := by
  rw [show D2M8K2.u12984 = KTree.node D2M8K2.u12976 (nat_lit 27987023) (nat_lit 2088782614) (nat_lit 0) D2M8K2.u12983 from rfl, totK_node, atot12976, atot12983]
  decide +kernel

theorem arows13001 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13001 = true := by
  rw [show D2M8K2.u13001 = KTree.node D2M8K2.u12993 (nat_lit 28043717) (nat_lit 2325570110) (nat_lit 0) D2M8K2.u13000 from rfl, allE_node, arows12993, irow13001, arows13000]
  all_goals rfl

theorem atot13001 : totK PD2M8K2 D2M8K2.u13001 = [0, 1626785887284, 5740335849387, 5627240324870, 1397906610656, 63381935556, 0, 0] := by
  rw [show D2M8K2.u13001 = KTree.node D2M8K2.u12993 (nat_lit 28043717) (nat_lit 2325570110) (nat_lit 0) D2M8K2.u13000 from rfl, totK_node, atot12993, atot13000]
  decide +kernel

theorem arows13016 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13016 = true := by
  rw [show D2M8K2.u13016 = KTree.node D2M8K2.u13008 (nat_lit 28063401) (nat_lit 1903177887) (nat_lit 0) D2M8K2.u13015 from rfl, allE_node, arows13008, irow13016, arows13015]
  all_goals rfl

theorem atot13016 : totK PD2M8K2 D2M8K2.u13016 = [0, 234545227448, 2902933689826, 6816477148717, 3881684973622, 430787953595, 6115358396, 0] := by
  rw [show D2M8K2.u13016 = KTree.node D2M8K2.u13008 (nat_lit 28063401) (nat_lit 1903177887) (nat_lit 0) D2M8K2.u13015 from rfl, totK_node, atot13008, atot13015]
  decide +kernel

theorem arows13032 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13032 = true := by
  rw [show D2M8K2.u13032 = KTree.node D2M8K2.u13024 (nat_lit 28084085) (nat_lit 2404007425) (nat_lit 0) D2M8K2.u13031 from rfl, allE_node, arows13024, irow13032, arows13031]
  all_goals rfl

theorem atot13032 : totK PD2M8K2 D2M8K2.u13032 = [0, 1423446428950, 5476047580062, 5896958537116, 1583266672586, 71409659663, 0, 0] := by
  rw [show D2M8K2.u13032 = KTree.node D2M8K2.u13024 (nat_lit 28084085) (nat_lit 2404007425) (nat_lit 0) D2M8K2.u13031 from rfl, totK_node, atot13024, atot13031]
  decide +kernel

theorem arows13047 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13047 = true := by
  rw [show D2M8K2.u13047 = KTree.node D2M8K2.u13039 (nat_lit 28106527) (nat_lit 909849003) (nat_lit 0) D2M8K2.u13046 from rfl, allE_node, arows13039, irow13047, arows13046]
  all_goals rfl

theorem atot13047 : totK PD2M8K2 D2M8K2.u13047 = [0, 653724168880, 3573423141441, 6254646317195, 3475393452784, 382847685290, 6190125969, 0] := by
  rw [show D2M8K2.u13047 = KTree.node D2M8K2.u13039 (nat_lit 28106527) (nat_lit 909849003) (nat_lit 0) D2M8K2.u13046 from rfl, totK_node, atot13039, atot13046]
  decide +kernel

theorem arows13066 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13066 = true := by
  rw [show D2M8K2.u13066 = KTree.node D2M8K2.u13058 (nat_lit 28381714) (nat_lit 3143150935) (nat_lit 0) D2M8K2.u13065 from rfl, allE_node, arows13058, irow13066, arows13065]
  all_goals rfl

theorem atot13066 : totK PD2M8K2 D2M8K2.u13066 = [0, 1319093304201, 5346420019053, 5966518588350, 1568992216412, 67113803584, 0, 0] := by
  rw [show D2M8K2.u13066 = KTree.node D2M8K2.u13058 (nat_lit 28381714) (nat_lit 3143150935) (nat_lit 0) D2M8K2.u13065 from rfl, totK_node, atot13058, atot13065]
  decide +kernel

theorem arows13081 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13081 = true := by
  rw [show D2M8K2.u13081 = KTree.node D2M8K2.u13073 (nat_lit 28404950) (nat_lit 3130483929) (nat_lit 0) D2M8K2.u13080 from rfl, allE_node, arows13073, irow13081, arows13080]
  all_goals rfl

theorem atot13081 : totK PD2M8K2 D2M8K2.u13081 = [0, 703929212621, 3774226377759, 6549099125578, 3085010445792, 241430414141, 1369150432, 0] := by
  rw [show D2M8K2.u13081 = KTree.node D2M8K2.u13073 (nat_lit 28404950) (nat_lit 3130483929) (nat_lit 0) D2M8K2.u13080 from rfl, totK_node, atot13073, atot13080]
  decide +kernel

theorem arows13097 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13097 = true := by
  rw [show D2M8K2.u13097 = KTree.node D2M8K2.u13089 (nat_lit 28423353) (nat_lit 1864447005) (nat_lit 0) D2M8K2.u13096 from rfl, allE_node, arows13089, irow13097, arows13096]
  all_goals rfl

theorem atot13097 : totK PD2M8K2 D2M8K2.u13097 = [0, 1296612107251, 5344344837906, 6098307412555, 1712243748569, 83653118347, 0, 0] := by
  rw [show D2M8K2.u13097 = KTree.node D2M8K2.u13089 (nat_lit 28423353) (nat_lit 1864447005) (nat_lit 0) D2M8K2.u13096 from rfl, totK_node, atot13089, atot13096]
  decide +kernel

theorem arows13112 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13112 = true := by
  rw [show D2M8K2.u13112 = KTree.node D2M8K2.u13104 (nat_lit 28442977) (nat_lit 1503033362) (nat_lit 0) D2M8K2.u13111 from rfl, allE_node, arows13104, irow13112, arows13111]
  all_goals rfl

theorem atot13112 : totK PD2M8K2 D2M8K2.u13112 = [0, 413264604107, 2672151908140, 5951058178628, 4611798456965, 834320924728, 21811729820, 0] := by
  rw [show D2M8K2.u13112 = KTree.node D2M8K2.u13104 (nat_lit 28442977) (nat_lit 1503033362) (nat_lit 0) D2M8K2.u13111 from rfl, totK_node, atot13104, atot13111]
  decide +kernel

theorem arows13129 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13129 = true := by
  rw [show D2M8K2.u13129 = KTree.node D2M8K2.u13121 (nat_lit 28503094) (nat_lit 3561620279) (nat_lit 0) D2M8K2.u13128 from rfl, allE_node, arows13121, irow13129, arows13128]
  all_goals rfl

theorem atot13129 : totK PD2M8K2 D2M8K2.u13129 = [0, 1606228760063, 5768175408289, 5703382476489, 1359703956616, 55491918696, 0, 0] := by
  rw [show D2M8K2.u13129 = KTree.node D2M8K2.u13121 (nat_lit 28503094) (nat_lit 3561620279) (nat_lit 0) D2M8K2.u13128 from rfl, totK_node, atot13121, atot13128]
  decide +kernel

theorem arows13144 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13144 = true := by
  rw [show D2M8K2.u13144 = KTree.node D2M8K2.u13136 (nat_lit 28516989) (nat_lit 1159419478) (nat_lit 2) D2M8K2.u13143 from rfl, allE_node, arows13136, irow13144, arows13143]
  all_goals rfl

theorem atot13144 : totK PD2M8K2 D2M8K2.u13144 = [0, 87861870204, 2330848581685, 6612998628763, 4542102048849, 615855406707, 15398727635, 0] := by
  rw [show D2M8K2.u13144 = KTree.node D2M8K2.u13136 (nat_lit 28516989) (nat_lit 1159419478) (nat_lit 2) D2M8K2.u13143 from rfl, totK_node, atot13136, atot13143]
  decide +kernel

theorem arows13160 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13160 = true := by
  rw [show D2M8K2.u13160 = KTree.node D2M8K2.u13152 (nat_lit 28537590) (nat_lit 3739328852) (nat_lit 0) D2M8K2.u13159 from rfl, allE_node, arows13152, irow13160, arows13159]
  all_goals rfl

theorem atot13160 : totK PD2M8K2 D2M8K2.u13160 = [0, 1522680147547, 5440742512524, 5552769810884, 1725697038496, 149793760619, 3667207281, 0] := by
  rw [show D2M8K2.u13160 = KTree.node D2M8K2.u13152 (nat_lit 28537590) (nat_lit 3739328852) (nat_lit 0) D2M8K2.u13159 from rfl, totK_node, atot13152, atot13159]
  decide +kernel

theorem arows13175 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13175 = true := by
  rw [show D2M8K2.u13175 = KTree.node D2M8K2.u13167 (nat_lit 28554781) (nat_lit 1081283312) (nat_lit 0) D2M8K2.u13174 from rfl, allE_node, arows13167, irow13175, arows13174]
  all_goals rfl

theorem atot13175 : totK PD2M8K2 D2M8K2.u13175 = [0, 511297306850, 3760384856457, 6866530801317, 2985482735678, 217764392738, 1138244013, 0] := by
  rw [show D2M8K2.u13175 = KTree.node D2M8K2.u13167 (nat_lit 28554781) (nat_lit 1081283312) (nat_lit 0) D2M8K2.u13174 from rfl, totK_node, atot13167, atot13174]
  decide +kernel

theorem arows13193 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13193 = true := by
  rw [show D2M8K2.u13193 = KTree.node D2M8K2.u13185 (nat_lit 28578210) (nat_lit 3262745333) (nat_lit 0) D2M8K2.u13192 from rfl, allE_node, arows13185, irow13193, arows13192]
  all_goals rfl

theorem atot13193 : totK PD2M8K2 D2M8K2.u13193 = [0, 1230295041496, 4761819783807, 5751291813477, 2353554207638, 275670884127, 4977114383, 0] := by
  rw [show D2M8K2.u13193 = KTree.node D2M8K2.u13185 (nat_lit 28578210) (nat_lit 3262745333) (nat_lit 0) D2M8K2.u13192 from rfl, totK_node, atot13185, atot13192]
  decide +kernel

theorem arows13208 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13208 = true := by
  rw [show D2M8K2.u13208 = KTree.node D2M8K2.u13200 (nat_lit 28598752) (nat_lit 3751831776) (nat_lit 0) D2M8K2.u13207 from rfl, allE_node, arows13200, irow13208, arows13207]
  all_goals rfl

theorem atot13208 : totK PD2M8K2 D2M8K2.u13208 = [0, 428021878965, 3217095981228, 6568331172770, 3772908319067, 400519017812, 6241690223, 0] := by
  rw [show D2M8K2.u13208 = KTree.node D2M8K2.u13200 (nat_lit 28598752) (nat_lit 3751831776) (nat_lit 0) D2M8K2.u13207 from rfl, totK_node, atot13200, atot13207]
  decide +kernel

theorem arows13224 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13224 = true := by
  rw [show D2M8K2.u13224 = KTree.node D2M8K2.u13216 (nat_lit 28874624) (nat_lit 2390327964) (nat_lit 0) D2M8K2.u13223 from rfl, allE_node, arows13216, irow13224, arows13223]
  all_goals rfl

theorem atot13224 : totK PD2M8K2 D2M8K2.u13224 = [0, 1680865931409, 5953236854247, 5542115916564, 1132334711654, 42412163793, 0, 0] := by
  rw [show D2M8K2.u13224 = KTree.node D2M8K2.u13216 (nat_lit 28874624) (nat_lit 2390327964) (nat_lit 0) D2M8K2.u13223 from rfl, totK_node, atot13216, atot13223]
  decide +kernel

theorem arows13239 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13239 = true := by
  rw [show D2M8K2.u13239 = KTree.node D2M8K2.u13231 (nat_lit 28892794) (nat_lit 3956944184) (nat_lit 0) D2M8K2.u13238 from rfl, allE_node, arows13231, irow13239, arows13238]
  all_goals rfl

theorem atot13239 : totK PD2M8K2 D2M8K2.u13239 = [0, 450309721602, 3429476203260, 6833207723322, 3179135945667, 229027833555, 1369150432, 0] := by
  rw [show D2M8K2.u13239 = KTree.node D2M8K2.u13231 (nat_lit 28892794) (nat_lit 3956944184) (nat_lit 0) D2M8K2.u13238 from rfl, totK_node, atot13231, atot13238]
  decide +kernel

theorem arows13256 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13256 = true := by
  rw [show D2M8K2.u13256 = KTree.node D2M8K2.u13248 (nat_lit 28916034) (nat_lit 1569029368) (nat_lit 0) D2M8K2.u13255 from rfl, allE_node, arows13248, irow13256, arows13255]
  all_goals rfl

theorem atot13256 : totK PD2M8K2 D2M8K2.u13256 = [0, 1569651411858, 5728517918692, 5718019146097, 1421442920018, 64980090578, 0, 0] := by
  rw [show D2M8K2.u13256 = KTree.node D2M8K2.u13248 (nat_lit 28916034) (nat_lit 1569029368) (nat_lit 0) D2M8K2.u13255 from rfl, totK_node, atot13248, atot13255]
  decide +kernel

theorem arows13271 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13271 = true := by
  rw [show D2M8K2.u13271 = KTree.node D2M8K2.u13263 (nat_lit 28933396) (nat_lit 4005314280) (nat_lit 0) D2M8K2.u13270 from rfl, allE_node, arows13263, irow13271, arows13270]
  all_goals rfl

theorem atot13271 : totK PD2M8K2 D2M8K2.u13271 = [0, 330028431640, 2564944188107, 6047847640499, 4569571740134, 892049390616, 34105821913, 0] := by
  rw [show D2M8K2.u13271 = KTree.node D2M8K2.u13263 (nat_lit 28933396) (nat_lit 4005314280) (nat_lit 0) D2M8K2.u13270 from rfl, totK_node, atot13263, atot13270]
  decide +kernel

theorem arows13287 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13287 = true := by
  rw [show D2M8K2.u13287 = KTree.node D2M8K2.u13279 (nat_lit 28949881) (nat_lit 1493958301) (nat_lit 0) D2M8K2.u13286 from rfl, allE_node, arows13279, irow13287, arows13286]
  all_goals rfl

theorem atot13287 : totK PD2M8K2 D2M8K2.u13287 = [0, 1264237419251, 4783778449871, 5712497549718, 2486293922347, 251737039797, 1415142070, 0] := by
  rw [show D2M8K2.u13287 = KTree.node D2M8K2.u13279 (nat_lit 28949881) (nat_lit 1493958301) (nat_lit 0) D2M8K2.u13286 from rfl, totK_node, atot13279, atot13286]
  decide +kernel

theorem arows13302 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13302 = true := by
  rw [show D2M8K2.u13302 = KTree.node D2M8K2.u13294 (nat_lit 28967044) (nat_lit 3847744678) (nat_lit 0) D2M8K2.u13301 from rfl, allE_node, arows13294, irow13302, arows13301]
  all_goals rfl

theorem atot13302 : totK PD2M8K2 D2M8K2.u13302 = [0, 750959639351, 4136207531272, 6531803552768, 2694059533884, 191257002879, 1206465782, 0] := by
  rw [show D2M8K2.u13302 = KTree.node D2M8K2.u13294 (nat_lit 28967044) (nat_lit 3847744678) (nat_lit 0) D2M8K2.u13301 from rfl, totK_node, atot13294, atot13301]
  decide +kernel

theorem arows13323 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13323 = true := by
  rw [show D2M8K2.u13323 = KTree.node D2M8K2.u13315 (nat_lit 28987180) (nat_lit 3824353533) (nat_lit 0) D2M8K2.u13322 from rfl, allE_node, arows13315, irow13323, arows13322]
  all_goals rfl

theorem atot13323 : totK PD2M8K2 D2M8K2.u13323 = [0, 824641558620, 3791691685548, 5888761118708, 3234106937132, 483006478715, 17590593026, 0] := by
  rw [show D2M8K2.u13323 = KTree.node D2M8K2.u13315 (nat_lit 28987180) (nat_lit 3824353533) (nat_lit 0) D2M8K2.u13322 from rfl, totK_node, atot13315, atot13322]
  decide +kernel

theorem arows13338 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13338 = true := by
  rw [show D2M8K2.u13338 = KTree.node D2M8K2.u13330 (nat_lit 29005471) (nat_lit 2357151223) (nat_lit 0) D2M8K2.u13337 from rfl, allE_node, arows13330, irow13338, arows13337]
  all_goals rfl

theorem atot13338 : totK PD2M8K2 D2M8K2.u13338 = [0, 1191038544860, 4813996337486, 5965383431862, 2213639900831, 159658014739, 1239866073, 0] := by
  rw [show D2M8K2.u13338 = KTree.node D2M8K2.u13330 (nat_lit 29005471) (nat_lit 2357151223) (nat_lit 0) D2M8K2.u13337 from rfl, totK_node, atot13330, atot13337]
  decide +kernel

theorem arows13354 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13354 = true := by
  rw [show D2M8K2.u13354 = KTree.node D2M8K2.u13346 (nat_lit 29025336) (nat_lit 3580874609) (nat_lit 0) D2M8K2.u13353 from rfl, allE_node, arows13346, irow13354, arows13353]
  all_goals rfl

theorem atot13354 : totK PD2M8K2 D2M8K2.u13354 = [0, 683693930759, 3504008660865, 6081270204523, 3494904069251, 506285480033, 17826068843, 0] := by
  rw [show D2M8K2.u13354 = KTree.node D2M8K2.u13346 (nat_lit 29025336) (nat_lit 3580874609) (nat_lit 0) D2M8K2.u13353 from rfl, totK_node, atot13346, atot13353]
  decide +kernel

theorem arows13369 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13369 = true := by
  rw [show D2M8K2.u13369 = KTree.node D2M8K2.u13361 (nat_lit 29041096) (nat_lit 3659318637) (nat_lit 0) D2M8K2.u13368 from rfl, allE_node, arows13361, irow13369, arows13368]
  all_goals rfl

theorem atot13369 : totK PD2M8K2 D2M8K2.u13369 = [0, 1445859365247, 5581343558732, 5873285510559, 1505372613822, 66224643496, 0, 0] := by
  rw [show D2M8K2.u13369 = KTree.node D2M8K2.u13361 (nat_lit 29041096) (nat_lit 3659318637) (nat_lit 0) D2M8K2.u13368 from rfl, totK_node, atot13361, atot13368]
  decide +kernel

theorem arows13386 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13386 = true := by
  rw [show D2M8K2.u13386 = KTree.node D2M8K2.u13378 (nat_lit 29061655) (nat_lit 2225288195) (nat_lit 0) D2M8K2.u13385 from rfl, allE_node, arows13378, irow13386, arows13385]
  all_goals rfl

theorem atot13386 : totK PD2M8K2 D2M8K2.u13386 = [0, 0, 2446323692502, 7079445649071, 4252112780513, 454150631968, 6115358396, 0] := by
  rw [show D2M8K2.u13386 = KTree.node D2M8K2.u13378 (nat_lit 29061655) (nat_lit 2225288195) (nat_lit 0) D2M8K2.u13385 from rfl, totK_node, atot13378, atot13385]
  decide +kernel

theorem arows13401 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13401 = true := by
  rw [show D2M8K2.u13401 = KTree.node D2M8K2.u13393 (nat_lit 29125584) (nat_lit 3718232426) (nat_lit 0) D2M8K2.u13400 from rfl, allE_node, arows13393, irow13401, arows13400]
  all_goals rfl

theorem atot13401 : totK PD2M8K2 D2M8K2.u13401 = [0, 0, 1571822924392, 6022831771817, 5525930089321, 979947432741, 33786171890, 0] := by
  rw [show D2M8K2.u13401 = KTree.node D2M8K2.u13393 (nat_lit 29125584) (nat_lit 3718232426) (nat_lit 0) D2M8K2.u13400 from rfl, totK_node, atot13393, atot13400]
  decide +kernel

theorem arows13417 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13417 = true := by
  rw [show D2M8K2.u13417 = KTree.node D2M8K2.u13409 (nat_lit 29148721) (nat_lit 1403630470) (nat_lit 0) D2M8K2.u13416 from rfl, allE_node, arows13409, irow13417, arows13416]
  all_goals rfl

theorem atot13417 : totK PD2M8K2 D2M8K2.u13417 = [0, 0, 743084180336, 4184275552324, 6619202246627, 2458079711405, 185509894128, 1209030869] := by
  rw [show D2M8K2.u13417 = KTree.node D2M8K2.u13409 (nat_lit 29148721) (nat_lit 1403630470) (nat_lit 0) D2M8K2.u13416 from rfl, totK_node, atot13409, atot13416]
  decide +kernel

theorem arows13432 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13432 = true := by
  rw [show D2M8K2.u13432 = KTree.node D2M8K2.u13424 (nat_lit 29169947) (nat_lit 967888069) (nat_lit 0) D2M8K2.u13431 from rfl, allE_node, arows13424, irow13432, arows13431]
  all_goals rfl

theorem atot13432 : totK PD2M8K2 D2M8K2.u13432 = [0, 0, 1929583671648, 6472506639457, 5223928412617, 787642269317, 23758133627, 0] := by
  rw [show D2M8K2.u13432 = KTree.node D2M8K2.u13424 (nat_lit 29169947) (nat_lit 967888069) (nat_lit 0) D2M8K2.u13431 from rfl, totK_node, atot13424, atot13431]
  decide +kernel

theorem arows13450 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13450 = true := by
  rw [show D2M8K2.u13450 = KTree.node D2M8K2.u13442 (nat_lit 29210837) (nat_lit 2300682363) (nat_lit 0) D2M8K2.u13449 from rfl, allE_node, arows13442, irow13450, arows13449]
  all_goals rfl

theorem atot13450 : totK PD2M8K2 D2M8K2.u13450 = [0, 0, 1791943886647, 6164237701562, 5333641192788, 995860319051, 34354748642, 0] := by
  rw [show D2M8K2.u13450 = KTree.node D2M8K2.u13442 (nat_lit 29210837) (nat_lit 2300682363) (nat_lit 0) D2M8K2.u13449 from rfl, totK_node, atot13442, atot13449]
  decide +kernel

theorem arows13465 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13465 = true := by
  rw [show D2M8K2.u13465 = KTree.node D2M8K2.u13457 (nat_lit 29251423) (nat_lit 2276198477) (nat_lit 0) D2M8K2.u13464 from rfl, allE_node, arows13457, irow13465, arows13464]
  all_goals rfl

theorem atot13465 : totK PD2M8K2 D2M8K2.u13465 = [0, 0, 1975045275662, 6347485966790, 5102200781685, 933187288688, 33217523550, 0] := by
  rw [show D2M8K2.u13465 = KTree.node D2M8K2.u13457 (nat_lit 29251423) (nat_lit 2276198477) (nat_lit 0) D2M8K2.u13464 from rfl, totK_node, atot13457, atot13464]
  decide +kernel

theorem arows13481 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13481 = true := by
  rw [show D2M8K2.u13481 = KTree.node D2M8K2.u13473 (nat_lit 29287944) (nat_lit 3572807429) (nat_lit 0) D2M8K2.u13480 from rfl, allE_node, arows13473, irow13481, arows13480]
  all_goals rfl

theorem atot13481 : totK PD2M8K2 D2M8K2.u13481 = [0, 0, 1696928111009, 5837403667931, 5488544420977, 1190215914361, 51057111145, 0] := by
  rw [show D2M8K2.u13481 = KTree.node D2M8K2.u13473 (nat_lit 29287944) (nat_lit 3572807429) (nat_lit 0) D2M8K2.u13480 from rfl, totK_node, atot13473, atot13480]
  decide +kernel

theorem arows13496 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13496 = true := by
  rw [show D2M8K2.u13496 = KTree.node D2M8K2.u13488 (nat_lit 29307460) (nat_lit 3869846782) (nat_lit 0) D2M8K2.u13495 from rfl, allE_node, arows13488, irow13496, arows13495]
  all_goals rfl

theorem atot13496 : totK PD2M8K2 D2M8K2.u13496 = [186677387228, 459373490871, 202050743940, 2585454042269, 6665253669781, 3574283802623, 410989452623, 6115358396] := by
  rw [show D2M8K2.u13496 = KTree.node D2M8K2.u13488 (nat_lit 29307460) (nat_lit 3869846782) (nat_lit 0) D2M8K2.u13495 from rfl, totK_node, atot13488, atot13495]
  decide +kernel

theorem arows13513 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13513 = true := by
  rw [show D2M8K2.u13513 = KTree.node D2M8K2.u13505 (nat_lit 29871114) (nat_lit 3914212688) (nat_lit 0) D2M8K2.u13512 from rfl, allE_node, arows13505, irow13513, arows13512]
  all_goals rfl

theorem atot13513 : totK PD2M8K2 D2M8K2.u13513 = [1712307939724, 5972401735050, 5519886769907, 1084147871015, 32650077886, 0, 0, 0] := by
  rw [show D2M8K2.u13513 = KTree.node D2M8K2.u13505 (nat_lit 29871114) (nat_lit 3914212688) (nat_lit 0) D2M8K2.u13512 from rfl, totK_node, atot13505, atot13512]
  decide +kernel

theorem arows13528 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13528 = true := by
  rw [show D2M8K2.u13528 = KTree.node D2M8K2.u13520 (nat_lit 29888092) (nat_lit 3969568137) (nat_lit 0) D2M8K2.u13527 from rfl, allE_node, arows13520, irow13528, arows13527]
  all_goals rfl

theorem atot13528 : totK PD2M8K2 D2M8K2.u13528 = [198165556517, 3090969448648, 7080654850503, 3555595884576, 284336936744, 1369150432, 0, 0] := by
  rw [show D2M8K2.u13528 = KTree.node D2M8K2.u13520 (nat_lit 29888092) (nat_lit 3969568137) (nat_lit 0) D2M8K2.u13527 from rfl, totK_node, atot13520, atot13527]
  decide +kernel

theorem arows13544 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13544 = true := by
  rw [show D2M8K2.u13544 = KTree.node D2M8K2.u13536 (nat_lit 29950042) (nat_lit 3932136345) (nat_lit 0) D2M8K2.u13543 from rfl, allE_node, arows13536, irow13544, arows13543]
  all_goals rfl

theorem atot13544 : totK PD2M8K2 D2M8K2.u13544 = [1733428126403, 5893585869768, 5477551759760, 1269885051053, 61468971431, 0, 0, 0] := by
  rw [show D2M8K2.u13544 = KTree.node D2M8K2.u13536 (nat_lit 29950042) (nat_lit 3932136345) (nat_lit 0) D2M8K2.u13543 from rfl, totK_node, atot13536, atot13543]
  decide +kernel

theorem arows13559 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13559 = true := by
  rw [show D2M8K2.u13559 = KTree.node D2M8K2.u13551 (nat_lit 29967691) (nat_lit 1273930765) (nat_lit 0) D2M8K2.u13558 from rfl, allE_node, arows13551, irow13559, arows13558]
  all_goals rfl

theorem atot13559 : totK PD2M8K2 D2M8K2.u13559 = [250158719299, 2714143001086, 6455761198684, 4210384679835, 586625815859, 15244263794, 0, 0] := by
  rw [show D2M8K2.u13559 = KTree.node D2M8K2.u13551 (nat_lit 29967691) (nat_lit 1273930765) (nat_lit 0) D2M8K2.u13558 from rfl, totK_node, atot13551, atot13558]
  decide +kernel

theorem arows13578 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13578 = true := by
  rw [show D2M8K2.u13578 = KTree.node D2M8K2.u13570 (nat_lit 29989041) (nat_lit 1618026260) (nat_lit 0) D2M8K2.u13577 from rfl, allE_node, arows13570, irow13578, arows13577]
  all_goals rfl

theorem atot13578 : totK PD2M8K2 D2M8K2.u13578 = [1452866744464, 5243793175628, 5659677996414, 1912234918347, 175284473541, 3552795014, 0, 0] := by
  rw [show D2M8K2.u13578 = KTree.node D2M8K2.u13570 (nat_lit 29989041) (nat_lit 1618026260) (nat_lit 0) D2M8K2.u13577 from rfl, totK_node, atot13570, atot13577]
  decide +kernel

theorem arows13593 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13593 = true := by
  rw [show D2M8K2.u13593 = KTree.node D2M8K2.u13585 (nat_lit 30006200) (nat_lit 3733850413) (nat_lit 0) D2M8K2.u13592 from rfl, allE_node, arows13585, irow13593, arows13592]
  all_goals rfl

theorem atot13593 : totK PD2M8K2 D2M8K2.u13593 = [531243139844, 3405414755257, 6284102240136, 3576049516178, 496808970149, 14345316470, 0, 0] := by
  rw [show D2M8K2.u13593 = KTree.node D2M8K2.u13585 (nat_lit 30006200) (nat_lit 3733850413) (nat_lit 0) D2M8K2.u13592 from rfl, totK_node, atot13585, atot13592]
  decide +kernel

theorem arows13609 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13609 = true := by
  rw [show D2M8K2.u13609 = KTree.node D2M8K2.u13601 (nat_lit 30027249) (nat_lit 1565909187) (nat_lit 0) D2M8K2.u13608 from rfl, allE_node, arows13601, irow13609, arows13608]
  all_goals rfl

theorem atot13609 : totK PD2M8K2 D2M8K2.u13609 = [1221142394597, 4756231158840, 5692793673730, 2377113093005, 258111555391, 4720618446, 0, 0] := by
  rw [show D2M8K2.u13609 = KTree.node D2M8K2.u13601 (nat_lit 30027249) (nat_lit 1565909187) (nat_lit 0) D2M8K2.u13608 from rfl, totK_node, atot13601, atot13608]
  decide +kernel

theorem arows13624 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13624 = true := by
  rw [show D2M8K2.u13624 = KTree.node D2M8K2.u13616 (nat_lit 30048288) (nat_lit 3619169329) (nat_lit 0) D2M8K2.u13623 from rfl, allE_node, arows13616, irow13624, arows13623]
  all_goals rfl

theorem atot13624 : totK PD2M8K2 D2M8K2.u13624 = [423568743631, 3500818777963, 6837089721271, 3200446526223, 250668590347, 2233351729, 0, 0] := by
  rw [show D2M8K2.u13624 = KTree.node D2M8K2.u13616 (nat_lit 30048288) (nat_lit 3619169329) (nat_lit 0) D2M8K2.u13623 from rfl, totK_node, atot13616, atot13623]
  decide +kernel

theorem arows13641 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13641 = true := by
  rw [show D2M8K2.u13641 = KTree.node D2M8K2.u13633 (nat_lit 30073279) (nat_lit 2369880789) (nat_lit 0) D2M8K2.u13640 from rfl, allE_node, arows13633, irow13641, arows13640]
  all_goals rfl

theorem atot13641 : totK PD2M8K2 D2M8K2.u13641 = [1596198355648, 5475208955860, 5425819220668, 1772546565039, 206624394145, 3882006667, 0, 0] := by
  rw [show D2M8K2.u13641 = KTree.node D2M8K2.u13633 (nat_lit 30073279) (nat_lit 2369880789) (nat_lit 0) D2M8K2.u13640 from rfl, totK_node, atot13633, atot13640]
  decide +kernel

theorem arows13656 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13656 = true := by
  rw [show D2M8K2.u13656 = KTree.node D2M8K2.u13648 (nat_lit 30089773) (nat_lit 1112616237) (nat_lit 0) D2M8K2.u13655 from rfl, allE_node, arows13648, irow13656, arows13655]
  all_goals rfl

theorem atot13656 : totK PD2M8K2 D2M8K2.u13656 = [442799796658, 3185439030376, 6444915283400, 3897701116692, 448633201131, 6190125969, 0, 0] := by
  rw [show D2M8K2.u13656 = KTree.node D2M8K2.u13648 (nat_lit 30089773) (nat_lit 1112616237) (nat_lit 0) D2M8K2.u13655 from rfl, totK_node, atot13648, atot13655]
  decide +kernel

theorem arows13672 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13672 = true := by
  rw [show D2M8K2.u13672 = KTree.node D2M8K2.u13664 (nat_lit 30109454) (nat_lit 2878069907) (nat_lit 0) D2M8K2.u13671 from rfl, allE_node, arows13664, irow13672, arows13671]
  all_goals rfl

theorem atot13672 : totK PD2M8K2 D2M8K2.u13672 = [0, 1663739607308, 5974888082201, 5526419322908, 1091299777213, 40943381153, 0, 0] := by
  rw [show D2M8K2.u13672 = KTree.node D2M8K2.u13664 (nat_lit 30109454) (nat_lit 2878069907) (nat_lit 0) D2M8K2.u13671 from rfl, totK_node, atot13664, atot13671]
  decide +kernel

theorem arows13687 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13687 = true := by
  rw [show D2M8K2.u13687 = KTree.node D2M8K2.u13679 (nat_lit 30126655) (nat_lit 1796471101) (nat_lit 0) D2M8K2.u13686 from rfl, allE_node, arows13679, irow13687, arows13686]
  all_goals rfl

theorem atot13687 : totK PD2M8K2 D2M8K2.u13687 = [0, 1055547689358, 4617167840065, 6049158300295, 2174048462141, 206804173743, 1369150432, 0] := by
  rw [show D2M8K2.u13687 = KTree.node D2M8K2.u13679 (nat_lit 30126655) (nat_lit 1796471101) (nat_lit 0) D2M8K2.u13686 from rfl, totK_node, atot13679, atot13686]
  decide +kernel

theorem arows13705 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13705 = true := by
  rw [show D2M8K2.u13705 = KTree.node D2M8K2.u13697 (nat_lit 30192458) (nat_lit 3728825213) (nat_lit 0) D2M8K2.u13704 from rfl, allE_node, arows13697, irow13705, arows13704]
  all_goals rfl

theorem atot13705 : totK PD2M8K2 D2M8K2.u13705 = [0, 1134051614701, 4979136357065, 6231791754627, 1815873700247, 92771229980, 0, 0] := by
  rw [show D2M8K2.u13705 = KTree.node D2M8K2.u13697 (nat_lit 30192458) (nat_lit 3728825213) (nat_lit 0) D2M8K2.u13704 from rfl, totK_node, atot13697, atot13704]
  decide +kernel

theorem arows13720 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13720 = true := by
  rw [show D2M8K2.u13720 = KTree.node D2M8K2.u13712 (nat_lit 30210540) (nat_lit 2890330849) (nat_lit 0) D2M8K2.u13719 from rfl, allE_node, arows13712, irow13720, arows13719]
  all_goals rfl

theorem atot13720 : totK PD2M8K2 D2M8K2.u13720 = [0, 1595623926338, 5918125853585, 5741799266936, 1112504540332, 33020449330, 0, 0] := by
  rw [show D2M8K2.u13720 = KTree.node D2M8K2.u13712 (nat_lit 30210540) (nat_lit 2890330849) (nat_lit 0) D2M8K2.u13719 from rfl, totK_node, atot13712, atot13719]
  decide +kernel

theorem arows13736 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13736 = true := by
  rw [show D2M8K2.u13736 = KTree.node D2M8K2.u13728 (nat_lit 30249508) (nat_lit 2387876533) (nat_lit 0) D2M8K2.u13735 from rfl, allE_node, arows13728, irow13736, arows13735]
  all_goals rfl

theorem atot13736 : totK PD2M8K2 D2M8K2.u13736 = [0, 1650255688321, 5851953890446, 5626739596115, 1191889076074, 38520984637, 0, 0] := by
  rw [show D2M8K2.u13736 = KTree.node D2M8K2.u13728 (nat_lit 30249508) (nat_lit 2387876533) (nat_lit 0) D2M8K2.u13735 from rfl, totK_node, atot13728, atot13735]
  decide +kernel

theorem arows13751 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13751 = true := by
  rw [show D2M8K2.u13751 = KTree.node D2M8K2.u13743 (nat_lit 30287907) (nat_lit 3639380560) (nat_lit 0) D2M8K2.u13750 from rfl, allE_node, arows13743, irow13751, arows13750]
  all_goals rfl

theorem atot13751 : totK PD2M8K2 D2M8K2.u13751 = [0, 1641534855723, 5964452652079, 5616737905003, 1044244438937, 32517432587, 0, 0] := by
  rw [show D2M8K2.u13751 = KTree.node D2M8K2.u13743 (nat_lit 30287907) (nat_lit 3639380560) (nat_lit 0) D2M8K2.u13750 from rfl, totK_node, atot13743, atot13750]
  decide +kernel

theorem arows13768 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13768 = true := by
  rw [show D2M8K2.u13768 = KTree.node D2M8K2.u13760 (nat_lit 30326769) (nat_lit 1745224386) (nat_lit 0) D2M8K2.u13767 from rfl, allE_node, arows13760, irow13768, arows13767]
  all_goals rfl

theorem atot13768 : totK PD2M8K2 D2M8K2.u13768 = [49567372496, 1683685803632, 5788320011896, 5728767112469, 1269148069747, 41804758000, 0, 0] := by
  rw [show D2M8K2.u13768 = KTree.node D2M8K2.u13760 (nat_lit 30326769) (nat_lit 1745224386) (nat_lit 0) D2M8K2.u13767 from rfl, totK_node, atot13760, atot13767]
  decide +kernel

theorem arows13783 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13783 = true := by
  rw [show D2M8K2.u13783 = KTree.node D2M8K2.u13775 (nat_lit 30408354) (nat_lit 1053839421) (nat_lit 0) D2M8K2.u13782 from rfl, allE_node, arows13775, irow13783, arows13782]
  all_goals rfl

theorem atot13783 : totK PD2M8K2 D2M8K2.u13783 = [1638535874748, 5771786869334, 5613287569972, 1396952202429, 63580453314, 0, 0, 0] := by
  rw [show D2M8K2.u13783 = KTree.node D2M8K2.u13775 (nat_lit 30408354) (nat_lit 1053839421) (nat_lit 0) D2M8K2.u13782 from rfl, totK_node, atot13775, atot13782]
  decide +kernel

theorem arows13799 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13799 = true := by
  rw [show D2M8K2.u13799 = KTree.node D2M8K2.u13791 (nat_lit 30425380) (nat_lit 3965521428) (nat_lit 0) D2M8K2.u13798 from rfl, allE_node, arows13791, irow13799, arows13798]
  all_goals rfl

theorem atot13799 : totK PD2M8K2 D2M8K2.u13799 = [425933657684, 2986559293773, 6035645266150, 4116937935269, 883508907106, 42081742489, 0, 0] := by
  rw [show D2M8K2.u13799 = KTree.node D2M8K2.u13791 (nat_lit 30425380) (nat_lit 3965521428) (nat_lit 0) D2M8K2.u13798 from rfl, totK_node, atot13791, atot13798]
  decide +kernel

theorem arows13814 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13814 = true := by
  rw [show D2M8K2.u13814 = KTree.node D2M8K2.u13806 (nat_lit 30439094) (nat_lit 3982192391) (nat_lit 0) D2M8K2.u13813 from rfl, allE_node, arows13806, irow13814, arows13813]
  all_goals rfl

theorem atot13814 : totK PD2M8K2 D2M8K2.u13814 = [754346683581, 3336366164311, 5604035023830, 4011536885705, 740497979681, 15936385454, 0, 0] := by
  rw [show D2M8K2.u13814 = KTree.node D2M8K2.u13806 (nat_lit 30439094) (nat_lit 3982192391) (nat_lit 0) D2M8K2.u13813 from rfl, totK_node, atot13806, atot13813]
  decide +kernel

theorem arows13834 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13834 = true := by
  rw [show D2M8K2.u13834 = KTree.node D2M8K2.u13826 (nat_lit 30456410) (nat_lit 4079365871) (nat_lit 0) D2M8K2.u13833 from rfl, allE_node, arows13826, irow13834, arows13833]
  all_goals rfl

theorem atot13834 : totK PD2M8K2 D2M8K2.u13834 = [1239149993863, 4903112155567, 5935498122128, 2145012769702, 162623504779, 1206465782, 0, 0] := by
  rw [show D2M8K2.u13834 = KTree.node D2M8K2.u13826 (nat_lit 30456410) (nat_lit 4079365871) (nat_lit 0) D2M8K2.u13833 from rfl, totK_node, atot13826, atot13833]
  decide +kernel

theorem arows13849 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13849 = true := by
  rw [show D2M8K2.u13849 = KTree.node D2M8K2.u13841 (nat_lit 30475957) (nat_lit 1112185182) (nat_lit 0) D2M8K2.u13848 from rfl, allE_node, arows13841, irow13849, arows13848]
  all_goals rfl

theorem atot13849 : totK PD2M8K2 D2M8K2.u13849 = [491803923217, 3188639361306, 6280618844594, 3838048504743, 574385198913, 17590593026, 0, 0] := by
  rw [show D2M8K2.u13849 = KTree.node D2M8K2.u13841 (nat_lit 30475957) (nat_lit 1112185182) (nat_lit 0) D2M8K2.u13848 from rfl, totK_node, atot13841, atot13848]
  decide +kernel

theorem arows13865 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13865 = true := by
  rw [show D2M8K2.u13865 = KTree.node D2M8K2.u13857 (nat_lit 30495483) (nat_lit 3743919589) (nat_lit 0) D2M8K2.u13864 from rfl, allE_node, arows13857, irow13865, arows13864]
  all_goals rfl

theorem atot13865 : totK PD2M8K2 D2M8K2.u13865 = [1502239843726, 5572651855650, 5802357784049, 1541723261404, 65738977272, 0, 0, 0] := by
  rw [show D2M8K2.u13865 = KTree.node D2M8K2.u13857 (nat_lit 30495483) (nat_lit 3743919589) (nat_lit 0) D2M8K2.u13864 from rfl, totK_node, atot13857, atot13864]
  decide +kernel

theorem arows13880 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13880 = true := by
  rw [show D2M8K2.u13880 = KTree.node D2M8K2.u13872 (nat_lit 30514900) (nat_lit 2774901383) (nat_lit 0) D2M8K2.u13879 from rfl, allE_node, arows13872, irow13880, arows13879]
  all_goals rfl

theorem atot13880 : totK PD2M8K2 D2M8K2.u13880 = [159085141884, 2318099179849, 6419626359087, 4723147416755, 716022478761, 19065934916, 0, 0] := by
  rw [show D2M8K2.u13880 = KTree.node D2M8K2.u13872 (nat_lit 30514900) (nat_lit 2774901383) (nat_lit 0) D2M8K2.u13879 from rfl, totK_node, atot13872, atot13879]
  decide +kernel

theorem arows13897 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13897 = true := by
  rw [show D2M8K2.u13897 = KTree.node D2M8K2.u13889 (nat_lit 30533767) (nat_lit 2377939237) (nat_lit 0) D2M8K2.u13896 from rfl, allE_node, arows13889, irow13897, arows13896]
  all_goals rfl

theorem atot13897 : totK PD2M8K2 D2M8K2.u13897 = [1499199388381, 5608320063292, 5767414922445, 1519292234992, 68882635676, 0, 0, 0] := by
  rw [show D2M8K2.u13897 = KTree.node D2M8K2.u13889 (nat_lit 30533767) (nat_lit 2377939237) (nat_lit 0) D2M8K2.u13896 from rfl, totK_node, atot13889, atot13896]
  decide +kernel

theorem arows13912 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13912 = true := by
  rw [show D2M8K2.u13912 = KTree.node D2M8K2.u13904 (nat_lit 30558844) (nat_lit 3208552075) (nat_lit 0) D2M8K2.u13911 from rfl, allE_node, arows13904, irow13912, arows13911]
  all_goals rfl

theorem atot13912 : totK PD2M8K2 D2M8K2.u13912 = [773699682448, 3983724264117, 6341631391661, 3034903730049, 324260258194, 4977114383, 0, 0] := by
  rw [show D2M8K2.u13912 = KTree.node D2M8K2.u13904 (nat_lit 30558844) (nat_lit 3208552075) (nat_lit 0) D2M8K2.u13911 from rfl, totK_node, atot13904, atot13911]
  decide +kernel

theorem arows13928 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13928 = true := by
  rw [show D2M8K2.u13928 = KTree.node D2M8K2.u13920 (nat_lit 30576601) (nat_lit 1357260598) (nat_lit 0) D2M8K2.u13927 from rfl, allE_node, arows13920, irow13928, arows13927]
  all_goals rfl

theorem atot13928 : totK PD2M8K2 D2M8K2.u13928 = [1273419804210, 5166100042425, 6106934431260, 1856692937816, 90967539770, 0, 0, 0] := by
  rw [show D2M8K2.u13928 = KTree.node D2M8K2.u13920 (nat_lit 30576601) (nat_lit 1357260598) (nat_lit 0) D2M8K2.u13927 from rfl, totK_node, atot13920, atot13927]
  decide +kernel

theorem arows13943 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13943 = true := by
  rw [show D2M8K2.u13943 = KTree.node D2M8K2.u13935 (nat_lit 30595805) (nat_lit 2232995411) (nat_lit 0) D2M8K2.u13942 from rfl, allE_node, arows13935, irow13943, arows13942]
  all_goals rfl

theorem atot13943 : totK PD2M8K2 D2M8K2.u13943 = [0, 1798603391163, 6251904050890, 5424393164324, 901461402482, 19545957871, 0, 0] := by
  rw [show D2M8K2.u13943 = KTree.node D2M8K2.u13935 (nat_lit 30595805) (nat_lit 2232995411) (nat_lit 0) D2M8K2.u13942 from rfl, totK_node, atot13935, atot13942]
  decide +kernel

theorem arows13961 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13961 = true := by
  rw [show D2M8K2.u13961 = KTree.node D2M8K2.u13953 (nat_lit 30656859) (nat_lit 3684992843) (nat_lit 0) D2M8K2.u13960 from rfl, allE_node, arows13953, irow13961, arows13960]
  all_goals rfl

theorem atot13961 : totK PD2M8K2 D2M8K2.u13961 = [0, 1691835200920, 5730706772511, 5512455117406, 1449813193121, 68466875824, 0, 0] := by
  rw [show D2M8K2.u13961 = KTree.node D2M8K2.u13953 (nat_lit 30656859) (nat_lit 3684992843) (nat_lit 0) D2M8K2.u13960 from rfl, totK_node, atot13953, atot13960]
  decide +kernel

theorem arows13976 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13976 = true := by
  rw [show D2M8K2.u13976 = KTree.node D2M8K2.u13968 (nat_lit 30674073) (nat_lit 1774750196) (nat_lit 0) D2M8K2.u13975 from rfl, allE_node, arows13968, irow13976, arows13975]
  all_goals rfl

theorem atot13976 : totK PD2M8K2 D2M8K2.u13976 = [0, 425933657684, 3052847300606, 6036182044454, 4008329027738, 845396649254, 41989737272, 0] := by
  rw [show D2M8K2.u13976 = KTree.node D2M8K2.u13968 (nat_lit 30674073) (nat_lit 1774750196) (nat_lit 0) D2M8K2.u13975 from rfl, totK_node, atot13968, atot13975]
  decide +kernel

theorem arows13992 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u13992 = true := by
  rw [show D2M8K2.u13992 = KTree.node D2M8K2.u13984 (nat_lit 30687944) (nat_lit 3699321969) (nat_lit 0) D2M8K2.u13991 from rfl, allE_node, arows13984, irow13992, arows13991]
  all_goals rfl

theorem atot13992 : totK PD2M8K2 D2M8K2.u13992 = [0, 754346683581, 3361389655544, 5611216051673, 3926243931246, 677179701384, 15657634319, 0] := by
  rw [show D2M8K2.u13992 = KTree.node D2M8K2.u13984 (nat_lit 30687944) (nat_lit 3699321969) (nat_lit 0) D2M8K2.u13991 from rfl, totK_node, atot13984, atot13991]
  decide +kernel

theorem arows14007 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14007 = true := by
  rw [show D2M8K2.u14007 = KTree.node D2M8K2.u13999 (nat_lit 30705435) (nat_lit 3745788549) (nat_lit 0) D2M8K2.u14006 from rfl, allE_node, arows13999, irow14007, arows14006]
  all_goals rfl

theorem atot14007 : totK PD2M8K2 D2M8K2.u14007 = [0, 1239149993863, 5158331311126, 6123313205368, 1791518657041, 81277680635, 0, 0] := by
  rw [show D2M8K2.u14007 = KTree.node D2M8K2.u13999 (nat_lit 30705435) (nat_lit 3745788549) (nat_lit 0) D2M8K2.u14006 from rfl, totK_node, atot13999, atot14006]
  decide +kernel

theorem arows14024 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14024 = true := by
  rw [show D2M8K2.u14024 = KTree.node D2M8K2.u14016 (nat_lit 30726964) (nat_lit 3551119300) (nat_lit 0) D2M8K2.u14023 from rfl, allE_node, arows14016, irow14024, arows14023]
  all_goals rfl

theorem atot14024 : totK PD2M8K2 D2M8K2.u14024 = [0, 754535350537, 3742081564472, 6087915645471, 3339746459152, 407749907206, 6546549506, 0] := by
  rw [show D2M8K2.u14024 = KTree.node D2M8K2.u14016 (nat_lit 30726964) (nat_lit 3551119300) (nat_lit 0) D2M8K2.u14023 from rfl, totK_node, atot14016, atot14023]
  decide +kernel

theorem arows14039 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14039 = true := by
  rw [show D2M8K2.u14039 = KTree.node D2M8K2.u14031 (nat_lit 30745813) (nat_lit 1250220224) (nat_lit 0) D2M8K2.u14038 from rfl, allE_node, arows14031, irow14039, arows14038]
  all_goals rfl

theorem atot14039 : totK PD2M8K2 D2M8K2.u14039 = [0, 1239508416406, 5211692699078, 6122354561392, 1779578958633, 82018189834, 0, 0] := by
  rw [show D2M8K2.u14039 = KTree.node D2M8K2.u14031 (nat_lit 30745813) (nat_lit 1250220224) (nat_lit 0) D2M8K2.u14038 from rfl, totK_node, atot14031, atot14038]
  decide +kernel

theorem arows14055 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14055 = true := by
  rw [show D2M8K2.u14055 = KTree.node D2M8K2.u14047 (nat_lit 30767458) (nat_lit 3820209302) (nat_lit 0) D2M8K2.u14054 from rfl, allE_node, arows14047, irow14055, arows14054]
  all_goals rfl

theorem atot14055 : totK PD2M8K2 D2M8K2.u14055 = [0, 496232549225, 3153544658494, 6344313904990, 3898690920008, 448473227405, 6624648996, 0] := by
  rw [show D2M8K2.u14055 = KTree.node D2M8K2.u14047 (nat_lit 30767458) (nat_lit 3820209302) (nat_lit 0) D2M8K2.u14054 from rfl, totK_node, atot14047, atot14054]
  decide +kernel

theorem arows14070 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14070 = true := by
  rw [show D2M8K2.u14070 = KTree.node D2M8K2.u14062 (nat_lit 30786214) (nat_lit 2011570061) (nat_lit 0) D2M8K2.u14069 from rfl, allE_node, arows14062, irow14070, arows14069]
  all_goals rfl

theorem atot14070 : totK PD2M8K2 D2M8K2.u14070 = [0, 1162051981040, 5074553121587, 6165507315463, 1897445464398, 99079720417, 0, 0] := by
  rw [show D2M8K2.u14070 = KTree.node D2M8K2.u14062 (nat_lit 30786214) (nat_lit 2011570061) (nat_lit 0) D2M8K2.u14069 from rfl, totK_node, atot14062, atot14069]
  decide +kernel

theorem arows14089 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14089 = true := by
  rw [show D2M8K2.u14089 = KTree.node D2M8K2.u14081 (nat_lit 30815545) (nat_lit 1527080184) (nat_lit 0) D2M8K2.u14088 from rfl, allE_node, arows14081, irow14089, arows14088]
  all_goals rfl

theorem atot14089 : totK PD2M8K2 D2M8K2.u14089 = [0, 1188568373986, 4639270568712, 5884992751878, 2498603444332, 233349637367, 1429815836, 0] := by
  rw [show D2M8K2.u14089 = KTree.node D2M8K2.u14081 (nat_lit 30815545) (nat_lit 1527080184) (nat_lit 0) D2M8K2.u14088 from rfl, totK_node, atot14081, atot14088]
  decide +kernel

theorem arows14104 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14104 = true := by
  rw [show D2M8K2.u14104 = KTree.node D2M8K2.u14096 (nat_lit 30832566) (nat_lit 3751687149) (nat_lit 0) D2M8K2.u14103 from rfl, allE_node, arows14096, irow14104, arows14103]
  all_goals rfl

theorem atot14104 : totK PD2M8K2 D2M8K2.u14104 = [0, 858551112672, 4632653489490, 6579419924126, 2280571763918, 119999559431, 0, 0] := by
  rw [show D2M8K2.u14104 = KTree.node D2M8K2.u14096 (nat_lit 30832566) (nat_lit 3751687149) (nat_lit 0) D2M8K2.u14103 from rfl, totK_node, atot14096, atot14103]
  decide +kernel

theorem arows14120 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14120 = true := by
  rw [show D2M8K2.u14120 = KTree.node D2M8K2.u14112 (nat_lit 30854376) (nat_lit 3313019272) (nat_lit 0) D2M8K2.u14119 from rfl, allE_node, arows14112, irow14120, arows14119]
  all_goals rfl

theorem atot14120 : totK PD2M8K2 D2M8K2.u14120 = [856534553545, 2863653322308, 3233037282559, 3689523944792, 3158392503975, 537986995740, 12189850367, 0] := by
  rw [show D2M8K2.u14120 = KTree.node D2M8K2.u14112 (nat_lit 30854376) (nat_lit 3313019272) (nat_lit 0) D2M8K2.u14119 from rfl, totK_node, atot14112, atot14119]
  decide +kernel

theorem arows14135 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14135 = true := by
  rw [show D2M8K2.u14135 = KTree.node D2M8K2.u14127 (nat_lit 30872672) (nat_lit 3092414250) (nat_lit 0) D2M8K2.u14134 from rfl, allE_node, arows14127, irow14135, arows14134]
  all_goals rfl

theorem atot14135 : totK PD2M8K2 D2M8K2.u14135 = [1120017607156, 4658687483376, 5939993438989, 2274592521313, 210648945722, 1369150432, 0, 0] := by
  rw [show D2M8K2.u14135 = KTree.node D2M8K2.u14127 (nat_lit 30872672) (nat_lit 3092414250) (nat_lit 0) D2M8K2.u14134 from rfl, totK_node, atot14127, atot14134]
  decide +kernel

theorem arows14152 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14152 = true := by
  rw [show D2M8K2.u14152 = KTree.node D2M8K2.u14144 (nat_lit 30894888) (nat_lit 3442028263) (nat_lit 0) D2M8K2.u14151 from rfl, allE_node, arows14144, irow14152, arows14151]
  all_goals rfl

theorem atot14152 : totK PD2M8K2 D2M8K2.u14152 = [867496502247, 4327730696135, 6509492679946, 2599270245262, 141034070134, 0, 0, 0] := by
  rw [show D2M8K2.u14152 = KTree.node D2M8K2.u14144 (nat_lit 30894888) (nat_lit 3442028263) (nat_lit 0) D2M8K2.u14151 from rfl, totK_node, atot14144, atot14151]
  decide +kernel

theorem arows14167 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14167 = true := by
  rw [show D2M8K2.u14167 = KTree.node D2M8K2.u14159 (nat_lit 30914011) (nat_lit 2186329530) (nat_lit 0) D2M8K2.u14166 from rfl, allE_node, arows14159, irow14167, arows14166]
  all_goals rfl

theorem atot14167 : totK PD2M8K2 D2M8K2.u14167 = [1133597771793, 4704573034857, 5894308500903, 2391191641167, 410400977169, 26904681413, 0, 0] := by
  rw [show D2M8K2.u14167 = KTree.node D2M8K2.u14159 (nat_lit 30914011) (nat_lit 2186329530) (nat_lit 0) D2M8K2.u14166 from rfl, totK_node, atot14159, atot14166]
  decide +kernel

theorem arows14183 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14183 = true := by
  rw [show D2M8K2.u14183 = KTree.node D2M8K2.u14175 (nat_lit 30931004) (nat_lit 2711067808) (nat_lit 0) D2M8K2.u14182 from rfl, allE_node, arows14175, irow14183, arows14182]
  all_goals rfl

theorem atot14183 : totK PD2M8K2 D2M8K2.u14183 = [108461727635, 1797361913893, 5770723855250, 5576538376848, 1197000749725, 30065390301, 0, 0] := by
  rw [show D2M8K2.u14183 = KTree.node D2M8K2.u14175 (nat_lit 30931004) (nat_lit 2711067808) (nat_lit 0) D2M8K2.u14182 from rfl, totK_node, atot14175, atot14182]
  decide +kernel

theorem arows14198 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14198 = true := by
  rw [show D2M8K2.u14198 = KTree.node D2M8K2.u14190 (nat_lit 30945089) (nat_lit 2222245322) (nat_lit 0) D2M8K2.u14197 from rfl, allE_node, arows14190, irow14198, arows14197]
  all_goals rfl

theorem atot14198 : totK PD2M8K2 D2M8K2.u14198 = [1581574276611, 5736227948773, 5684737474487, 1349239975964, 56791237187, 0, 0, 0] := by
  rw [show D2M8K2.u14198 = KTree.node D2M8K2.u14190 (nat_lit 30945089) (nat_lit 2222245322) (nat_lit 0) D2M8K2.u14197 from rfl, totK_node, atot14190, atot14197]
  decide +kernel

theorem arows14216 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14216 = true := by
  rw [show D2M8K2.u14216 = KTree.node D2M8K2.u14208 (nat_lit 30962665) (nat_lit 674866401) (nat_lit 0) D2M8K2.u14215 from rfl, allE_node, arows14208, irow14216, arows14215]
  all_goals rfl

theorem atot14216 : totK PD2M8K2 D2M8K2.u14216 = [413128340692, 3093434427411, 6410948061467, 3844152242055, 517557784980, 14222663156, 0, 0] := by
  rw [show D2M8K2.u14216 = KTree.node D2M8K2.u14208 (nat_lit 30962665) (nat_lit 674866401) (nat_lit 0) D2M8K2.u14215 from rfl, totK_node, atot14208, atot14215]
  decide +kernel

theorem arows14231 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14231 = true := by
  rw [show D2M8K2.u14231 = KTree.node D2M8K2.u14223 (nat_lit 31024869) (nat_lit 1484011954) (nat_lit 0) D2M8K2.u14230 from rfl, allE_node, arows14223, irow14231, arows14230]
  all_goals rfl

theorem atot14231 : totK PD2M8K2 D2M8K2.u14231 = [1227212795503, 4749084266327, 5732515423691, 2386026497150, 248934877654, 4574395652, 0, 0] := by
  rw [show D2M8K2.u14231 = KTree.node D2M8K2.u14223 (nat_lit 31024869) (nat_lit 1484011954) (nat_lit 0) D2M8K2.u14230 from rfl, totK_node, atot14223, atot14230]
  decide +kernel

theorem arows14247 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14247 = true := by
  rw [show D2M8K2.u14247 = KTree.node D2M8K2.u14239 (nat_lit 31045634) (nat_lit 4134394906) (nat_lit 0) D2M8K2.u14246 from rfl, allE_node, arows14239, irow14247, arows14246]
  all_goals rfl

theorem atot14247 : totK PD2M8K2 D2M8K2.u14247 = [424157580399, 3271287400930, 6645374719258, 3565053511742, 347317432635, 2233351729, 0, 0] := by
  rw [show D2M8K2.u14247 = KTree.node D2M8K2.u14239 (nat_lit 31045634) (nat_lit 4134394906) (nat_lit 0) D2M8K2.u14246 from rfl, totK_node, atot14239, atot14246]
  decide +kernel

theorem arows14262 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14262 = true := by
  rw [show D2M8K2.u14262 = KTree.node D2M8K2.u14254 (nat_lit 31069162) (nat_lit 3970051473) (nat_lit 0) D2M8K2.u14261 from rfl, allE_node, arows14254, irow14262, arows14261]
  all_goals rfl

theorem atot14262 : totK PD2M8K2 D2M8K2.u14262 = [1618228349563, 5710859816622, 5593689198205, 1460341273924, 131696722771, 3882006667, 0, 0] := by
  rw [show D2M8K2.u14262 = KTree.node D2M8K2.u14254 (nat_lit 31069162) (nat_lit 3970051473) (nat_lit 0) D2M8K2.u14261 from rfl, totK_node, atot14254, atot14261]
  decide +kernel

theorem arows14279 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14279 = true := by
  rw [show D2M8K2.u14279 = KTree.node D2M8K2.u14271 (nat_lit 31086555) (nat_lit 3425562994) (nat_lit 0) D2M8K2.u14278 from rfl, allE_node, arows14271, irow14279, arows14278]
  all_goals rfl

theorem atot14279 : totK PD2M8K2 D2M8K2.u14279 = [424455604040, 3156918847622, 6481864124908, 3935029983823, 447948382403, 6190125969, 0, 0] := by
  rw [show D2M8K2.u14279 = KTree.node D2M8K2.u14271 (nat_lit 31086555) (nat_lit 3425562994) (nat_lit 0) D2M8K2.u14278 from rfl, totK_node, atot14271, atot14278]
  decide +kernel

theorem arows14294 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14294 = true := by
  rw [show D2M8K2.u14294 = KTree.node D2M8K2.u14286 (nat_lit 31105573) (nat_lit 1367397861) (nat_lit 0) D2M8K2.u14293 from rfl, allE_node, arows14286, irow14294, arows14293]
  all_goals rfl

theorem atot14294 : totK PD2M8K2 D2M8K2.u14294 = [0, 1621552168641, 5877465816037, 5597935839640, 1165199819651, 42299523770, 0, 0] := by
  rw [show D2M8K2.u14294 = KTree.node D2M8K2.u14286 (nat_lit 31105573) (nat_lit 1367397861) (nat_lit 0) D2M8K2.u14293 from rfl, totK_node, atot14286, atot14293]
  decide +kernel

theorem arows14310 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14310 = true := by
  rw [show D2M8K2.u14310 = KTree.node D2M8K2.u14302 (nat_lit 31124494) (nat_lit 4009919491) (nat_lit 0) D2M8K2.u14309 from rfl, allE_node, arows14302, irow14310, arows14309]
  all_goals rfl

theorem atot14310 : totK PD2M8K2 D2M8K2.u14310 = [0, 793484814992, 4353156393826, 6506126093483, 2322023350887, 164985161863, 1275377855, 0] := by
  rw [show D2M8K2.u14310 = KTree.node D2M8K2.u14302 (nat_lit 31124494) (nat_lit 4009919491) (nat_lit 0) D2M8K2.u14309 from rfl, totK_node, atot14302, atot14309]
  decide +kernel

theorem arows14325 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14325 = true := by
  rw [show D2M8K2.u14325 = KTree.node D2M8K2.u14317 (nat_lit 31152382) (nat_lit 3859415176) (nat_lit 0) D2M8K2.u14324 from rfl, allE_node, arows14317, irow14325, arows14324]
  all_goals rfl

theorem atot14325 : totK PD2M8K2 D2M8K2.u14325 = [0, 1339005908609, 5281012845699, 6047225992108, 1754991195466, 83527373602, 0, 0] := by
  rw [show D2M8K2.u14325 = KTree.node D2M8K2.u14317 (nat_lit 31152382) (nat_lit 3859415176) (nat_lit 0) D2M8K2.u14324 from rfl, totK_node, atot14317, atot14324]
  decide +kernel

theorem arows14347 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14347 = true := by
  rw [show D2M8K2.u14347 = KTree.node D2M8K2.u14339 (nat_lit 31187907) (nat_lit 2022206094) (nat_lit 0) D2M8K2.u14346 from rfl, allE_node, arows14339, irow14347, arows14346]
  all_goals rfl

theorem atot14347 : totK PD2M8K2 D2M8K2.u14347 = [0, 1671284575737, 5907207509481, 5594748462780, 1245846857321, 47095271999, 0, 0] := by
  rw [show D2M8K2.u14347 = KTree.node D2M8K2.u14339 (nat_lit 31187907) (nat_lit 2022206094) (nat_lit 0) D2M8K2.u14346 from rfl, totK_node, atot14339, atot14346]
  decide +kernel

theorem arows14362 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14362 = true := by
  rw [show D2M8K2.u14362 = KTree.node D2M8K2.u14354 (nat_lit 31204760) (nat_lit 3754315224) (nat_lit 0) D2M8K2.u14361 from rfl, allE_node, arows14354, irow14362, arows14361]
  all_goals rfl

theorem atot14362 : totK PD2M8K2 D2M8K2.u14362 = [0, 1091379742691, 4735445972232, 6085095855183, 2155231278388, 171355220462, 1206465782, 0] := by
  rw [show D2M8K2.u14362 = KTree.node D2M8K2.u14354 (nat_lit 31204760) (nat_lit 3754315224) (nat_lit 0) D2M8K2.u14361 from rfl, totK_node, atot14354, atot14361]
  decide +kernel

theorem arows14378 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14378 = true := by
  rw [show D2M8K2.u14378 = KTree.node D2M8K2.u14370 (nat_lit 31224108) (nat_lit 2848573874) (nat_lit 0) D2M8K2.u14377 from rfl, allE_node, arows14370, irow14378, arows14377]
  all_goals rfl

theorem atot14378 : totK PD2M8K2 D2M8K2.u14378 = [0, 749943018193, 3664867720637, 5915488575136, 3239761954804, 516729522718, 17590593026, 0] := by
  rw [show D2M8K2.u14378 = KTree.node D2M8K2.u14370 (nat_lit 31224108) (nat_lit 2848573874) (nat_lit 0) D2M8K2.u14377 from rfl, totK_node, atot14370, atot14377]
  decide +kernel

theorem arows14393 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14393 = true := by
  rw [show D2M8K2.u14393 = KTree.node D2M8K2.u14385 (nat_lit 31284720) (nat_lit 3666280895) (nat_lit 0) D2M8K2.u14392 from rfl, allE_node, arows14385, irow14393, arows14392]
  all_goals rfl

theorem atot14393 : totK PD2M8K2 D2M8K2.u14393 = [0, 897982296059, 4532158396959, 6422874117300, 2275789909597, 143525137224, 1103454931, 0] := by
  rw [show D2M8K2.u14393 = KTree.node D2M8K2.u14385 (nat_lit 31284720) (nat_lit 3666280895) (nat_lit 0) D2M8K2.u14392 from rfl, totK_node, atot14385, atot14392]
  decide +kernel

theorem arows14410 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14410 = true := by
  rw [show D2M8K2.u14410 = KTree.node D2M8K2.u14402 (nat_lit 31313952) (nat_lit 3719854113) (nat_lit 0) D2M8K2.u14409 from rfl, allE_node, arows14402, irow14410, arows14409]
  all_goals rfl

theorem atot14410 : totK PD2M8K2 D2M8K2.u14410 = [0, 1251655844296, 4777035851957, 5760005584152, 2252361284420, 226316244537, 4779662215, 0] := by
  rw [show D2M8K2.u14410 = KTree.node D2M8K2.u14402 (nat_lit 31313952) (nat_lit 3719854113) (nat_lit 0) D2M8K2.u14409 from rfl, totK_node, atot14402, atot14409]
  decide +kernel

theorem arows14425 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14425 = true := by
  rw [show D2M8K2.u14425 = KTree.node D2M8K2.u14417 (nat_lit 31331117) (nat_lit 1609235076) (nat_lit 0) D2M8K2.u14424 from rfl, allE_node, arows14417, irow14425, arows14424]
  all_goals rfl

theorem atot14425 : totK PD2M8K2 D2M8K2.u14425 = [758382914429, 3417424963406, 5481537570047, 3881478421320, 869852837851, 35630744579, 0, 0] := by
  rw [show D2M8K2.u14425 = KTree.node D2M8K2.u14417 (nat_lit 31331117) (nat_lit 1609235076) (nat_lit 0) D2M8K2.u14424 from rfl, totK_node, atot14417, atot14424]
  decide +kernel

theorem arows14441 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14441 = true := by
  rw [show D2M8K2.u14441 = KTree.node D2M8K2.u14433 (nat_lit 31370165) (nat_lit 2374301204) (nat_lit 0) D2M8K2.u14440 from rfl, allE_node, arows14433, irow14441, arows14440]
  all_goals rfl

theorem atot14441 : totK PD2M8K2 D2M8K2.u14441 = [1218362405256, 4806962946757, 5849068578805, 2179535474987, 197811493452, 1369150432, 0, 0] := by
  rw [show D2M8K2.u14441 = KTree.node D2M8K2.u14433 (nat_lit 31370165) (nat_lit 2374301204) (nat_lit 0) D2M8K2.u14440 from rfl, totK_node, atot14433, atot14440]
  decide +kernel

theorem arows14456 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14456 = true := by
  rw [show D2M8K2.u14456 = KTree.node D2M8K2.u14448 (nat_lit 31392361) (nat_lit 1485375384) (nat_lit 0) D2M8K2.u14455 from rfl, allE_node, arows14448, irow14456, arows14455]
  all_goals rfl

theorem atot14456 : totK PD2M8K2 D2M8K2.u14456 = [774308869471, 4219336347426, 6639169586304, 2689377726406, 155172048195, 0, 0, 0] := by
  rw [show D2M8K2.u14456 = KTree.node D2M8K2.u14448 (nat_lit 31392361) (nat_lit 1485375384) (nat_lit 0) D2M8K2.u14455 from rfl, totK_node, atot14448, atot14455]
  decide +kernel

theorem arows14474 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14474 = true := by
  rw [show D2M8K2.u14474 = KTree.node D2M8K2.u14466 (nat_lit 31411163) (nat_lit 590533056) (nat_lit 0) D2M8K2.u14473 from rfl, allE_node, arows14466, irow14474, arows14473]
  all_goals rfl

theorem atot14474 : totK PD2M8K2 D2M8K2.u14474 = [1227008250617, 4902382641826, 5848025964534, 2184856153853, 344577778801, 25191558099, 0, 0] := by
  rw [show D2M8K2.u14474 = KTree.node D2M8K2.u14466 (nat_lit 31411163) (nat_lit 590533056) (nat_lit 0) D2M8K2.u14473 from rfl, totK_node, atot14466, atot14473]
  decide +kernel

theorem arows14489 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14489 = true := by
  rw [show D2M8K2.u14489 = KTree.node D2M8K2.u14481 (nat_lit 31428485) (nat_lit 1016795184) (nat_lit 0) D2M8K2.u14488 from rfl, allE_node, arows14481, irow14489, arows14488]
  all_goals rfl

theorem atot14489 : totK PD2M8K2 D2M8K2.u14489 = [71933061318, 1653765809287, 5758204487062, 5713341675123, 1254513407656, 32826569844, 0, 0] := by
  rw [show D2M8K2.u14489 = KTree.node D2M8K2.u14481 (nat_lit 31428485) (nat_lit 1016795184) (nat_lit 0) D2M8K2.u14488 from rfl, totK_node, atot14481, atot14488]
  decide +kernel

theorem arows14505 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14505 = true := by
  rw [show D2M8K2.u14505 = KTree.node D2M8K2.u14497 (nat_lit 31484043) (nat_lit 3733603620) (nat_lit 0) D2M8K2.u14504 from rfl, allE_node, arows14497, irow14505, arows14504]
  all_goals rfl

theorem atot14505 : totK PD2M8K2 D2M8K2.u14505 = [1610949211955, 5852131922536, 5634346419316, 1284232691783, 53105194181, 0, 0, 0] := by
  rw [show D2M8K2.u14505 = KTree.node D2M8K2.u14497 (nat_lit 31484043) (nat_lit 3733603620) (nat_lit 0) D2M8K2.u14504 from rfl, totK_node, atot14497, atot14504]
  decide +kernel

theorem arows14520 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14520 = true := by
  rw [show D2M8K2.u14520 = KTree.node D2M8K2.u14512 (nat_lit 31501162) (nat_lit 3989806208) (nat_lit 0) D2M8K2.u14519 from rfl, allE_node, arows14512, irow14520, arows14519]
  all_goals rfl

theorem atot14520 : totK PD2M8K2 D2M8K2.u14520 = [424393285092, 3042047670761, 6364236631728, 3919742264055, 529804289807, 14345316470, 0, 0] := by
  rw [show D2M8K2.u14520 = KTree.node D2M8K2.u14512 (nat_lit 31501162) (nat_lit 3989806208) (nat_lit 0) D2M8K2.u14519 from rfl, totK_node, atot14512, atot14519]
  decide +kernel

theorem arows14537 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14537 = true := by
  rw [show D2M8K2.u14537 = KTree.node D2M8K2.u14529 (nat_lit 31521685) (nat_lit 1241005059) (nat_lit 0) D2M8K2.u14536 from rfl, allE_node, arows14529, irow14537, arows14536]
  all_goals rfl

theorem atot14537 : totK PD2M8K2 D2M8K2.u14537 = [1227472386314, 4763177773837, 5753044238405, 2395564354112, 252583470443, 4720618446, 0, 0] := by
  rw [show D2M8K2.u14537 = KTree.node D2M8K2.u14529 (nat_lit 31521685) (nat_lit 1241005059) (nat_lit 0) D2M8K2.u14536 from rfl, totK_node, atot14529, atot14536]
  decide +kernel

theorem arows14552 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14552 = true := by
  rw [show D2M8K2.u14552 = KTree.node D2M8K2.u14544 (nat_lit 31542414) (nat_lit 3955710005) (nat_lit 0) D2M8K2.u14551 from rfl, allE_node, arows14544, irow14552, arows14551]
  all_goals rfl

theorem atot14552 : totK PD2M8K2 D2M8K2.u14552 = [424188206739, 3336114051182, 6694006762889, 3478588006844, 325593534051, 2233351729, 0, 0] := by
  rw [show D2M8K2.u14552 = KTree.node D2M8K2.u14544 (nat_lit 31542414) (nat_lit 3955710005) (nat_lit 0) D2M8K2.u14551 from rfl, totK_node, atot14544, atot14551]
  decide +kernel

theorem arows14568 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14568 = true := by
  rw [show D2M8K2.u14568 = KTree.node D2M8K2.u14560 (nat_lit 31566500) (nat_lit 3174394906) (nat_lit 0) D2M8K2.u14567 from rfl, allE_node, arows14560, irow14568, arows14567]
  all_goals rfl

theorem atot14568 : totK PD2M8K2 D2M8K2.u14568 = [1599812268301, 5608554417967, 5550031073370, 1596979159818, 158020151568, 3882006667, 0, 0] := by
  rw [show D2M8K2.u14568 = KTree.node D2M8K2.u14560 (nat_lit 31566500) (nat_lit 3174394906) (nat_lit 0) D2M8K2.u14567 from rfl, totK_node, atot14560, atot14567]
  decide +kernel

theorem arows14583 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14583 = true := by
  rw [show D2M8K2.u14583 = KTree.node D2M8K2.u14575 (nat_lit 31583663) (nat_lit 2180194614) (nat_lit 0) D2M8K2.u14582 from rfl, allE_node, arows14575, irow14583, arows14582]
  all_goals rfl

theorem atot14583 : totK PD2M8K2 D2M8K2.u14583 = [443036656631, 3230087757121, 6489913744218, 3855791134818, 442611987035, 6190125969, 0, 0] := by
  rw [show D2M8K2.u14583 = KTree.node D2M8K2.u14575 (nat_lit 31583663) (nat_lit 2180194614) (nat_lit 0) D2M8K2.u14582 from rfl, totK_node, atot14575, atot14582]
  decide +kernel

theorem arows14602 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14602 = true := by
  rw [show D2M8K2.u14602 = KTree.node D2M8K2.u14594 (nat_lit 31602987) (nat_lit 2143697449) (nat_lit 0) D2M8K2.u14601 from rfl, allE_node, arows14594, irow14602, arows14601]
  all_goals rfl

theorem atot14602 : totK PD2M8K2 D2M8K2.u14602 = [0, 1653014370841, 6048533225515, 5560051449105, 1028294563585, 30414116156, 0, 0] := by
  rw [show D2M8K2.u14602 = KTree.node D2M8K2.u14594 (nat_lit 31602987) (nat_lit 2143697449) (nat_lit 0) D2M8K2.u14601 from rfl, totK_node, atot14594, atot14601]
  decide +kernel

theorem arows14617 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14617 = true := by
  rw [show D2M8K2.u14617 = KTree.node D2M8K2.u14609 (nat_lit 31621614) (nat_lit 4079165587) (nat_lit 0) D2M8K2.u14616 from rfl, allE_node, arows14609, irow14617, arows14616]
  all_goals rfl

theorem atot14617 : totK PD2M8K2 D2M8K2.u14617 = [0, 794504379502, 4223864462098, 6463029162482, 2452778098376, 175204562414, 1310517177, 0] := by
  rw [show D2M8K2.u14617 = KTree.node D2M8K2.u14609 (nat_lit 31621614) (nat_lit 4079165587) (nat_lit 0) D2M8K2.u14616 from rfl, totK_node, atot14609, atot14616]
  decide +kernel

theorem arows14633 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14633 = true := by
  rw [show D2M8K2.u14633 = KTree.node D2M8K2.u14625 (nat_lit 31649576) (nat_lit 3942464715) (nat_lit 0) D2M8K2.u14632 from rfl, allE_node, arows14625, irow14633, arows14632]
  all_goals rfl

theorem atot14633 : totK PD2M8K2 D2M8K2.u14633 = [0, 1198608178547, 5060871439323, 6206072237355, 1907418150727, 91193168967, 0, 0] := by
  rw [show D2M8K2.u14633 = KTree.node D2M8K2.u14625 (nat_lit 31649576) (nat_lit 3942464715) (nat_lit 0) D2M8K2.u14632 from rfl, totK_node, atot14625, atot14632]
  decide +kernel

theorem arows14648 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14648 = true := by
  rw [show D2M8K2.u14648 = KTree.node D2M8K2.u14640 (nat_lit 31726197) (nat_lit 1737201167) (nat_lit 0) D2M8K2.u14647 from rfl, allE_node, arows14640, irow14648, arows14647]
  all_goals rfl

theorem atot14648 : totK PD2M8K2 D2M8K2.u14648 = [0, 1636629711083, 5825046871785, 5633463187714, 1290218714738, 48079679568, 0, 0] := by
  rw [show D2M8K2.u14648 = KTree.node D2M8K2.u14640 (nat_lit 31726197) (nat_lit 1737201167) (nat_lit 0) D2M8K2.u14647 from rfl, totK_node, atot14640, atot14647]
  decide +kernel

theorem arows14665 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14665 = true := by
  rw [show D2M8K2.u14665 = KTree.node D2M8K2.u14657 (nat_lit 31742940) (nat_lit 2904797078) (nat_lit 0) D2M8K2.u14664 from rfl, allE_node, arows14657, irow14665, arows14664]
  all_goals rfl

theorem atot14665 : totK PD2M8K2 D2M8K2.u14665 = [0, 1267933769246, 4932146730513, 5845843052034, 2034701510274, 160648241085, 1217496766, 0] := by
  rw [show D2M8K2.u14665 = KTree.node D2M8K2.u14657 (nat_lit 31742940) (nat_lit 2904797078) (nat_lit 0) D2M8K2.u14664 from rfl, totK_node, atot14657, atot14664]
  decide +kernel

theorem arows14680 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14680 = true := by
  rw [show D2M8K2.u14680 = KTree.node D2M8K2.u14672 (nat_lit 31761854) (nat_lit 3781039000) (nat_lit 0) D2M8K2.u14679 from rfl, allE_node, arows14672, irow14680, arows14679]
  all_goals rfl

theorem atot14680 : totK PD2M8K2 D2M8K2.u14680 = [0, 542119350841, 3348667951581, 6193121935292, 3510574891479, 543090347752, 17736366219, 0] := by
  rw [show D2M8K2.u14680 = KTree.node D2M8K2.u14672 (nat_lit 31761854) (nat_lit 3781039000) (nat_lit 0) D2M8K2.u14679 from rfl, totK_node, atot14672, atot14679]
  decide +kernel

theorem arows14696 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14696 = true := by
  rw [show D2M8K2.u14696 = KTree.node D2M8K2.u14688 (nat_lit 31781644) (nat_lit 2586741991) (nat_lit 0) D2M8K2.u14695 from rfl, allE_node, arows14688, irow14696, arows14695]
  all_goals rfl

theorem atot14696 : totK PD2M8K2 D2M8K2.u14696 = [0, 1107589045217, 4837959797989, 6111665717333, 2106026999245, 135591005206, 1138244013, 0] := by
  rw [show D2M8K2.u14696 = KTree.node D2M8K2.u14688 (nat_lit 31781644) (nat_lit 2586741991) (nat_lit 0) D2M8K2.u14695 from rfl, totK_node, atot14688, atot14695]
  decide +kernel

theorem arows14711 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14711 = true := by
  rw [show D2M8K2.u14711 = KTree.node D2M8K2.u14703 (nat_lit 31810329) (nat_lit 1829496000) (nat_lit 0) D2M8K2.u14710 from rfl, allE_node, arows14703, irow14711, arows14710]
  all_goals rfl

theorem atot14711 : totK PD2M8K2 D2M8K2.u14711 = [0, 1085848686297, 4534962710313, 5961325533870, 2455148565701, 243971822299, 4914284239, 0] := by
  rw [show D2M8K2.u14711 = KTree.node D2M8K2.u14703 (nat_lit 31810329) (nat_lit 1829496000) (nat_lit 0) D2M8K2.u14710 from rfl, totK_node, atot14703, atot14710]
  decide +kernel

theorem arows14729 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14729 = true := by
  rw [show D2M8K2.u14729 = KTree.node D2M8K2.u14721 (nat_lit 31827760) (nat_lit 3348375543) (nat_lit 0) D2M8K2.u14728 from rfl, allE_node, arows14721, irow14729, arows14728]
  all_goals rfl

theorem atot14729 : totK PD2M8K2 D2M8K2.u14729 = [755379393932, 3229426205828, 5312027086361, 4146301490942, 993837352197, 40338621816, 0, 0] := by
  rw [show D2M8K2.u14729 = KTree.node D2M8K2.u14721 (nat_lit 31827760) (nat_lit 3348375543) (nat_lit 0) D2M8K2.u14728 from rfl, totK_node, atot14721, atot14728]
  decide +kernel

theorem arows14744 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14744 = true := by
  rw [show D2M8K2.u14744 = KTree.node D2M8K2.u14736 (nat_lit 32363146) (nat_lit 2879695581) (nat_lit 0) D2M8K2.u14743 from rfl, allE_node, arows14736, irow14744, arows14743]
  all_goals rfl

theorem atot14744 : totK PD2M8K2 D2M8K2.u14744 = [1248359448182, 5212126564468, 6047494427766, 1683300535623, 75146767824, 0, 0, 0] := by
  rw [show D2M8K2.u14744 = KTree.node D2M8K2.u14736 (nat_lit 32363146) (nat_lit 2879695581) (nat_lit 0) D2M8K2.u14743 from rfl, totK_node, atot14736, atot14743]
  decide +kernel

theorem arows14760 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14760 = true := by
  rw [show D2M8K2.u14760 = KTree.node D2M8K2.u14752 (nat_lit 32384124) (nat_lit 2954287894) (nat_lit 0) D2M8K2.u14759 from rfl, allE_node, arows14752, irow14760, arows14759]
  all_goals rfl

theorem atot14760 : totK PD2M8K2 D2M8K2.u14760 = [601719591565, 3613534956320, 6582534819779, 3312819690027, 284986368581, 1369150432, 0, 0] := by
  rw [show D2M8K2.u14760 = KTree.node D2M8K2.u14752 (nat_lit 32384124) (nat_lit 2954287894) (nat_lit 0) D2M8K2.u14759 from rfl, totK_node, atot14752, atot14759]
  decide +kernel

theorem arows14775 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14775 = true := by
  rw [show D2M8K2.u14775 = KTree.node D2M8K2.u14767 (nat_lit 32404097) (nat_lit 2224194006) (nat_lit 0) D2M8K2.u14774 from rfl, allE_node, arows14767, irow14775, arows14774]
  all_goals rfl

theorem atot14775 : totK PD2M8K2 D2M8K2.u14775 = [1429471031326, 5525082074738, 5933404484535, 1568719200611, 79223312222, 0, 0, 0] := by
  rw [show D2M8K2.u14775 = KTree.node D2M8K2.u14767 (nat_lit 32404097) (nat_lit 2224194006) (nat_lit 0) D2M8K2.u14774 from rfl, totK_node, atot14767, atot14774]
  decide +kernel

theorem arows14792 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14792 = true := by
  rw [show D2M8K2.u14792 = KTree.node D2M8K2.u14784 (nat_lit 32421203) (nat_lit 2728513855) (nat_lit 0) D2M8K2.u14791 from rfl, allE_node, arows14784, irow14792, arows14791]
  all_goals rfl

theorem atot14792 : totK PD2M8K2 D2M8K2.u14792 = [0, 1673251944257, 5946373951789, 5577498709456, 1240927029270, 48715757244, 0, 0] := by
  rw [show D2M8K2.u14792 = KTree.node D2M8K2.u14784 (nat_lit 32421203) (nat_lit 2728513855) (nat_lit 0) D2M8K2.u14791 from rfl, totK_node, atot14784, atot14791]
  decide +kernel

theorem arows14807 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14807 = true := by
  rw [show D2M8K2.u14807 = KTree.node D2M8K2.u14799 (nat_lit 32436149) (nat_lit 1813637861) (nat_lit 0) D2M8K2.u14806 from rfl, allE_node, arows14799, irow14807, arows14806]
  all_goals rfl

theorem atot14807 : totK PD2M8K2 D2M8K2.u14807 = [1517608550593, 5153901558401, 5339993423299, 2108133368306, 337596134731, 9302370699, 0, 0] := by
  rw [show D2M8K2.u14807 = KTree.node D2M8K2.u14799 (nat_lit 32436149) (nat_lit 1813637861) (nat_lit 0) D2M8K2.u14806 from rfl, totK_node, atot14799, atot14806]
  decide +kernel

theorem arows14823 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14823 = true := by
  rw [show D2M8K2.u14823 = KTree.node D2M8K2.u14815 (nat_lit 32453286) (nat_lit 3670019927) (nat_lit 0) D2M8K2.u14822 from rfl, allE_node, arows14815, irow14823, arows14822]
  all_goals rfl

theorem atot14823 : totK PD2M8K2 D2M8K2.u14823 = [500634718716, 3363759042439, 6369611778474, 3560785090155, 486945757594, 14222663156, 0, 0] := by
  rw [show D2M8K2.u14823 = KTree.node D2M8K2.u14815 (nat_lit 32453286) (nat_lit 3670019927) (nat_lit 0) D2M8K2.u14822 from rfl, totK_node, atot14815, atot14822]
  decide +kernel

theorem arows14838 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14838 = true := by
  rw [show D2M8K2.u14838 = KTree.node D2M8K2.u14830 (nat_lit 32474426) (nat_lit 2912530576) (nat_lit 0) D2M8K2.u14837 from rfl, allE_node, arows14830, irow14838, arows14837]
  all_goals rfl

theorem atot14838 : totK PD2M8K2 D2M8K2.u14838 = [1265953108975, 4742070525141, 5700227253119, 2461718418360, 260178942910, 4574395652, 0, 0] := by
  rw [show D2M8K2.u14838 = KTree.node D2M8K2.u14830 (nat_lit 32474426) (nat_lit 2912530576) (nat_lit 0) D2M8K2.u14837 from rfl, totK_node, atot14830, atot14837]
  decide +kernel

theorem arows14858 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14858 = true := by
  rw [show D2M8K2.u14858 = KTree.node D2M8K2.u14850 (nat_lit 32491910) (nat_lit 4180403854) (nat_lit 0) D2M8K2.u14857 from rfl, allE_node, arows14850, irow14858, arows14857]
  all_goals rfl

theorem atot14858 : totK PD2M8K2 D2M8K2.u14858 = [752797281591, 4159115934286, 6511376143519, 2746598340483, 213235512454, 1239866073, 0, 0] := by
  rw [show D2M8K2.u14858 = KTree.node D2M8K2.u14850 (nat_lit 32491910) (nat_lit 4180403854) (nat_lit 0) D2M8K2.u14857 from rfl, totK_node, atot14850, atot14857]
  decide +kernel

theorem arows14873 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14873 = true := by
  rw [show D2M8K2.u14873 = KTree.node D2M8K2.u14865 (nat_lit 32511494) (nat_lit 4125181146) (nat_lit 0) D2M8K2.u14872 from rfl, allE_node, arows14865, irow14873, arows14872]
  all_goals rfl

theorem atot14873 : totK PD2M8K2 D2M8K2.u14873 = [844463631107, 3800184175413, 5784111556685, 3384085641129, 552836154007, 17826068843, 0, 0] := by
  rw [show D2M8K2.u14873 = KTree.node D2M8K2.u14865 (nat_lit 32511494) (nat_lit 4125181146) (nat_lit 0) D2M8K2.u14872 from rfl, totK_node, atot14865, atot14872]
  decide +kernel

theorem arows14889 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14889 = true := by
  rw [show D2M8K2.u14889 = KTree.node D2M8K2.u14881 (nat_lit 32567736) (nat_lit 3616749085) (nat_lit 0) D2M8K2.u14888 from rfl, allE_node, arows14881, irow14889, arows14888]
  all_goals rfl

theorem atot14889 : totK PD2M8K2 D2M8K2.u14889 = [1292464131673, 5205132742463, 6123379329314, 1779100401070, 71548455391, 0, 0, 0] := by
  rw [show D2M8K2.u14889 = KTree.node D2M8K2.u14881 (nat_lit 32567736) (nat_lit 3616749085) (nat_lit 0) D2M8K2.u14888 from rfl, totK_node, atot14881, atot14888]
  decide +kernel

theorem arows14904 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14904 = true := by
  rw [show D2M8K2.u14904 = KTree.node D2M8K2.u14896 (nat_lit 32586636) (nat_lit 3603715367) (nat_lit 0) D2M8K2.u14903 from rfl, allE_node, arows14896, irow14904, arows14903]
  all_goals rfl

theorem atot14904 : totK PD2M8K2 D2M8K2.u14904 = [0, 1763677066225, 6213219511251, 5468440659460, 903199676217, 19545957871, 0, 0] := by
  rw [show D2M8K2.u14904 = KTree.node D2M8K2.u14896 (nat_lit 32586636) (nat_lit 3603715367) (nat_lit 0) D2M8K2.u14903 from rfl, totK_node, atot14896, atot14903]
  decide +kernel

theorem arows14921 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14921 = true := by
  rw [show D2M8K2.u14921 = KTree.node D2M8K2.u14913 (nat_lit 32607408) (nat_lit 3613646958) (nat_lit 0) D2M8K2.u14920 from rfl, allE_node, arows14913, irow14921, arows14920]
  all_goals rfl

theorem atot14921 : totK PD2M8K2 D2M8K2.u14921 = [0, 1827814776120, 6197138887293, 5331583014763, 933216185672, 26194144004, 0, 0] := by
  rw [show D2M8K2.u14921 = KTree.node D2M8K2.u14913 (nat_lit 32607408) (nat_lit 3613646958) (nat_lit 0) D2M8K2.u14920 from rfl, totK_node, atot14913, atot14920]
  decide +kernel

theorem arows14936 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14936 = true := by
  rw [show D2M8K2.u14936 = KTree.node D2M8K2.u14928 (nat_lit 32625480) (nat_lit 3426994335) (nat_lit 0) D2M8K2.u14935 from rfl, allE_node, arows14928, irow14936, arows14935]
  all_goals rfl

theorem atot14936 : totK PD2M8K2 D2M8K2.u14936 = [0, 362470949035, 3373973730897, 7024465678719, 3157648408059, 215719617134, 1369150432, 0] := by
  rw [show D2M8K2.u14936 = KTree.node D2M8K2.u14928 (nat_lit 32625480) (nat_lit 3426994335) (nat_lit 0) D2M8K2.u14935 from rfl, totK_node, atot14928, atot14935]
  decide +kernel

theorem arows14952 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14952 = true := by
  rw [show D2M8K2.u14952 = KTree.node D2M8K2.u14944 (nat_lit 32648956) (nat_lit 3126240037) (nat_lit 0) D2M8K2.u14951 from rfl, allE_node, arows14944, irow14952, arows14951]
  all_goals rfl

theorem atot14952 : totK PD2M8K2 D2M8K2.u14952 = [0, 1667546588054, 5797952709935, 5625109690371, 1400875229333, 57177212067, 0, 0] := by
  rw [show D2M8K2.u14952 = KTree.node D2M8K2.u14944 (nat_lit 32648956) (nat_lit 3126240037) (nat_lit 0) D2M8K2.u14951 from rfl, totK_node, atot14944, atot14951]
  decide +kernel

theorem arows14967 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14967 = true := by
  rw [show D2M8K2.u14967 = KTree.node D2M8K2.u14959 (nat_lit 32684336) (nat_lit 3519590335) (nat_lit 0) D2M8K2.u14966 from rfl, allE_node, arows14959, irow14967, arows14966]
  all_goals rfl

theorem atot14967 : totK PD2M8K2 D2M8K2.u14967 = [0, 1523984213540, 5589679659440, 5723020144570, 1488852534275, 69114291539, 0, 0] := by
  rw [show D2M8K2.u14967 = KTree.node D2M8K2.u14959 (nat_lit 32684336) (nat_lit 3519590335) (nat_lit 0) D2M8K2.u14966 from rfl, totK_node, atot14959, atot14966]
  decide +kernel

theorem arows14985 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u14985 = true := by
  rw [show D2M8K2.u14985 = KTree.node D2M8K2.u14977 (nat_lit 32701450) (nat_lit 3884217855) (nat_lit 0) D2M8K2.u14984 from rfl, allE_node, arows14977, irow14985, arows14984]
  all_goals rfl

theorem atot14985 : totK PD2M8K2 D2M8K2.u14985 = [0, 672286054234, 3781407955912, 6328484143635, 3086740291994, 328552084436, 6301476269, 0] := by
  rw [show D2M8K2.u14985 = KTree.node D2M8K2.u14977 (nat_lit 32701450) (nat_lit 3884217855) (nat_lit 0) D2M8K2.u14984 from rfl, totK_node, atot14977, atot14984]
  decide +kernel

theorem arows15000 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15000 = true := by
  rw [show D2M8K2.u15000 = KTree.node D2M8K2.u14992 (nat_lit 32725487) (nat_lit 2140236870) (nat_lit 0) D2M8K2.u14999 from rfl, allE_node, arows14992, irow15000, arows14999]
  all_goals rfl

theorem atot15000 : totK PD2M8K2 D2M8K2.u15000 = [0, 1265062210594, 5158368070152, 6018845605466, 1828531846732, 95347543915, 0, 0] := by
  rw [show D2M8K2.u15000 = KTree.node D2M8K2.u14992 (nat_lit 32725487) (nat_lit 2140236870) (nat_lit 0) D2M8K2.u14999 from rfl, totK_node, atot14992, atot14999]
  decide +kernel

theorem arows15016 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15016 = true := by
  rw [show D2M8K2.u15016 = KTree.node D2M8K2.u15008 (nat_lit 32742298) (nat_lit 3826762833) (nat_lit 0) D2M8K2.u15015 from rfl, allE_node, arows15008, irow15016, arows15015]
  all_goals rfl

theorem atot15016 : totK PD2M8K2 D2M8K2.u15016 = [0, 751595623571, 3986462670342, 6344139053791, 2919335668674, 259571725088, 2335892675, 0] := by
  rw [show D2M8K2.u15016 = KTree.node D2M8K2.u15008 (nat_lit 32742298) (nat_lit 3826762833) (nat_lit 0) D2M8K2.u15015 from rfl, totK_node, atot15008, atot15015]
  decide +kernel

theorem arows15031 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15031 = true := by
  rw [show D2M8K2.u15031 = KTree.node D2M8K2.u15023 (nat_lit 32808217) (nat_lit 1208949132) (nat_lit 0) D2M8K2.u15030 from rfl, allE_node, arows15023, irow15031, arows15030]
  all_goals rfl

theorem atot15031 : totK PD2M8K2 D2M8K2.u15031 = [0, 1265384903141, 5113468478350, 5923848697893, 1904907542073, 158832461946, 4028038878, 0] := by
  rw [show D2M8K2.u15031 = KTree.node D2M8K2.u15023 (nat_lit 32808217) (nat_lit 1208949132) (nat_lit 0) D2M8K2.u15030 from rfl, totK_node, atot15023, atot15030]
  decide +kernel

theorem arows15048 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15048 = true := by
  rw [show D2M8K2.u15048 = KTree.node D2M8K2.u15040 (nat_lit 32824059) (nat_lit 3606563666) (nat_lit 0) D2M8K2.u15047 from rfl, allE_node, arows15040, irow15048, arows15047]
  all_goals rfl

theorem atot15048 : totK PD2M8K2 D2M8K2.u15048 = [0, 869639304998, 4306701795163, 6363728484042, 2601822186211, 205671396098, 1288491354, 0] := by
  rw [show D2M8K2.u15048 = KTree.node D2M8K2.u15040 (nat_lit 32824059) (nat_lit 3606563666) (nat_lit 0) D2M8K2.u15047 from rfl, totK_node, atot15040, atot15047]
  decide +kernel

theorem arows15063 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15063 = true := by
  rw [show D2M8K2.u15063 = KTree.node D2M8K2.u15055 (nat_lit 32843502) (nat_lit 3941302864) (nat_lit 0) D2M8K2.u15062 from rfl, allE_node, arows15055, irow15063, arows15062]
  all_goals rfl

theorem atot15063 : totK PD2M8K2 D2M8K2.u15063 = [0, 753166441893, 3301132224886, 5510806363506, 3830096567613, 774219421329, 31376465649, 0] := by
  rw [show D2M8K2.u15063 = KTree.node D2M8K2.u15055 (nat_lit 32843502) (nat_lit 3941302864) (nat_lit 0) D2M8K2.u15062 from rfl, totK_node, atot15055, atot15062]
  decide +kernel

theorem arows15079 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15079 = true := by
  rw [show D2M8K2.u15079 = KTree.node D2M8K2.u15071 (nat_lit 32860530) (nat_lit 3430439555) (nat_lit 0) D2M8K2.u15078 from rfl, allE_node, arows15071, irow15079, arows15078]
  all_goals rfl

theorem atot15079 : totK PD2M8K2 D2M8K2.u15079 = [0, 1343984441576, 5393272886018, 5967489791519, 1499289162459, 62940620160, 0, 0] := by
  rw [show D2M8K2.u15079 = KTree.node D2M8K2.u15071 (nat_lit 32860530) (nat_lit 3430439555) (nat_lit 0) D2M8K2.u15078 from rfl, totK_node, atot15071, atot15078]
  decide +kernel

theorem arows15094 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15094 = true := by
  rw [show D2M8K2.u15094 = KTree.node D2M8K2.u15086 (nat_lit 32881070) (nat_lit 3706066932) (nat_lit 0) D2M8K2.u15093 from rfl, allE_node, arows15086, irow15094, arows15093]
  all_goals rfl

theorem atot15094 : totK PD2M8K2 D2M8K2.u15094 = [0, 581874992973, 3667979097850, 6627241754919, 3075240252287, 256036413731, 1369150432, 0] := by
  rw [show D2M8K2.u15094 = KTree.node D2M8K2.u15086 (nat_lit 32881070) (nat_lit 3706066932) (nat_lit 0) D2M8K2.u15093 from rfl, totK_node, atot15086, atot15093]
  decide +kernel

theorem arows15113 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15113 = true := by
  rw [show D2M8K2.u15113 = KTree.node D2M8K2.u15105 (nat_lit 32943173) (nat_lit 2337965196) (nat_lit 0) D2M8K2.u15112 from rfl, allE_node, arows15105, irow15113, arows15112]
  all_goals rfl

theorem atot15113 : totK PD2M8K2 D2M8K2.u15113 = [0, 1397654668215, 5410976385098, 5906371559938, 1644851131532, 81932708148, 0, 0] := by
  rw [show D2M8K2.u15113 = KTree.node D2M8K2.u15105 (nat_lit 32943173) (nat_lit 2337965196) (nat_lit 0) D2M8K2.u15112 from rfl, totK_node, atot15105, atot15112]
  decide +kernel

theorem arows15128 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15128 = true := by
  rw [show D2M8K2.u15128 = KTree.node D2M8K2.u15120 (nat_lit 32959410) (nat_lit 1888166817) (nat_lit 2184) D2M8K2.u15127 from rfl, allE_node, arows15120, irow15128, arows15127]
  all_goals rfl

theorem atot15128 : totK PD2M8K2 D2M8K2.u15128 = [0, 419158787481, 3187536365989, 6526257526900, 3718840691297, 420777914564, 6601594569, 0] := by
  rw [show D2M8K2.u15128 = KTree.node D2M8K2.u15120 (nat_lit 32959410) (nat_lit 1888166817) (nat_lit 2184) D2M8K2.u15127 from rfl, totK_node, atot15120, atot15127]
  decide +kernel

theorem arows15144 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15144 = true := by
  rw [show D2M8K2.u15144 = KTree.node D2M8K2.u15136 (nat_lit 32983811) (nat_lit 2890378161) (nat_lit 0) D2M8K2.u15143 from rfl, allE_node, arows15136, irow15144, arows15143]
  all_goals rfl

theorem atot15144 : totK PD2M8K2 D2M8K2.u15144 = [0, 1564951096827, 5652588359474, 5762165751339, 1459620881490, 63794839350, 0, 0] := by
  rw [show D2M8K2.u15144 = KTree.node D2M8K2.u15136 (nat_lit 32983811) (nat_lit 2890378161) (nat_lit 0) D2M8K2.u15143 from rfl, totK_node, atot15136, atot15143]
  decide +kernel

theorem arows15159 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15159 = true := by
  rw [show D2M8K2.u15159 = KTree.node D2M8K2.u15151 (nat_lit 33003174) (nat_lit 3749681023) (nat_lit 0) D2M8K2.u15158 from rfl, allE_node, arows15151, irow15159, arows15158]
  all_goals rfl

theorem atot15159 : totK PD2M8K2 D2M8K2.u15159 = [0, 420637493945, 3076862189622, 6457130412268, 3918246142706, 449303738174, 6665697270, 0] := by
  rw [show D2M8K2.u15159 = KTree.node D2M8K2.u15151 (nat_lit 33003174) (nat_lit 3749681023) (nat_lit 0) D2M8K2.u15158 from rfl, totK_node, atot15151, atot15158]
  decide +kernel

theorem arows15176 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15176 = true := by
  rw [show D2M8K2.u15176 = KTree.node D2M8K2.u15168 (nat_lit 33024190) (nat_lit 3628795798) (nat_lit 0) D2M8K2.u15175 from rfl, allE_node, arows15168, irow15176, arows15175]
  all_goals rfl

theorem atot15176 : totK PD2M8K2 D2M8K2.u15176 = [0, 1224073644283, 5141830592140, 6072596678242, 1719524833920, 119833095531, 1138244013, 0] := by
  rw [show D2M8K2.u15176 = KTree.node D2M8K2.u15168 (nat_lit 33024190) (nat_lit 3628795798) (nat_lit 0) D2M8K2.u15175 from rfl, totK_node, atot15168, atot15175]
  decide +kernel

theorem arows15191 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15191 = true := by
  rw [show D2M8K2.u15191 = KTree.node D2M8K2.u15183 (nat_lit 33054068) (nat_lit 3146821927) (nat_lit 0) D2M8K2.u15190 from rfl, allE_node, arows15183, irow15191, arows15190]
  all_goals rfl

theorem atot15191 : totK PD2M8K2 D2M8K2.u15191 = [0, 1028028929009, 4615030728594, 6342037373525, 2322774058974, 122024167586, 0, 0] := by
  rw [show D2M8K2.u15191 = KTree.node D2M8K2.u15183 (nat_lit 33054068) (nat_lit 3146821927) (nat_lit 0) D2M8K2.u15190 from rfl, totK_node, atot15183, atot15190]
  decide +kernel

theorem arows15207 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15207 = true := by
  rw [show D2M8K2.u15207 = KTree.node D2M8K2.u15199 (nat_lit 33071244) (nat_lit 3023937196) (nat_lit 0) D2M8K2.u15206 from rfl, allE_node, arows15199, irow15207, arows15206]
  all_goals rfl

theorem atot15207 : totK PD2M8K2 D2M8K2.u15207 = [0, 1010969223297, 4520426051531, 6199801624462, 2515084567273, 197385062601, 1310285577, 0] := by
  rw [show D2M8K2.u15207 = KTree.node D2M8K2.u15199 (nat_lit 33071244) (nat_lit 3023937196) (nat_lit 0) D2M8K2.u15206 from rfl, totK_node, atot15199, atot15206]
  decide +kernel

theorem arows15222 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15222 = true := by
  rw [show D2M8K2.u15222 = KTree.node D2M8K2.u15214 (nat_lit 33087499) (nat_lit 1392170694) (nat_lit 0) D2M8K2.u15221 from rfl, allE_node, arows15214, irow15222, arows15221]
  all_goals rfl

theorem atot15222 : totK PD2M8K2 D2M8K2.u15222 = [0, 0, 1816356856204, 6230659429801, 5310253058927, 964216743293, 32931563536, 0] := by
  rw [show D2M8K2.u15222 = KTree.node D2M8K2.u15214 (nat_lit 33087499) (nat_lit 1392170694) (nat_lit 0) D2M8K2.u15221 from rfl, totK_node, atot15214, atot15221]
  decide +kernel

theorem arows15240 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15240 = true := by
  rw [show D2M8K2.u15240 = KTree.node D2M8K2.u15232 (nat_lit 33108240) (nat_lit 3342901075) (nat_lit 0) D2M8K2.u15239 from rfl, allE_node, arows15232, irow15240, arows15239]
  all_goals rfl

theorem atot15240 : totK PD2M8K2 D2M8K2.u15240 = [0, 0, 1646775375095, 6003473993727, 5647069559088, 950955480540, 33629503318, 0] := by
  rw [show D2M8K2.u15240 = KTree.node D2M8K2.u15232 (nat_lit 33108240) (nat_lit 3342901075) (nat_lit 0) D2M8K2.u15239 from rfl, totK_node, atot15232, atot15239]
  decide +kernel

theorem arows15255 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15255 = true := by
  rw [show D2M8K2.u15255 = KTree.node D2M8K2.u15247 (nat_lit 33129596) (nat_lit 3357151896) (nat_lit 0) D2M8K2.u15254 from rfl, allE_node, arows15247, irow15255, arows15254]
  all_goals rfl

theorem atot15255 : totK PD2M8K2 D2M8K2.u15255 = [0, 0, 595872241218, 3965017711140, 6824090214502, 2541712061150, 188888234110, 1369150432] := by
  rw [show D2M8K2.u15255 = KTree.node D2M8K2.u15247 (nat_lit 33129596) (nat_lit 3357151896) (nat_lit 0) D2M8K2.u15254 from rfl, totK_node, atot15247, atot15254]
  decide +kernel

theorem arows15271 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15271 = true := by
  rw [show D2M8K2.u15271 = KTree.node D2M8K2.u15263 (nat_lit 33193156) (nat_lit 3723149938) (nat_lit 0) D2M8K2.u15270 from rfl, allE_node, arows15263, irow15271, arows15270]
  all_goals rfl

theorem atot15271 : totK PD2M8K2 D2M8K2.u15271 = [0, 0, 1802790330766, 6248196586484, 5468936837623, 899975933022, 23076523923, 0] := by
  rw [show D2M8K2.u15271 = KTree.node D2M8K2.u15263 (nat_lit 33193156) (nat_lit 3723149938) (nat_lit 0) D2M8K2.u15270 from rfl, totK_node, atot15263, atot15270]
  decide +kernel

theorem arows15286 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15286 = true := by
  rw [show D2M8K2.u15286 = KTree.node D2M8K2.u15278 (nat_lit 33232961) (nat_lit 2203439716) (nat_lit 0) D2M8K2.u15285 from rfl, allE_node, arows15278, irow15286, arows15285]
  all_goals rfl

theorem atot15286 : totK PD2M8K2 D2M8K2.u15286 = [0, 0, 1738365727812, 6240710396550, 5630858667451, 900875297410, 21783111520, 0] := by
  rw [show D2M8K2.u15286 = KTree.node D2M8K2.u15278 (nat_lit 33232961) (nat_lit 2203439716) (nat_lit 0) D2M8K2.u15285 from rfl, totK_node, atot15278, atot15285]
  decide +kernel

theorem arows15303 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15303 = true := by
  rw [show D2M8K2.u15303 = KTree.node D2M8K2.u15295 (nat_lit 33272209) (nat_lit 1521992690) (nat_lit 0) D2M8K2.u15302 from rfl, allE_node, arows15295, irow15303, arows15302]
  all_goals rfl

theorem atot15303 : totK PD2M8K2 D2M8K2.u15303 = [0, 0, 1884437785287, 6564843021610, 5325768112779, 566989960947, 4828048548, 0] := by
  rw [show D2M8K2.u15303 = KTree.node D2M8K2.u15295 (nat_lit 33272209) (nat_lit 1521992690) (nat_lit 0) D2M8K2.u15302 from rfl, totK_node, atot15295, atot15302]
  decide +kernel

theorem arows15318 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15318 = true := by
  rw [show D2M8K2.u15318 = KTree.node D2M8K2.u15310 (nat_lit 33311818) (nat_lit 2586642311) (nat_lit 0) D2M8K2.u15317 from rfl, allE_node, arows15310, irow15318, arows15317]
  all_goals rfl

theorem atot15318 : totK PD2M8K2 D2M8K2.u15318 = [0, 0, 1614239205211, 5972803870359, 5876329890499, 1092607831417, 26159452061, 0] := by
  rw [show D2M8K2.u15318 = KTree.node D2M8K2.u15310 (nat_lit 33311818) (nat_lit 2586642311) (nat_lit 0) D2M8K2.u15317 from rfl, totK_node, atot15310, atot15317]
  decide +kernel

theorem arows15334 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15334 = true := by
  rw [show D2M8K2.u15334 = KTree.node D2M8K2.u15326 (nat_lit 33393601) (nat_lit 1532099120) (nat_lit 0) D2M8K2.u15333 from rfl, allE_node, arows15326, irow15334, arows15333]
  all_goals rfl

theorem atot15334 : totK PD2M8K2 D2M8K2.u15334 = [0, 1691835200920, 5562702637862, 5303383813359, 1672322222205, 261041953443, 17014456371, 0] := by
  rw [show D2M8K2.u15334 = KTree.node D2M8K2.u15326 (nat_lit 33393601) (nat_lit 1532099120) (nat_lit 0) D2M8K2.u15333 from rfl, totK_node, atot15326, atot15333]
  decide +kernel

theorem arows15349 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15349 = true := by
  rw [show D2M8K2.u15349 = KTree.node D2M8K2.u15341 (nat_lit 33410602) (nat_lit 3989042961) (nat_lit 0) D2M8K2.u15348 from rfl, allE_node, arows15341, irow15349, arows15348]
  all_goals rfl

theorem atot15349 : totK PD2M8K2 D2M8K2.u15349 = [0, 425933657684, 3098138486175, 6066031258479, 4017706037036, 868846767299, 42081742489, 0] := by
  rw [show D2M8K2.u15349 = KTree.node D2M8K2.u15341 (nat_lit 33410602) (nat_lit 3989042961) (nat_lit 0) D2M8K2.u15348 from rfl, totK_node, atot15341, atot15348]
  decide +kernel

theorem arows15370 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15370 = true := by
  rw [show D2M8K2.u15370 = KTree.node D2M8K2.u15362 (nat_lit 33424442) (nat_lit 4228345622) (nat_lit 0) D2M8K2.u15369 from rfl, allE_node, arows15362, irow15370, arows15369]
  all_goals rfl

theorem atot15370 : totK PD2M8K2 D2M8K2.u15370 = [0, 754346683581, 3344513993703, 5635162759061, 4005542305247, 716147356727, 15936385454, 0] := by
  rw [show D2M8K2.u15370 = KTree.node D2M8K2.u15362 (nat_lit 33424442) (nat_lit 4228345622) (nat_lit 0) D2M8K2.u15369 from rfl, totK_node, atot15362, atot15369]
  decide +kernel

theorem arows15385 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15385 = true := by
  rw [show D2M8K2.u15385 = KTree.node D2M8K2.u15377 (nat_lit 33441559) (nat_lit 1999090718) (nat_lit 0) D2M8K2.u15384 from rfl, allE_node, arows15377, irow15385, arows15384]
  all_goals rfl

theorem atot15385 : totK PD2M8K2 D2M8K2.u15385 = [0, 1239149993863, 5064523752523, 6040814439399, 1960986801674, 135303440414, 1206465782, 0] := by
  rw [show D2M8K2.u15385 = KTree.node D2M8K2.u15377 (nat_lit 33441559) (nat_lit 1999090718) (nat_lit 0) D2M8K2.u15384 from rfl, totK_node, atot15377, atot15384]
  decide +kernel

theorem arows15401 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15401 = true := by
  rw [show D2M8K2.u15401 = KTree.node D2M8K2.u15393 (nat_lit 33461606) (nat_lit 4124100495) (nat_lit 0) D2M8K2.u15400 from rfl, allE_node, arows15393, irow15401, arows15400]
  all_goals rfl

theorem atot15401 : totK PD2M8K2 D2M8K2.u15401 = [0, 419114938304, 3043820909052, 6395583082824, 4020310874768, 533685320899, 10797810883, 0] := by
  rw [show D2M8K2.u15401 = KTree.node D2M8K2.u15393 (nat_lit 33461606) (nat_lit 4124100495) (nat_lit 0) D2M8K2.u15400 from rfl, totK_node, atot15393, atot15400]
  decide +kernel

theorem arows15416 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15416 = true := by
  rw [show D2M8K2.u15416 = KTree.node D2M8K2.u15408 (nat_lit 33481248) (nat_lit 3510214185) (nat_lit 0) D2M8K2.u15415 from rfl, allE_node, arows15408, irow15416, arows15415]
  all_goals rfl

theorem atot15416 : totK PD2M8K2 D2M8K2.u15416 = [0, 1574928828639, 5712037015892, 5727040812225, 1453917664242, 63414555800, 0, 0] := by
  rw [show D2M8K2.u15416 = KTree.node D2M8K2.u15408 (nat_lit 33481248) (nat_lit 3510214185) (nat_lit 0) D2M8K2.u15415 from rfl, totK_node, atot15408, atot15415]
  decide +kernel

theorem arows15433 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15433 = true := by
  rw [show D2M8K2.u15433 = KTree.node D2M8K2.u15425 (nat_lit 33500836) (nat_lit 2261632939) (nat_lit 0) D2M8K2.u15432 from rfl, allE_node, arows15425, irow15433, arows15432]
  all_goals rfl

theorem atot15433 : totK PD2M8K2 D2M8K2.u15433 = [0, 180280610855, 2379532293760, 6511658250347, 4679613972867, 639481380397, 12143333308, 0] := by
  rw [show D2M8K2.u15433 = KTree.node D2M8K2.u15425 (nat_lit 33500836) (nat_lit 2261632939) (nat_lit 0) D2M8K2.u15432 from rfl, totK_node, atot15425, atot15432]
  decide +kernel

theorem arows15448 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15448 = true := by
  rw [show D2M8K2.u15448 = KTree.node D2M8K2.u15440 (nat_lit 33520009) (nat_lit 1467196014) (nat_lit 0) D2M8K2.u15447 from rfl, allE_node, arows15440, irow15448, arows15447]
  all_goals rfl

theorem atot15448 : totK PD2M8K2 D2M8K2.u15448 = [0, 1478003919410, 5649990158397, 5775815943054, 1535036664397, 87355212873, 0, 0] := by
  rw [show D2M8K2.u15448 = KTree.node D2M8K2.u15440 (nat_lit 33520009) (nat_lit 1467196014) (nat_lit 0) D2M8K2.u15447 from rfl, totK_node, atot15440, atot15447]
  decide +kernel

theorem arows15464 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15464 = true := by
  rw [show D2M8K2.u15464 = KTree.node D2M8K2.u15456 (nat_lit 33545170) (nat_lit 3038744076) (nat_lit 0) D2M8K2.u15463 from rfl, allE_node, arows15456, irow15464, arows15463]
  all_goals rfl

theorem atot15464 : totK PD2M8K2 D2M8K2.u15464 = [0, 773699682448, 4018321501869, 6432703034162, 2981602543453, 265789785891, 1493059870, 0] := by
  rw [show D2M8K2.u15464 = KTree.node D2M8K2.u15456 (nat_lit 33545170) (nat_lit 3038744076) (nat_lit 0) D2M8K2.u15463 from rfl, totK_node, atot15456, atot15463]
  decide +kernel

theorem arows15479 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15479 = true := by
  rw [show D2M8K2.u15479 = KTree.node D2M8K2.u15471 (nat_lit 33563098) (nat_lit 3494077241) (nat_lit 0) D2M8K2.u15478 from rfl, allE_node, arows15471, irow15479, arows15478]
  all_goals rfl

theorem atot15479 : totK PD2M8K2 D2M8K2.u15479 = [0, 1273419804210, 5124290298202, 6122517256572, 1901245676532, 85843688823, 0, 0] := by
  rw [show D2M8K2.u15479 = KTree.node D2M8K2.u15471 (nat_lit 33563098) (nat_lit 3494077241) (nat_lit 0) D2M8K2.u15478 from rfl, totK_node, atot15471, atot15478]
  decide +kernel

theorem arows15497 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15497 = true := by
  rw [show D2M8K2.u15497 = KTree.node D2M8K2.u15489 (nat_lit 33582485) (nat_lit 1633255976) (nat_lit 0) D2M8K2.u15496 from rfl, allE_node, arows15489, irow15497, arows15496]
  all_goals rfl

theorem atot15497 : totK PD2M8K2 D2M8K2.u15497 = [0, 161564142879, 2026902783099, 5971609303892, 5230032764154, 980420024424, 32872698681, 0] := by
  rw [show D2M8K2.u15497 = KTree.node D2M8K2.u15489 (nat_lit 33582485) (nat_lit 1633255976) (nat_lit 0) D2M8K2.u15496 from rfl, totK_node, atot15489, atot15496]
  decide +kernel

theorem arows15512 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15512 = true := by
  rw [show D2M8K2.u15512 = KTree.node D2M8K2.u15504 (nat_lit 33852506) (nat_lit 3787522108) (nat_lit 0) D2M8K2.u15511 from rfl, allE_node, arows15504, irow15512, arows15511]
  all_goals rfl

theorem atot15512 : totK PD2M8K2 D2M8K2.u15512 = [0, 1814988017822, 6164660849199, 5384522607101, 966638533004, 24855040165, 0, 0] := by
  rw [show D2M8K2.u15512 = KTree.node D2M8K2.u15504 (nat_lit 33852506) (nat_lit 3787522108) (nat_lit 0) D2M8K2.u15511 from rfl, totK_node, atot15504, atot15511]
  decide +kernel

theorem arows15528 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15528 = true := by
  rw [show D2M8K2.u15528 = KTree.node D2M8K2.u15520 (nat_lit 33870365) (nat_lit 2298722737) (nat_lit 0) D2M8K2.u15527 from rfl, allE_node, arows15520, irow15528, arows15527]
  all_goals rfl

theorem atot15528 : totK PD2M8K2 D2M8K2.u15528 = [0, 353535550406, 3314877778407, 6960285525681, 3359860425735, 260116602205, 1369150432, 0] := by
  rw [show D2M8K2.u15528 = KTree.node D2M8K2.u15520 (nat_lit 33870365) (nat_lit 2298722737) (nat_lit 0) D2M8K2.u15527 from rfl, totK_node, atot15520, atot15527]
  decide +kernel

theorem arows15543 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15543 = true := by
  rw [show D2M8K2.u15543 = KTree.node D2M8K2.u15535 (nat_lit 33894010) (nat_lit 3723179503) (nat_lit 0) D2M8K2.u15542 from rfl, allE_node, arows15535, irow15543, arows15542]
  all_goals rfl

theorem atot15543 : totK PD2M8K2 D2M8K2.u15543 = [0, 1647558723634, 5841002022999, 5683051203627, 1388359344973, 62915374561, 0, 0] := by
  rw [show D2M8K2.u15543 = KTree.node D2M8K2.u15535 (nat_lit 33894010) (nat_lit 3723179503) (nat_lit 0) D2M8K2.u15542 from rfl, totK_node, atot15535, atot15542]
  decide +kernel

theorem arows15560 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15560 = true := by
  rw [show D2M8K2.u15560 = KTree.node D2M8K2.u15552 (nat_lit 33910982) (nat_lit 3968173516) (nat_lit 0) D2M8K2.u15559 from rfl, allE_node, arows15552, irow15560, arows15559]
  all_goals rfl

theorem atot15560 : totK PD2M8K2 D2M8K2.u15560 = [0, 0, 2031652364727, 6326780041700, 5106531013713, 1029680102282, 39732786462, 0] := by
  rw [show D2M8K2.u15560 = KTree.node D2M8K2.u15552 (nat_lit 33910982) (nat_lit 3968173516) (nat_lit 0) D2M8K2.u15559 from rfl, totK_node, atot15552, atot15559]
  decide +kernel

theorem arows15575 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15575 = true := by
  rw [show D2M8K2.u15575 = KTree.node D2M8K2.u15567 (nat_lit 33926693) (nat_lit 2007773787) (nat_lit 0) D2M8K2.u15574 from rfl, allE_node, arows15567, irow15575, arows15574]
  all_goals rfl

theorem atot15575 : totK PD2M8K2 D2M8K2.u15575 = [0, 1282600422507, 4601183246137, 5393638787031, 2762301275967, 448620550959, 10717512769, 0] := by
  rw [show D2M8K2.u15575 = KTree.node D2M8K2.u15567 (nat_lit 33926693) (nat_lit 2007773787) (nat_lit 0) D2M8K2.u15574 from rfl, totK_node, atot15567, atot15574]
  decide +kernel

theorem arows15591 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15591 = true := by
  rw [show D2M8K2.u15591 = KTree.node D2M8K2.u15583 (nat_lit 33943228) (nat_lit 3826757949) (nat_lit 0) D2M8K2.u15590 from rfl, allE_node, arows15583, irow15591, arows15590]
  all_goals rfl

theorem atot15591 : totK PD2M8K2 D2M8K2.u15591 = [0, 824244286439, 4223185713828, 6405900306515, 2642097296638, 207555570969, 1206465782, 0] := by
  rw [show D2M8K2.u15591 = KTree.node D2M8K2.u15583 (nat_lit 33943228) (nat_lit 3826757949) (nat_lit 0) D2M8K2.u15590 from rfl, totK_node, atot15583, atot15590]
  decide +kernel

theorem arows15606 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15606 = true := by
  rw [show D2M8K2.u15606 = KTree.node D2M8K2.u15598 (nat_lit 33962483) (nat_lit 2840748100) (nat_lit 0) D2M8K2.u15605 from rfl, allE_node, arows15598, irow15606, arows15605]
  all_goals rfl

theorem atot15606 : totK PD2M8K2 D2M8K2.u15606 = [0, 802392591807, 3714362214407, 5841277665381, 3359720491363, 538304205312, 17590593026, 0] := by
  rw [show D2M8K2.u15606 = KTree.node D2M8K2.u15598 (nat_lit 33962483) (nat_lit 2840748100) (nat_lit 0) D2M8K2.u15605 from rfl, totK_node, atot15598, atot15605]
  decide +kernel

theorem arows15625 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15625 = true := by
  rw [show D2M8K2.u15625 = KTree.node D2M8K2.u15617 (nat_lit 34022689) (nat_lit 1509172513) (nat_lit 0) D2M8K2.u15624 from rfl, allE_node, arows15617, irow15625, arows15624]
  all_goals rfl

theorem atot15625 : totK PD2M8K2 D2M8K2.u15625 = [0, 848977784095, 4371444336815, 6490265546531, 2492136631062, 163843401996, 1138244013, 0] := by
  rw [show D2M8K2.u15625 = KTree.node D2M8K2.u15617 (nat_lit 34022689) (nat_lit 1509172513) (nat_lit 0) D2M8K2.u15624 from rfl, totK_node, atot15617, atot15624]
  decide +kernel

theorem arows15640 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15640 = true := by
  rw [show D2M8K2.u15640 = KTree.node D2M8K2.u15632 (nat_lit 34051404) (nat_lit 3569228782) (nat_lit 0) D2M8K2.u15639 from rfl, allE_node, arows15632, irow15640, arows15639]
  all_goals rfl

theorem atot15640 : totK PD2M8K2 D2M8K2.u15640 = [0, 1254121259161, 4785005373854, 5799597781790, 2316946014080, 232595736302, 4977114383, 0] := by
  rw [show D2M8K2.u15640 = KTree.node D2M8K2.u15632 (nat_lit 34051404) (nat_lit 3569228782) (nat_lit 0) D2M8K2.u15639 from rfl, totK_node, atot15632, atot15639]
  decide +kernel

theorem arows15656 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15656 = true := by
  rw [show D2M8K2.u15656 = KTree.node D2M8K2.u15648 (nat_lit 34068291) (nat_lit 2387195009) (nat_lit 0) D2M8K2.u15655 from rfl, allE_node, arows15648, irow15656, arows15655]
  all_goals rfl

theorem atot15656 : totK PD2M8K2 D2M8K2.u15656 = [0, 788562694442, 4124554889533, 6430411963349, 2917779611823, 243597935984, 1310285577, 0] := by
  rw [show D2M8K2.u15656 = KTree.node D2M8K2.u15648 (nat_lit 34068291) (nat_lit 2387195009) (nat_lit 0) D2M8K2.u15655 from rfl, totK_node, atot15648, atot15655]
  decide +kernel

theorem arows15671 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15671 = true := by
  rw [show D2M8K2.u15671 = KTree.node D2M8K2.u15663 (nat_lit 34088040) (nat_lit 3529689327) (nat_lit 0) D2M8K2.u15670 from rfl, allE_node, arows15663, irow15671, arows15670]
  all_goals rfl

theorem atot15671 : totK PD2M8K2 D2M8K2.u15671 = [0, 0, 1750432119017, 6136284246355, 5409156763848, 988993309746, 32931563536, 0] := by
  rw [show D2M8K2.u15671 = KTree.node D2M8K2.u15663 (nat_lit 34088040) (nat_lit 3529689327) (nat_lit 0) D2M8K2.u15670 from rfl, totK_node, atot15663, atot15670]
  decide +kernel

theorem arows15688 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15688 = true := by
  rw [show D2M8K2.u15688 = KTree.node D2M8K2.u15680 (nat_lit 34106774) (nat_lit 2211705737) (nat_lit 8) D2M8K2.u15687 from rfl, allE_node, arows15680, irow15688, arows15687]
  all_goals rfl

theorem atot15688 : totK PD2M8K2 D2M8K2.u15688 = [0, 0, 1202147851424, 5105898311520, 6055566806575, 1729318163070, 113434559660, 1275377855] := by
  rw [show D2M8K2.u15688 = KTree.node D2M8K2.u15680 (nat_lit 34106774) (nat_lit 2211705737) (nat_lit 8) D2M8K2.u15687 from rfl, totK_node, atot15680, atot15687]
  decide +kernel

theorem arows15703 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15703 = true := by
  rw [show D2M8K2.u15703 = KTree.node D2M8K2.u15695 (nat_lit 34136324) (nat_lit 3609684929) (nat_lit 0) D2M8K2.u15702 from rfl, allE_node, arows15695, irow15703, arows15702]
  all_goals rfl

theorem atot15703 : totK PD2M8K2 D2M8K2.u15703 = [0, 0, 1300513930509, 5384545203891, 6188171211578, 1593967869736, 55186157806, 0] := by
  rw [show D2M8K2.u15703 = KTree.node D2M8K2.u15695 (nat_lit 34136324) (nat_lit 3609684929) (nat_lit 0) D2M8K2.u15702 from rfl, totK_node, atot15695, atot15702]
  decide +kernel

theorem arows15719 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15719 = true := by
  rw [show D2M8K2.u15719 = KTree.node D2M8K2.u15711 (nat_lit 34174921) (nat_lit 1495594652) (nat_lit 0) D2M8K2.u15718 from rfl, allE_node, arows15711, irow15719, arows15718]
  all_goals rfl

theorem atot15719 : totK PD2M8K2 D2M8K2.u15719 = [0, 0, 1967015062152, 6369955646556, 5228274848215, 953437568991, 30941024509, 0] := by
  rw [show D2M8K2.u15719 = KTree.node D2M8K2.u15711 (nat_lit 34174921) (nat_lit 1495594652) (nat_lit 0) D2M8K2.u15718 from rfl, totK_node, atot15711, atot15718]
  decide +kernel

theorem arows15734 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15734 = true := by
  rw [show D2M8K2.u15734 = KTree.node D2M8K2.u15726 (nat_lit 34192576) (nat_lit 3778076146) (nat_lit 0) D2M8K2.u15733 from rfl, allE_node, arows15726, irow15734, arows15733]
  all_goals rfl

theorem atot15734 : totK PD2M8K2 D2M8K2.u15734 = [0, 0, 816396862079, 4378933964530, 6472500616440, 2365223537089, 163349786305, 1206465782] := by
  rw [show D2M8K2.u15734 = KTree.node D2M8K2.u15726 (nat_lit 34192576) (nat_lit 3778076146) (nat_lit 0) D2M8K2.u15733 from rfl, totK_node, atot15726, atot15733]
  decide +kernel

theorem arows15752 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15752 = true := by
  rw [show D2M8K2.u15752 = KTree.node D2M8K2.u15744 (nat_lit 34258229) (nat_lit 2399141089) (nat_lit 0) D2M8K2.u15751 from rfl, allE_node, arows15744, irow15752, arows15751]
  all_goals rfl

theorem atot15752 : totK PD2M8K2 D2M8K2.u15752 = [0, 0, 1549306762967, 5358946390242, 5332946213873, 1797037983039, 220462625266, 5395128787] := by
  rw [show D2M8K2.u15752 = KTree.node D2M8K2.u15744 (nat_lit 34258229) (nat_lit 2399141089) (nat_lit 0) D2M8K2.u15751 from rfl, totK_node, atot15744, atot15751]
  decide +kernel

theorem arows15767 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15767 = true := by
  rw [show D2M8K2.u15767 = KTree.node D2M8K2.u15759 (nat_lit 34302921) (nat_lit 1649608476) (nat_lit 2) D2M8K2.u15766 from rfl, allE_node, arows15759, irow15767, arows15766]
  all_goals rfl

theorem atot15767 : totK PD2M8K2 D2M8K2.u15767 = [0, 0, 1680784543910, 6099984385960, 5632947868299, 1049490975977, 31691046387, 0] := by
  rw [show D2M8K2.u15767 = KTree.node D2M8K2.u15759 (nat_lit 34302921) (nat_lit 1649608476) (nat_lit 2) D2M8K2.u15766 from rfl, totK_node, atot15759, atot15766]
  decide +kernel

theorem arows15783 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15783 = true := by
  rw [show D2M8K2.u15783 = KTree.node D2M8K2.u15775 (nat_lit 34340812) (nat_lit 3453424231) (nat_lit 0) D2M8K2.u15782 from rfl, allE_node, arows15775, irow15783, arows15782]
  all_goals rfl

theorem atot15783 : totK PD2M8K2 D2M8K2.u15783 = [0, 1181843208129, 4547045026873, 5414460860740, 2670268975909, 565084470050, 26013318776, 0] := by
  rw [show D2M8K2.u15783 = KTree.node D2M8K2.u15775 (nat_lit 34340812) (nat_lit 3453424231) (nat_lit 0) D2M8K2.u15782 from rfl, totK_node, atot15775, atot15782]
  decide +kernel

theorem arows15798 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15798 = true := by
  rw [show D2M8K2.u15798 = KTree.node D2M8K2.u15790 (nat_lit 34359461) (nat_lit 2186599966) (nat_lit 0) D2M8K2.u15797 from rfl, allE_node, arows15790, irow15798, arows15797]
  all_goals rfl

theorem atot15798 : totK PD2M8K2 D2M8K2.u15798 = [0, 794902111556, 4132455332610, 6403156092115, 2686312078913, 219537040814, 1369150432, 0] := by
  rw [show D2M8K2.u15798 = KTree.node D2M8K2.u15790 (nat_lit 34359461) (nat_lit 2186599966) (nat_lit 0) D2M8K2.u15797 from rfl, totK_node, atot15790, atot15797]
  decide +kernel

theorem arows15815 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15815 = true := by
  rw [show D2M8K2.u15815 = KTree.node D2M8K2.u15807 (nat_lit 34386640) (nat_lit 2399499417) (nat_lit 0) D2M8K2.u15814 from rfl, allE_node, arows15807, irow15815, arows15814]
  all_goals rfl

theorem atot15815 : totK PD2M8K2 D2M8K2.u15815 = [0, 1199418329317, 4937140004447, 6201840071305, 2086305514152, 105188343323, 0, 0] := by
  rw [show D2M8K2.u15815 = KTree.node D2M8K2.u15807 (nat_lit 34386640) (nat_lit 2399499417) (nat_lit 0) D2M8K2.u15814 from rfl, totK_node, atot15807, atot15814]
  decide +kernel

theorem arows15830 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15830 = true := by
  rw [show D2M8K2.u15830 = KTree.node D2M8K2.u15822 (nat_lit 34401019) (nat_lit 1503350993) (nat_lit 0) D2M8K2.u15829 from rfl, allE_node, arows15822, irow15830, arows15829]
  all_goals rfl

theorem atot15830 : totK PD2M8K2 D2M8K2.u15830 = [0, 801898790771, 3774727538805, 5811742226807, 3464032296242, 733818674012, 34639773963, 0] := by
  rw [show D2M8K2.u15830 = KTree.node D2M8K2.u15822 (nat_lit 34401019) (nat_lit 1503350993) (nat_lit 0) D2M8K2.u15829 from rfl, totK_node, atot15822, atot15829]
  decide +kernel

theorem arows15846 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15846 = true := by
  rw [show D2M8K2.u15846 = KTree.node D2M8K2.u15838 (nat_lit 34419010) (nat_lit 4141143164) (nat_lit 0) D2M8K2.u15845 from rfl, allE_node, arows15838, irow15846, arows15845]
  all_goals rfl

theorem atot15846 : totK PD2M8K2 D2M8K2.u15846 = [0, 664302839380, 3256067739818, 5772209983609, 4047098025878, 718187866822, 15936385454, 0] := by
  rw [show D2M8K2.u15846 = KTree.node D2M8K2.u15838 (nat_lit 34419010) (nat_lit 4141143164) (nat_lit 0) D2M8K2.u15845 from rfl, totK_node, atot15838, atot15845]
  decide +kernel

theorem arows15861 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15861 = true := by
  rw [show D2M8K2.u15861 = KTree.node D2M8K2.u15853 (nat_lit 34477304) (nat_lit 3862132601) (nat_lit 0) D2M8K2.u15860 from rfl, allE_node, arows15853, irow15861, arows15860]
  all_goals rfl

theorem atot15861 : totK PD2M8K2 D2M8K2.u15861 = [0, 1442972718985, 5475991242294, 5863049404229, 1593313223188, 76237013891, 0, 0] := by
  rw [show D2M8K2.u15861 = KTree.node D2M8K2.u15853 (nat_lit 34477304) (nat_lit 3862132601) (nat_lit 0) D2M8K2.u15860 from rfl, totK_node, atot15853, atot15860]
  decide +kernel

theorem arows15881 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15881 = true := by
  rw [show D2M8K2.u15881 = KTree.node D2M8K2.u15873 (nat_lit 34496054) (nat_lit 3052681437) (nat_lit 0) D2M8K2.u15880 from rfl, allE_node, arows15873, irow15881, arows15880]
  all_goals rfl

theorem atot15881 : totK PD2M8K2 D2M8K2.u15881 = [0, 89266124844, 2131999340728, 6449987617902, 4821601149810, 711705727026, 19065934916, 0] := by
  rw [show D2M8K2.u15881 = KTree.node D2M8K2.u15873 (nat_lit 34496054) (nat_lit 3052681437) (nat_lit 0) D2M8K2.u15880 from rfl, totK_node, atot15873, atot15880]
  decide +kernel

theorem arows15896 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15896 = true := by
  rw [show D2M8K2.u15896 = KTree.node D2M8K2.u15888 (nat_lit 34515486) (nat_lit 3880565180) (nat_lit 0) D2M8K2.u15895 from rfl, allE_node, arows15888, irow15896, arows15895]
  all_goals rfl

theorem atot15896 : totK PD2M8K2 D2M8K2.u15896 = [0, 1562394468209, 5863209581371, 5772023984093, 1224379395507, 36377888210, 0, 0] := by
  rw [show D2M8K2.u15896 = KTree.node D2M8K2.u15888 (nat_lit 34515486) (nat_lit 3880565180) (nat_lit 0) D2M8K2.u15895 from rfl, totK_node, atot15888, atot15895]
  decide +kernel

theorem arows15912 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15912 = true := by
  rw [show D2M8K2.u15912 = KTree.node D2M8K2.u15904 (nat_lit 34539790) (nat_lit 2214989119) (nat_lit 0) D2M8K2.u15911 from rfl, allE_node, arows15904, irow15912, arows15911]
  all_goals rfl

theorem atot15912 : totK PD2M8K2 D2M8K2.u15912 = [0, 674155161047, 3645356812532, 6320091201545, 3290065041074, 345448649931, 6115358396, 0] := by
  rw [show D2M8K2.u15912 = KTree.node D2M8K2.u15904 (nat_lit 34539790) (nat_lit 2214989119) (nat_lit 0) D2M8K2.u15911 from rfl, totK_node, atot15904, atot15911]
  decide +kernel

theorem arows15927 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15927 = true := by
  rw [show D2M8K2.u15927 = KTree.node D2M8K2.u15919 (nat_lit 34557775) (nat_lit 2432917385) (nat_lit 0) D2M8K2.u15926 from rfl, allE_node, arows15919, irow15927, arows15926]
  all_goals rfl

theorem atot15927 : totK PD2M8K2 D2M8K2.u15927 = [0, 1364983409395, 5316547471172, 6019633946559, 1771396208638, 84439449350, 0, 0] := by
  rw [show D2M8K2.u15927 = KTree.node D2M8K2.u15919 (nat_lit 34557775) (nat_lit 2432917385) (nat_lit 0) D2M8K2.u15926 from rfl, totK_node, atot15919, atot15926]
  decide +kernel

theorem arows15944 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15944 = true := by
  rw [show D2M8K2.u15944 = KTree.node D2M8K2.u15936 (nat_lit 34577036) (nat_lit 1809703006) (nat_lit 0) D2M8K2.u15943 from rfl, allE_node, arows15936, irow15944, arows15943]
  all_goals rfl

theorem atot15944 : totK PD2M8K2 D2M8K2.u15944 = [0, 0, 1867393757420, 6289135269856, 5336730125068, 870193344375, 19545957871, 0] := by
  rw [show D2M8K2.u15944 = KTree.node D2M8K2.u15936 (nat_lit 34577036) (nat_lit 1809703006) (nat_lit 0) D2M8K2.u15943 from rfl, totK_node, atot15936, atot15943]
  decide +kernel

theorem arows15959 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15959 = true := by
  rw [show D2M8K2.u15959 = KTree.node D2M8K2.u15951 (nat_lit 34598926) (nat_lit 3866554942) (nat_lit 0) D2M8K2.u15958 from rfl, allE_node, arows15951, irow15959, arows15958]
  all_goals rfl

theorem atot15959 : totK PD2M8K2 D2M8K2.u15959 = [0, 0, 1947272267012, 6426345870914, 5168009842901, 760819099397, 22412363506, 0] := by
  rw [show D2M8K2.u15959 = KTree.node D2M8K2.u15951 (nat_lit 34598926) (nat_lit 3866554942) (nat_lit 0) D2M8K2.u15958 from rfl, totK_node, atot15951, atot15958]
  decide +kernel

theorem arows15975 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15975 = true := by
  rw [show D2M8K2.u15975 = KTree.node D2M8K2.u15967 (nat_lit 34619891) (nat_lit 2834441033) (nat_lit 0) D2M8K2.u15974 from rfl, allE_node, arows15967, irow15975, arows15974]
  all_goals rfl

theorem atot15975 : totK PD2M8K2 D2M8K2.u15975 = [0, 0, 459572566048, 3958496829510, 7058304830053, 2612290829932, 156730003552, 1310517177] := by
  rw [show D2M8K2.u15975 = KTree.node D2M8K2.u15967 (nat_lit 34619891) (nat_lit 2834441033) (nat_lit 0) D2M8K2.u15974 from rfl, totK_node, atot15967, atot15974]
  decide +kernel

theorem arows15990 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u15990 = true := by
  rw [show D2M8K2.u15990 = KTree.node D2M8K2.u15982 (nat_lit 34646741) (nat_lit 2373890930) (nat_lit 0) D2M8K2.u15989 from rfl, allE_node, arows15982, irow15990, arows15989]
  all_goals rfl

theorem atot15990 : totK PD2M8K2 D2M8K2.u15990 = [0, 0, 2155585993098, 6541654392841, 5058577203633, 842339133943, 22494856912, 0] := by
  rw [show D2M8K2.u15990 = KTree.node D2M8K2.u15982 (nat_lit 34646741) (nat_lit 2373890930) (nat_lit 0) D2M8K2.u15989 from rfl, totK_node, atot15982, atot15989]
  decide +kernel

theorem arows16008 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16008 = true := by
  rw [show D2M8K2.u16008 = KTree.node D2M8K2.u16000 (nat_lit 34726302) (nat_lit 3819506073) (nat_lit 0) D2M8K2.u16007 from rfl, allE_node, arows16000, irow16008, arows16007]
  all_goals rfl

theorem atot16008 : totK PD2M8K2 D2M8K2.u16008 = [0, 0, 1486514008855, 5621085095359, 5822465637156, 1391699104029, 54142926489, 0] := by
  rw [show D2M8K2.u16008 = KTree.node D2M8K2.u16000 (nat_lit 34726302) (nat_lit 3819506073) (nat_lit 0) D2M8K2.u16007 from rfl, totK_node, atot16000, atot16007]
  decide +kernel

theorem arows16023 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16023 = true := by
  rw [show D2M8K2.u16023 = KTree.node D2M8K2.u16015 (nat_lit 34746704) (nat_lit 3703797458) (nat_lit 0) D2M8K2.u16022 from rfl, allE_node, arows16015, irow16023, arows16022]
  all_goals rfl

theorem atot16023 : totK PD2M8K2 D2M8K2.u16023 = [0, 0, 649641915702, 3800945227348, 6337433631618, 3083127843133, 346802042735, 6643327963] := by
  rw [show D2M8K2.u16023 = KTree.node D2M8K2.u16015 (nat_lit 34746704) (nat_lit 3703797458) (nat_lit 0) D2M8K2.u16022 from rfl, totK_node, atot16015, atot16022]
  decide +kernel

theorem arows16039 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16039 = true := by
  rw [show D2M8K2.u16039 = KTree.node D2M8K2.u16031 (nat_lit 34796173) (nat_lit 1385917071) (nat_lit 0) D2M8K2.u16038 from rfl, allE_node, arows16031, irow16039, arows16038]
  all_goals rfl

theorem atot16039 : totK PD2M8K2 D2M8K2.u16039 = [0, 0, 2155872671574, 6644138593000, 4926044632265, 779125318607, 22643548536, 0] := by
  rw [show D2M8K2.u16039 = KTree.node D2M8K2.u16031 (nat_lit 34796173) (nat_lit 1385917071) (nat_lit 0) D2M8K2.u16038 from rfl, totK_node, atot16031, atot16038]
  decide +kernel

theorem arows16054 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16054 = true := by
  rw [show D2M8K2.u16054 = KTree.node D2M8K2.u16046 (nat_lit 34814117) (nat_lit 1688398795) (nat_lit 0) D2M8K2.u16053 from rfl, allE_node, arows16046, irow16054, arows16053]
  all_goals rfl

theorem atot16054 : totK PD2M8K2 D2M8K2.u16054 = [0, 847096328040, 3452265271632, 5227186135830, 3946393178332, 922111645312, 36051743830, 0] := by
  rw [show D2M8K2.u16054 = KTree.node D2M8K2.u16046 (nat_lit 34814117) (nat_lit 1688398795) (nat_lit 0) D2M8K2.u16053 from rfl, totK_node, atot16046, atot16053]
  decide +kernel

theorem arows16071 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16071 = true := by
  rw [show D2M8K2.u16071 = KTree.node D2M8K2.u16063 (nat_lit 35350321) (nat_lit 1477613420) (nat_lit 0) D2M8K2.u16070 from rfl, allE_node, arows16063, irow16071, arows16070]
  all_goals rfl

theorem atot16071 : totK PD2M8K2 D2M8K2.u16071 = [0, 1160585531122, 4964136611916, 6083015108884, 1926286147243, 146077096297, 1369150432, 0] := by
  rw [show D2M8K2.u16071 = KTree.node D2M8K2.u16063 (nat_lit 35350321) (nat_lit 1477613420) (nat_lit 0) D2M8K2.u16070 from rfl, totK_node, atot16063, atot16070]
  decide +kernel

theorem arows16086 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16086 = true := by
  rw [show D2M8K2.u16086 = KTree.node D2M8K2.u16078 (nat_lit 35372909) (nat_lit 2053667081) (nat_lit 0) D2M8K2.u16085 from rfl, allE_node, arows16078, irow16086, arows16085]
  all_goals rfl

theorem atot16086 : totK PD2M8K2 D2M8K2.u16086 = [0, 858997118062, 4120308266495, 6479395171138, 2813620766006, 159308592021, 0, 0] := by
  rw [show D2M8K2.u16086 = KTree.node D2M8K2.u16078 (nat_lit 35372909) (nat_lit 2053667081) (nat_lit 0) D2M8K2.u16085 from rfl, totK_node, atot16078, atot16085]
  decide +kernel

theorem arows16102 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16102 = true := by
  rw [show D2M8K2.u16102 = KTree.node D2M8K2.u16094 (nat_lit 35391526) (nat_lit 3484605207) (nat_lit 0) D2M8K2.u16101 from rfl, allE_node, arows16094, irow16102, arows16101]
  all_goals rfl

theorem atot16102 : totK PD2M8K2 D2M8K2.u16102 = [0, 1172193504829, 5132351867931, 6263668464029, 1919627192681, 107655040202, 0, 0] := by
  rw [show D2M8K2.u16102 = KTree.node D2M8K2.u16094 (nat_lit 35391526) (nat_lit 3484605207) (nat_lit 0) D2M8K2.u16101 from rfl, totK_node, atot16094, atot16101]
  decide +kernel

theorem arows16117 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16117 = true := by
  rw [show D2M8K2.u16117 = KTree.node D2M8K2.u16109 (nat_lit 35408297) (nat_lit 1558655659) (nat_lit 0) D2M8K2.u16116 from rfl, allE_node, arows16109, irow16117, arows16116]
  all_goals rfl

theorem atot16117 : totK PD2M8K2 D2M8K2.u16117 = [0, 0, 1581679121987, 5912457442495, 5779861981754, 1199191608015, 37477867745, 0] := by
  rw [show D2M8K2.u16117 = KTree.node D2M8K2.u16109 (nat_lit 35408297) (nat_lit 1558655659) (nat_lit 0) D2M8K2.u16116 from rfl, totK_node, atot16109, atot16116]
  decide +kernel

theorem arows16136 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16136 = true := by
  rw [show D2M8K2.u16136 = KTree.node D2M8K2.u16128 (nat_lit 35423468) (nat_lit 3786797412) (nat_lit 0) D2M8K2.u16135 from rfl, allE_node, arows16128, irow16136, arows16135]
  all_goals rfl

theorem atot16136 : totK PD2M8K2 D2M8K2.u16136 = [0, 1608064984160, 5674237846644, 5501124878619, 1490477578918, 184496289031, 8063697217, 0] := by
  rw [show D2M8K2.u16136 = KTree.node D2M8K2.u16128 (nat_lit 35423468) (nat_lit 3786797412) (nat_lit 0) D2M8K2.u16135 from rfl, totK_node, atot16128, atot16135]
  decide +kernel

theorem arows16151 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16151 = true := by
  rw [show D2M8K2.u16151 = KTree.node D2M8K2.u16143 (nat_lit 35441680) (nat_lit 3382287894) (nat_lit 0) D2M8K2.u16150 from rfl, allE_node, arows16143, irow16151, arows16150]
  all_goals rfl

theorem atot16151 : totK PD2M8K2 D2M8K2.u16151 = [0, 406574288871, 3085158785441, 6479557166041, 3863173383106, 472560434763, 10008546867, 0] := by
  rw [show D2M8K2.u16151 = KTree.node D2M8K2.u16143 (nat_lit 35441680) (nat_lit 3382287894) (nat_lit 0) D2M8K2.u16150 from rfl, totK_node, atot16143, atot16150]
  decide +kernel

theorem arows16167 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16167 = true := by
  rw [show D2M8K2.u16167 = KTree.node D2M8K2.u16159 (nat_lit 35462983) (nat_lit 2386117944) (nat_lit 0) D2M8K2.u16166 from rfl, allE_node, arows16159, irow16167, arows16166]
  all_goals rfl

theorem atot16167 : totK PD2M8K2 D2M8K2.u16167 = [0, 1345468884193, 5037514121755, 5802693968821, 2110950534581, 157781279733, 1021600638, 0] := by
  rw [show D2M8K2.u16167 = KTree.node D2M8K2.u16159 (nat_lit 35462983) (nat_lit 2386117944) (nat_lit 0) D2M8K2.u16166 from rfl, totK_node, atot16159, atot16166]
  decide +kernel

theorem arows16182 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16182 = true := by
  rw [show D2M8K2.u16182 = KTree.node D2M8K2.u16174 (nat_lit 35480239) (nat_lit 2447444894) (nat_lit 0) D2M8K2.u16181 from rfl, allE_node, arows16174, irow16182, arows16181]
  all_goals rfl

theorem atot16182 : totK PD2M8K2 D2M8K2.u16182 = [0, 673281506373, 3829063940302, 6417789971382, 3190987281863, 300918908510, 2410950632, 0] := by
  rw [show D2M8K2.u16182 = KTree.node D2M8K2.u16174 (nat_lit 35480239) (nat_lit 2447444894) (nat_lit 0) D2M8K2.u16181 from rfl, totK_node, atot16174, atot16181]
  decide +kernel

theorem arows16199 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16199 = true := by
  rw [show D2M8K2.u16199 = KTree.node D2M8K2.u16191 (nat_lit 35543026) (nat_lit 3994572769) (nat_lit 0) D2M8K2.u16198 from rfl, allE_node, arows16191, irow16199, arows16198]
  all_goals rfl

theorem atot16199 : totK PD2M8K2 D2M8K2.u16199 = [0, 1143893231512, 4485431143655, 5757929286702, 2708442605956, 331975209595, 8735979960, 0] := by
  rw [show D2M8K2.u16199 = KTree.node D2M8K2.u16191 (nat_lit 35543026) (nat_lit 3994572769) (nat_lit 0) D2M8K2.u16198 from rfl, totK_node, atot16191, atot16198]
  decide +kernel

theorem arows16214 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16214 = true := by
  rw [show D2M8K2.u16214 = KTree.node D2M8K2.u16206 (nat_lit 35559536) (nat_lit 3427855976) (nat_lit 0) D2M8K2.u16213 from rfl, allE_node, arows16206, irow16214, arows16213]
  all_goals rfl

theorem atot16214 : totK PD2M8K2 D2M8K2.u16214 = [0, 993034531268, 4497425596165, 6197423009672, 2551025007457, 205122459893, 1310285577, 0] := by
  rw [show D2M8K2.u16214 = KTree.node D2M8K2.u16206 (nat_lit 35559536) (nat_lit 3427855976) (nat_lit 0) D2M8K2.u16213 from rfl, totK_node, atot16206, atot16213]
  decide +kernel

theorem arows16230 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16230 = true := by
  rw [show D2M8K2.u16230 = KTree.node D2M8K2.u16222 (nat_lit 35575216) (nat_lit 2116244903) (nat_lit 0) D2M8K2.u16229 from rfl, allE_node, arows16222, irow16230, arows16229]
  all_goals rfl

theorem atot16230 : totK PD2M8K2 D2M8K2.u16230 = [0, 0, 1934313794815, 6314464695579, 5135849538013, 930351893770, 32931563536, 0] := by
  rw [show D2M8K2.u16230 = KTree.node D2M8K2.u16222 (nat_lit 35575216) (nat_lit 2116244903) (nat_lit 0) D2M8K2.u16229 from rfl, totK_node, atot16222, atot16229]
  decide +kernel

theorem arows16245 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16245 = true := by
  rw [show D2M8K2.u16245 = KTree.node D2M8K2.u16237 (nat_lit 35596086) (nat_lit 3767507487) (nat_lit 0) D2M8K2.u16244 from rfl, allE_node, arows16237, irow16245, arows16244]
  all_goals rfl

theorem atot16245 : totK PD2M8K2 D2M8K2.u16245 = [0, 0, 1568942934754, 5941081785881, 5724879461230, 1050791176516, 33414641835, 0] := by
  rw [show D2M8K2.u16245 = KTree.node D2M8K2.u16237 (nat_lit 35596086) (nat_lit 3767507487) (nat_lit 0) D2M8K2.u16244 from rfl, totK_node, atot16237, atot16244]
  decide +kernel

theorem arows16263 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16263 = true := by
  rw [show D2M8K2.u16263 = KTree.node D2M8K2.u16255 (nat_lit 35617801) (nat_lit 1505158212) (nat_lit 0) D2M8K2.u16262 from rfl, allE_node, arows16255, irow16263, arows16262]
  all_goals rfl

theorem atot16263 : totK PD2M8K2 D2M8K2.u16263 = [0, 0, 511088486868, 3588640810990, 6870297051929, 3010843599840, 215637219031, 1369150432] := by
  rw [show D2M8K2.u16263 = KTree.node D2M8K2.u16255 (nat_lit 35617801) (nat_lit 1505158212) (nat_lit 0) D2M8K2.u16262 from rfl, totK_node, atot16255, atot16262]
  decide +kernel

theorem arows16278 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16278 = true := by
  rw [show D2M8K2.u16278 = KTree.node D2M8K2.u16270 (nat_lit 35639165) (nat_lit 1808598868) (nat_lit 0) D2M8K2.u16277 from rfl, allE_node, arows16270, irow16278, arows16277]
  all_goals rfl

theorem atot16278 : totK PD2M8K2 D2M8K2.u16278 = [0, 0, 1922680518743, 6435621130908, 5273635439225, 921259505352, 30406022472, 0] := by
  rw [show D2M8K2.u16278 = KTree.node D2M8K2.u16270 (nat_lit 35639165) (nat_lit 1808598868) (nat_lit 0) D2M8K2.u16277 from rfl, totK_node, atot16270, atot16277]
  decide +kernel

theorem arows16294 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16294 = true := by
  rw [show D2M8K2.u16294 = KTree.node D2M8K2.u16286 (nat_lit 35675777) (nat_lit 2220551655) (nat_lit 0) D2M8K2.u16293 from rfl, allE_node, arows16286, irow16294, arows16293]
  all_goals rfl

theorem atot16294 : totK PD2M8K2 D2M8K2.u16294 = [0, 0, 1605937210258, 5833899284684, 5711042630655, 1298697179483, 49536069866, 0] := by
  rw [show D2M8K2.u16294 = KTree.node D2M8K2.u16286 (nat_lit 35675777) (nat_lit 2220551655) (nat_lit 0) D2M8K2.u16293 from rfl, totK_node, atot16286, atot16293]
  decide +kernel

theorem arows16309 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16309 = true := by
  rw [show D2M8K2.u16309 = KTree.node D2M8K2.u16301 (nat_lit 35696810) (nat_lit 3498321250) (nat_lit 0) D2M8K2.u16308 from rfl, allE_node, arows16301, irow16309, arows16308]
  all_goals rfl

theorem atot16309 : totK PD2M8K2 D2M8K2.u16309 = [0, 0, 602869134900, 3741954496223, 6449353925042, 3039564680183, 322102058452, 6301476269] := by
  rw [show D2M8K2.u16309 = KTree.node D2M8K2.u16301 (nat_lit 35696810) (nat_lit 3498321250) (nat_lit 0) D2M8K2.u16308 from rfl, totK_node, atot16301, atot16308]
  decide +kernel

theorem arows16326 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16326 = true := by
  rw [show D2M8K2.u16326 = KTree.node D2M8K2.u16318 (nat_lit 35721772) (nat_lit 2896855373) (nat_lit 512) D2M8K2.u16325 from rfl, allE_node, arows16318, irow16326, arows16325]
  all_goals rfl

theorem atot16326 : totK PD2M8K2 D2M8K2.u16326 = [0, 0, 1410093006780, 5543646236714, 5934498676792, 1481662800508, 57231897009, 0] := by
  rw [show D2M8K2.u16326 = KTree.node D2M8K2.u16318 (nat_lit 35721772) (nat_lit 2896855373) (nat_lit 512) D2M8K2.u16325 from rfl, totK_node, atot16318, atot16325]
  decide +kernel

theorem arows16341 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16341 = true := by
  rw [show D2M8K2.u16341 = KTree.node D2M8K2.u16333 (nat_lit 35745602) (nat_lit 2627028404) (nat_lit 0) D2M8K2.u16340 from rfl, allE_node, arows16333, irow16341, arows16340]
  all_goals rfl

theorem atot16341 : totK PD2M8K2 D2M8K2.u16341 = [0, 0, 843057015360, 4140121531009, 6100281975526, 2858394327517, 319462662295, 6363931553] := by
  rw [show D2M8K2.u16341 = KTree.node D2M8K2.u16333 (nat_lit 35745602) (nat_lit 2627028404) (nat_lit 0) D2M8K2.u16340 from rfl, totK_node, atot16333, atot16340]
  decide +kernel

theorem arows16357 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16357 = true := by
  rw [show D2M8K2.u16357 = KTree.node D2M8K2.u16349 (nat_lit 35802224) (nat_lit 3064838031) (nat_lit 0) D2M8K2.u16356 from rfl, allE_node, arows16349, irow16357, arows16356]
  all_goals rfl

theorem atot16357 : totK PD2M8K2 D2M8K2.u16357 = [0, 0, 1288971957659, 5230256854810, 6082493845239, 1706567507128, 73721864074, 0] := by
  rw [show D2M8K2.u16357 = KTree.node D2M8K2.u16349 (nat_lit 35802224) (nat_lit 3064838031) (nat_lit 0) D2M8K2.u16356 from rfl, totK_node, atot16349, atot16356]
  decide +kernel

theorem arows16372 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u16372 = true := by
  rw [show D2M8K2.u16372 = KTree.node D2M8K2.u16364 (nat_lit 35821512) (nat_lit 3621588267) (nat_lit 0) D2M8K2.u16371 from rfl, allE_node, arows16364, irow16372, arows16371]
  all_goals rfl

theorem atot16372 : totK PD2M8K2 D2M8K2.u16372 = [0, 0, 0, 1846805747070, 6178724237232, 5094868530562, 932129833522, 32664957003] := by
  rw [show D2M8K2.u16372 = KTree.node D2M8K2.u16364 (nat_lit 35821512) (nat_lit 3621588267) (nat_lit 0) D2M8K2.u16371 from rfl, totK_node, atot16364, atot16371]
  decide +kernel

theorem arows30 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u30 = true := by
  rw [show D2M8K2.u30 = KTree.node D2M8K2.u14 (nat_lit 16953) (nat_lit 1899350950) (nat_lit 0) D2M8K2.u29 from rfl, allE_node, arows14, irow30, arows29]
  all_goals rfl

theorem atot30 : totK PD2M8K2 D2M8K2.u30 = [2125803138054, 9461077530359, 12416608382119, 4400837068088, 304269731475, 1369150432, 0, 0] := by
  rw [show D2M8K2.u30 = KTree.node D2M8K2.u14 (nat_lit 16953) (nat_lit 1899350950) (nat_lit 0) D2M8K2.u29 from rfl, totK_node, atot14, atot29]
  decide +kernel

theorem arows61 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u61 = true := by
  rw [show D2M8K2.u61 = KTree.node D2M8K2.u45 (nat_lit 99180) (nat_lit 3098270986) (nat_lit 0) D2M8K2.u60 from rfl, allE_node, arows45, irow61, arows60]
  all_goals rfl

theorem atot61 : totK PD2M8K2 D2M8K2.u61 = [2013486191525, 8801013381992, 12067035169501, 5243461146202, 582133431186, 14222663156, 0, 0] := by
  rw [show D2M8K2.u61 = KTree.node D2M8K2.u45 (nat_lit 99180) (nat_lit 3098270986) (nat_lit 0) D2M8K2.u60 from rfl, totK_node, atot45, atot60]
  decide +kernel

theorem arows93 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u93 = true := by
  rw [show D2M8K2.u93 = KTree.node D2M8K2.u77 (nat_lit 137990) (nat_lit 4112680829) (nat_lit 0) D2M8K2.u92 from rfl, allE_node, arows77, irow93, arows92]
  all_goals rfl

theorem atot93 : totK PD2M8K2 D2M8K2.u93 = [2013968688706, 8893751024962, 12198416634243, 5170947348445, 471086131067, 5814261725, 0, 0] := by
  rw [show D2M8K2.u93 = KTree.node D2M8K2.u77 (nat_lit 137990) (nat_lit 4112680829) (nat_lit 0) D2M8K2.u92 from rfl, totK_node, atot77, atot92]
  decide +kernel

theorem arows124 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u124 = true := by
  rw [show D2M8K2.u124 = KTree.node D2M8K2.u108 (nat_lit 173279) (nat_lit 1532069793) (nat_lit 0) D2M8K2.u123 from rfl, allE_node, arows108, irow124, arows123]
  all_goals rfl

theorem atot124 : totK PD2M8K2 D2M8K2.u124 = [2008348425205, 8588049282223, 11765133950839, 5494556341788, 708250459019, 18964312856, 0, 0] := by
  rw [show D2M8K2.u124 = KTree.node D2M8K2.u108 (nat_lit 173279) (nat_lit 1532069793) (nat_lit 0) D2M8K2.u123 from rfl, totK_node, atot108, atot123]
  decide +kernel

theorem arows157 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u157 = true := by
  rw [show D2M8K2.u157 = KTree.node D2M8K2.u141 (nat_lit 213678) (nat_lit 3888402024) (nat_lit 0) D2M8K2.u156 from rfl, allE_node, arows141, irow157, arows156]
  all_goals rfl

theorem atot157 : totK PD2M8K2 D2M8K2.u157 = [2019269348258, 8963928223972, 12291900548121, 5013342929293, 463700905966, 6287399960, 0, 0] := by
  rw [show D2M8K2.u157 = KTree.node D2M8K2.u141 (nat_lit 213678) (nat_lit 3888402024) (nat_lit 0) D2M8K2.u156 from rfl, totK_node, atot141, atot156]
  decide +kernel

theorem arows188 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u188 = true := by
  rw [show D2M8K2.u188 = KTree.node D2M8K2.u172 (nat_lit 249913) (nat_lit 1439895473) (nat_lit 0) D2M8K2.u187 from rfl, allE_node, arows172, irow188, arows187]
  all_goals rfl

theorem atot188 : totK PD2M8K2 D2M8K2.u188 = [0, 3559511232297, 12228711802367, 10842977440568, 1932389433843, 63850132885, 0, 0] := by
  rw [show D2M8K2.u188 = KTree.node D2M8K2.u172 (nat_lit 249913) (nat_lit 1439895473) (nat_lit 0) D2M8K2.u187 from rfl, totK_node, atot172, atot187]
  decide +kernel

theorem arows220 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u220 = true := by
  rw [show D2M8K2.u220 = KTree.node D2M8K2.u204 (nat_lit 332806) (nat_lit 2479086455) (nat_lit 0) D2M8K2.u219 from rfl, allE_node, arows204, irow220, arows219]
  all_goals rfl

theorem atot220 : totK PD2M8K2 D2M8K2.u220 = [0, 2151787428820, 9613604050913, 12408859765395, 4029419434834, 299515488964, 1369150432, 0] := by
  rw [show D2M8K2.u220 = KTree.node D2M8K2.u204 (nat_lit 332806) (nat_lit 2479086455) (nat_lit 0) D2M8K2.u219 from rfl, totK_node, atot204, atot219]
  decide +kernel

theorem arows251 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u251 = true := by
  rw [show D2M8K2.u251 = KTree.node D2M8K2.u235 (nat_lit 389388) (nat_lit 3414424540) (nat_lit 0) D2M8K2.u250 from rfl, allE_node, arows235, irow251, arows250]
  all_goals rfl

theorem atot251 : totK PD2M8K2 D2M8K2.u251 = [0, 3248276845519, 11787588435883, 11372823401947, 2271130110730, 67967447995, 0, 0] := by
  rw [show D2M8K2.u251 = KTree.node D2M8K2.u235 (nat_lit 389388) (nat_lit 3414424540) (nat_lit 0) D2M8K2.u250 from rfl, totK_node, atot235, atot250]
  decide +kernel

theorem arows285 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u285 = true := by
  rw [show D2M8K2.u285 = KTree.node D2M8K2.u269 (nat_lit 463778) (nat_lit 3779517726) (nat_lit 0) D2M8K2.u284 from rfl, allE_node, arows269, irow285, arows284]
  all_goals rfl

theorem atot285 : totK PD2M8K2 D2M8K2.u285 = [637203700550, 4790452383251, 11557030601991, 9874732923354, 1981210035436, 61338740791, 0, 0] := by
  rw [show D2M8K2.u285 = KTree.node D2M8K2.u269 (nat_lit 463778) (nat_lit 3779517726) (nat_lit 0) D2M8K2.u284 from rfl, totK_node, atot269, atot284]
  decide +kernel

theorem arows316 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u316 = true := by
  rw [show D2M8K2.u316 = KTree.node D2M8K2.u300 (nat_lit 1017081) (nat_lit 1725113201) (nat_lit 0) D2M8K2.u315 from rfl, allE_node, arows300, irow316, arows315]
  all_goals rfl

theorem atot316 : totK PD2M8K2 D2M8K2.u316 = [1889935344600, 8836328900925, 12613877985338, 4988069603750, 357685470415, 1369150432, 0, 0] := by
  rw [show D2M8K2.u316 = KTree.node D2M8K2.u300 (nat_lit 1017081) (nat_lit 1725113201) (nat_lit 0) D2M8K2.u315 from rfl, totK_node, atot300, atot315]
  decide +kernel

theorem arows348 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u348 = true := by
  rw [show D2M8K2.u348 = KTree.node D2M8K2.u332 (nat_lit 1063977) (nat_lit 1917677306) (nat_lit 0) D2M8K2.u347 from rfl, allE_node, arows332, irow348, arows347]
  all_goals rfl

theorem atot348 : totK PD2M8K2 D2M8K2.u348 = [1654961273610, 7543165731071, 11458781503803, 6833287461951, 1357776728974, 52799255258, 0, 0] := by
  rw [show D2M8K2.u348 = KTree.node D2M8K2.u332 (nat_lit 1063977) (nat_lit 1917677306) (nat_lit 0) D2M8K2.u347 from rfl, totK_node, atot332, atot347]
  decide +kernel

theorem arows379 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u379 = true := by
  rw [show D2M8K2.u379 = KTree.node D2M8K2.u363 (nat_lit 1098131) (nat_lit 2920618751) (nat_lit 0) D2M8K2.u378 from rfl, allE_node, arows363, irow379, arows378]
  all_goals rfl

theorem atot379 : totK PD2M8K2 D2M8K2.u379 = [1613103918421, 7844331406397, 12231062638014, 6144627042747, 749947785558, 18797058808, 0, 0] := by
  rw [show D2M8K2.u379 = KTree.node D2M8K2.u363 (nat_lit 1098131) (nat_lit 2920618751) (nat_lit 0) D2M8K2.u378 from rfl, totK_node, atot363, atot378]
  decide +kernel

theorem arows412 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u412 = true := by
  rw [show D2M8K2.u412 = KTree.node D2M8K2.u396 (nat_lit 1174525) (nat_lit 1010147465) (nat_lit 0) D2M8K2.u411 from rfl, allE_node, arows396, irow412, arows411]
  all_goals rfl

theorem atot412 : totK PD2M8K2 D2M8K2.u412 = [1981691567540, 9135832574737, 12503439112206, 4743662581343, 325621013844, 1138244013, 0, 0] := by
  rw [show D2M8K2.u412 = KTree.node D2M8K2.u396 (nat_lit 1174525) (nat_lit 1010147465) (nat_lit 0) D2M8K2.u411 from rfl, totK_node, atot396, atot411]
  decide +kernel

theorem arows443 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u443 = true := by
  rw [show D2M8K2.u443 = KTree.node D2M8K2.u427 (nat_lit 1214915) (nat_lit 2948508575) (nat_lit 0) D2M8K2.u442 from rfl, allE_node, arows427, irow443, arows442]
  all_goals rfl

theorem atot443 : totK PD2M8K2 D2M8K2.u443 = [1993260921846, 8473825682683, 11867718074536, 5788756235420, 681137151096, 11167240352, 0, 0] := by
  rw [show D2M8K2.u443 = KTree.node D2M8K2.u427 (nat_lit 1214915) (nat_lit 2948508575) (nat_lit 0) D2M8K2.u442 from rfl, totK_node, atot427, atot442]
  decide +kernel

theorem arows475 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u475 = true := by
  rw [show D2M8K2.u475 = KTree.node D2M8K2.u459 (nat_lit 1255836) (nat_lit 3071647410) (nat_lit 0) D2M8K2.u474 from rfl, allE_node, arows459, irow475, arows474]
  all_goals rfl

theorem atot475 : totK PD2M8K2 D2M8K2.u475 = [0, 2640171738397, 10512234685564, 11838567764648, 3339118188232, 204837501523, 1275377855, 0] := by
  rw [show D2M8K2.u475 = KTree.node D2M8K2.u459 (nat_lit 1255836) (nat_lit 3071647410) (nat_lit 0) D2M8K2.u474 from rfl, totK_node, atot459, atot474]
  decide +kernel

theorem arows506 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u506 = true := by
  rw [show D2M8K2.u506 = KTree.node D2M8K2.u490 (nat_lit 1301570) (nat_lit 4117905904) (nat_lit 0) D2M8K2.u505 from rfl, allE_node, arows490, irow506, arows505]
  all_goals rfl

theorem atot506 : totK PD2M8K2 D2M8K2.u506 = [0, 2927402400917, 11067622176631, 11687404819922, 3034221987183, 128795138248, 0, 0] := by
  rw [show D2M8K2.u506 = KTree.node D2M8K2.u490 (nat_lit 1301570) (nat_lit 4117905904) (nat_lit 0) D2M8K2.u505 from rfl, totK_node, atot490, atot505]
  decide +kernel

theorem arows541 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u541 = true := by
  rw [show D2M8K2.u541 = KTree.node D2M8K2.u525 (nat_lit 1355358) (nat_lit 3104946267) (nat_lit 0) D2M8K2.u540 from rfl, allE_node, arows525, irow541, arows540]
  all_goals rfl

theorem atot541 : totK PD2M8K2 D2M8K2.u541 = [0, 1628708016125, 8143175066656, 12273107923309, 5594116494706, 700524852019, 18797058808, 0] := by
  rw [show D2M8K2.u541 = KTree.node D2M8K2.u525 (nat_lit 1355358) (nat_lit 3104946267) (nat_lit 0) D2M8K2.u540 from rfl, totK_node, atot525, atot540]
  decide +kernel

theorem arows572 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u572 = true := by
  rw [show D2M8K2.u572 = KTree.node D2M8K2.u556 (nat_lit 1435425) (nat_lit 1854144789) (nat_lit 0) D2M8K2.u571 from rfl, allE_node, arows556, irow572, arows571]
  all_goals rfl

theorem atot572 : totK PD2M8K2 D2M8K2.u572 = [0, 2065613854775, 9195407022480, 12305794934136, 4509114690718, 364776121288, 5883117146, 0] := by
  rw [show D2M8K2.u572 = KTree.node D2M8K2.u556 (nat_lit 1435425) (nat_lit 1854144789) (nat_lit 0) D2M8K2.u571 from rfl, totK_node, atot556, atot571]
  decide +kernel

theorem arows604 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u604 = true := by
  rw [show D2M8K2.u604 = KTree.node D2M8K2.u588 (nat_lit 1500688) (nat_lit 3688860793) (nat_lit 0) D2M8K2.u603 from rfl, allE_node, arows588, irow604, arows603]
  all_goals rfl

theorem atot604 : totK PD2M8K2 D2M8K2.u604 = [2029730790675, 8512764871177, 11419732190855, 5807735422815, 1016088705815, 36795064199, 0, 0] := by
  rw [show D2M8K2.u604 = KTree.node D2M8K2.u588 (nat_lit 1500688) (nat_lit 3688860793) (nat_lit 0) D2M8K2.u603 from rfl, totK_node, atot588, atot603]
  decide +kernel

theorem arows635 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u635 = true := by
  rw [show D2M8K2.u635 = KTree.node D2M8K2.u619 (nat_lit 1544833) (nat_lit 1567295825) (nat_lit 0) D2M8K2.u634 from rfl, allE_node, arows619, irow635, arows634]
  all_goals rfl

theorem atot635 : totK PD2M8K2 D2M8K2.u635 = [1662880577002, 8169954340154, 12485110542063, 5779758141106, 726396641612, 30413599429, 0, 0] := by
  rw [show D2M8K2.u635 = KTree.node D2M8K2.u619 (nat_lit 1544833) (nat_lit 1567295825) (nat_lit 0) D2M8K2.u634 from rfl, totK_node, atot619, atot634]
  decide +kernel

theorem arows668 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u668 = true := by
  rw [show D2M8K2.u668 = KTree.node D2M8K2.u652 (nat_lit 1621192) (nat_lit 3831628960) (nat_lit 0) D2M8K2.u667 from rfl, allE_node, arows652, irow668, arows667]
  all_goals rfl

theorem atot668 : totK PD2M8K2 D2M8K2.u668 = [2107516443803, 8539973211866, 11336454545615, 5865580909499, 983643457131, 23813810311, 0, 0] := by
  rw [show D2M8K2.u668 = KTree.node D2M8K2.u652 (nat_lit 1621192) (nat_lit 3831628960) (nat_lit 0) D2M8K2.u667 from rfl, totK_node, atot652, atot667]
  decide +kernel

theorem arows699 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u699 = true := by
  rw [show D2M8K2.u699 = KTree.node D2M8K2.u683 (nat_lit 1656138) (nat_lit 3229329029) (nat_lit 0) D2M8K2.u698 from rfl, allE_node, arows683, irow699, arows698]
  all_goals rfl

theorem atot699 : totK PD2M8K2 D2M8K2.u699 = [1546055658120, 7622690261931, 12184903588495, 6433332173948, 797032208932, 19065934916, 0, 0] := by
  rw [show D2M8K2.u699 = KTree.node D2M8K2.u683 (nat_lit 1656138) (nat_lit 3229329029) (nat_lit 0) D2M8K2.u698 from rfl, totK_node, atot683, atot698]
  decide +kernel

theorem arows731 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u731 = true := by
  rw [show D2M8K2.u731 = KTree.node D2M8K2.u715 (nat_lit 1694539) (nat_lit 2140749232) (nat_lit 0) D2M8K2.u730 from rfl, allE_node, arows715, irow731, arows730]
  all_goals rfl

theorem atot731 : totK PD2M8K2 D2M8K2.u731 = [1989013625119, 8851870601025, 12259713429687, 5155971669199, 488482722573, 6115358396, 0, 0] := by
  rw [show D2M8K2.u731 = KTree.node D2M8K2.u715 (nat_lit 1694539) (nat_lit 2140749232) (nat_lit 0) D2M8K2.u730 from rfl, totK_node, atot715, atot730]
  decide +kernel

theorem arows762 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u762 = true := by
  rw [show D2M8K2.u762 = KTree.node D2M8K2.u746 (nat_lit 1732424) (nat_lit 3854819470) (nat_lit 0) D2M8K2.u761 from rfl, allE_node, arows746, irow762, arows761]
  all_goals rfl

theorem atot762 : totK PD2M8K2 D2M8K2.u762 = [440289439084, 5082304649052, 12714592238283, 9109828976792, 1381324883546, 35406168733, 0, 0] := by
  rw [show D2M8K2.u762 = KTree.node D2M8K2.u746 (nat_lit 1732424) (nat_lit 3854819470) (nat_lit 0) D2M8K2.u761 from rfl, totK_node, atot746, atot761]
  decide +kernel

theorem arows796 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u796 = true := by
  rw [show D2M8K2.u796 = KTree.node D2M8K2.u780 (nat_lit 1773839) (nat_lit 2041990513) (nat_lit 0) D2M8K2.u795 from rfl, allE_node, arows780, irow796, arows795]
  all_goals rfl

theorem atot796 : totK PD2M8K2 D2M8K2.u796 = [0, 2032403483397, 9341604928106, 12610660372308, 4298150807966, 262225392612, 1310517177, 0] := by
  rw [show D2M8K2.u796 = KTree.node D2M8K2.u780 (nat_lit 1773839) (nat_lit 2041990513) (nat_lit 0) D2M8K2.u795 from rfl, totK_node, atot780, atot795]
  decide +kernel

theorem arows827 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u827 = true := by
  rw [show D2M8K2.u827 = KTree.node D2M8K2.u811 (nat_lit 1878001) (nat_lit 1406327514) (nat_lit 0) D2M8K2.u826 from rfl, allE_node, arows811, irow827, arows826]
  all_goals rfl

theorem atot827 : totK PD2M8K2 D2M8K2.u827 = [0, 2563009165716, 10305450394930, 11884810897920, 3651371439678, 231766867242, 1217496766, 0] := by
  rw [show D2M8K2.u827 = KTree.node D2M8K2.u811 (nat_lit 1878001) (nat_lit 1406327514) (nat_lit 0) D2M8K2.u826 from rfl, totK_node, atot811, atot826]
  decide +kernel

theorem arows859 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u859 = true := by
  rw [show D2M8K2.u859 = KTree.node D2M8K2.u843 (nat_lit 1913304) (nat_lit 1628380929) (nat_lit 0) D2M8K2.u858 from rfl, allE_node, arows843, irow859, arows858]
  all_goals rfl

theorem atot859 : totK PD2M8K2 D2M8K2.u859 = [0, 1979129314488, 8677847784659, 11891933426275, 5179872650452, 645232735942, 18874610232, 0] := by
  rw [show D2M8K2.u859 = KTree.node D2M8K2.u843 (nat_lit 1913304) (nat_lit 1628380929) (nat_lit 0) D2M8K2.u858 from rfl, totK_node, atot843, atot858]
  decide +kernel

theorem arows890 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u890 = true := by
  rw [show D2M8K2.u890 = KTree.node D2M8K2.u874 (nat_lit 1955262) (nat_lit 3971616199) (nat_lit 0) D2M8K2.u889 from rfl, allE_node, arows874, irow890, arows889]
  all_goals rfl

theorem atot890 : totK PD2M8K2 D2M8K2.u890 = [437191058986, 3259387326217, 9487945599747, 11221824662893, 3939571395926, 307788782750, 4914284239, 0] := by
  rw [show D2M8K2.u890 = KTree.node D2M8K2.u874 (nat_lit 1955262) (nat_lit 3971616199) (nat_lit 0) D2M8K2.u889 from rfl, totK_node, atot874, atot889]
  decide +kernel

theorem arows923 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u923 = true := by
  rw [show D2M8K2.u923 = KTree.node D2M8K2.u907 (nat_lit 2010707) (nat_lit 2070714339) (nat_lit 0) D2M8K2.u922 from rfl, allE_node, arows907, irow923, arows922]
  all_goals rfl

theorem atot923 : totK PD2M8K2 D2M8K2.u923 = [2020751517044, 9187272399339, 12490910082279, 4664943151448, 338614364492, 1369150432, 0, 0] := by
  rw [show D2M8K2.u923 = KTree.node D2M8K2.u907 (nat_lit 2010707) (nat_lit 2070714339) (nat_lit 0) D2M8K2.u922 from rfl, totK_node, atot907, atot922]
  decide +kernel

theorem arows954 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u954 = true := by
  rw [show D2M8K2.u954 = KTree.node D2M8K2.u938 (nat_lit 2058394) (nat_lit 3900895255) (nat_lit 0) D2M8K2.u953 from rfl, allE_node, arows938, irow954, arows953]
  all_goals rfl

theorem atot954 : totK PD2M8K2 D2M8K2.u954 = [1638947043019, 7440541889038, 11506472101222, 6923042400627, 1294048769811, 48715757244, 0, 0] := by
  rw [show D2M8K2.u954 = KTree.node D2M8K2.u938 (nat_lit 2058394) (nat_lit 3900895255) (nat_lit 0) D2M8K2.u953 from rfl, totK_node, atot938, atot953]
  decide +kernel

theorem arows986 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u986 = true := by
  rw [show D2M8K2.u986 = KTree.node D2M8K2.u970 (nat_lit 2092998) (nat_lit 2537696831) (nat_lit 0) D2M8K2.u985 from rfl, allE_node, arows970, irow986, arows985]
  all_goals rfl

theorem atot986 : totK PD2M8K2 D2M8K2.u986 = [1575236328664, 7857257325781, 12332310108711, 6107335127298, 749967334648, 18797058808, 0, 0] := by
  rw [show D2M8K2.u986 = KTree.node D2M8K2.u970 (nat_lit 2092998) (nat_lit 2537696831) (nat_lit 0) D2M8K2.u985 from rfl, totK_node, atot970, atot985]
  decide +kernel

theorem arows1017 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1017 = true := by
  rw [show D2M8K2.u1017 = KTree.node D2M8K2.u1001 (nat_lit 2131600) (nat_lit 2745016400) (nat_lit 0) D2M8K2.u1016 from rfl, allE_node, arows1001, irow1017, arows1016]
  all_goals rfl

theorem atot1017 : totK PD2M8K2 D2M8K2.u1017 = [1985723861530, 8734790182617, 12067465593633, 5353872692693, 600030238434, 14345316470, 0, 0] := by
  rw [show D2M8K2.u1017 = KTree.node D2M8K2.u1001 (nat_lit 2131600) (nat_lit 2745016400) (nat_lit 0) D2M8K2.u1016 from rfl, totK_node, atot1001, atot1016]
  decide +kernel

theorem arows1053 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1053 = true := by
  rw [show D2M8K2.u1053 = KTree.node D2M8K2.u1037 (nat_lit 2167076) (nat_lit 2768977572) (nat_lit 0) D2M8K2.u1052 from rfl, allE_node, arows1037, irow1053, arows1052]
  all_goals rfl

theorem atot1053 : totK PD2M8K2 D2M8K2.u1053 = [2102405875695, 9092842879098, 12067672951005, 4912468077836, 445979703382, 5858862459, 0, 0] := by
  rw [show D2M8K2.u1053 = KTree.node D2M8K2.u1037 (nat_lit 2167076) (nat_lit 2768977572) (nat_lit 0) D2M8K2.u1052 from rfl, totK_node, atot1037, atot1052]
  decide +kernel

theorem arows1084 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1084 = true := by
  rw [show D2M8K2.u1084 = KTree.node D2M8K2.u1068 (nat_lit 2251515) (nat_lit 3285790262) (nat_lit 0) D2M8K2.u1083 from rfl, allE_node, arows1068, irow1084, arows1083]
  all_goals rfl

theorem atot1084 : totK PD2M8K2 D2M8K2.u1084 = [0, 2811072745722, 10979729462051, 11553495412451, 2956760015589, 175456202453, 1209030869, 0] := by
  rw [show D2M8K2.u1084 = KTree.node D2M8K2.u1068 (nat_lit 2251515) (nat_lit 3285790262) (nat_lit 0) D2M8K2.u1083 from rfl, totK_node, atot1068, atot1083]
  decide +kernel

theorem arows1116 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1116 = true := by
  rw [show D2M8K2.u1116 = KTree.node D2M8K2.u1100 (nat_lit 2295141) (nat_lit 1495181049) (nat_lit 0) D2M8K2.u1115 from rfl, allE_node, arows1100, irow1116, arows1115]
  all_goals rfl

theorem atot1116 : totK PD2M8K2 D2M8K2.u1116 = [0, 3057047366564, 11360756705121, 11519701487087, 2811170416952, 119355665737, 0, 0] := by
  rw [show D2M8K2.u1116 = KTree.node D2M8K2.u1100 (nat_lit 2295141) (nat_lit 1495181049) (nat_lit 0) D2M8K2.u1115 from rfl, totK_node, atot1100, atot1115]
  decide +kernel

theorem arows1147 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1147 = true := by
  rw [show D2M8K2.u1147 = KTree.node D2M8K2.u1131 (nat_lit 2375937) (nat_lit 1541330370) (nat_lit 0) D2M8K2.u1146 from rfl, allE_node, arows1131, irow1147, arows1146]
  all_goals rfl

theorem atot1147 : totK PD2M8K2 D2M8K2.u1147 = [0, 3379184854875, 11960573054106, 11153705092080, 2220322376696, 68968225506, 0, 0] := by
  rw [show D2M8K2.u1147 = KTree.node D2M8K2.u1131 (nat_lit 2375937) (nat_lit 1541330370) (nat_lit 0) D2M8K2.u1146 from rfl, totK_node, atot1131, atot1146]
  decide +kernel

theorem arows1180 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1180 = true := by
  rw [show D2M8K2.u1180 = KTree.node D2M8K2.u1164 (nat_lit 2428705) (nat_lit 1561875799) (nat_lit 0) D2M8K2.u1179 from rfl, allE_node, arows1164, irow1180, arows1179]
  all_goals rfl

theorem atot1180 : totK PD2M8K2 D2M8K2.u1180 = [751404570366, 3550503813634, 8439419024554, 10829588195475, 4445690987211, 443986553077, 6115358396, 0] := by
  rw [show D2M8K2.u1180 = KTree.node D2M8K2.u1164 (nat_lit 2428705) (nat_lit 1561875799) (nat_lit 0) D2M8K2.u1179 from rfl, totK_node, atot1164, atot1179]
  decide +kernel

theorem arows1211 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1211 = true := by
  rw [show D2M8K2.u1211 = KTree.node D2M8K2.u1195 (nat_lit 2510403) (nat_lit 1668821184) (nat_lit 0) D2M8K2.u1210 from rfl, allE_node, arows1195, irow1211, arows1210]
  all_goals rfl

theorem atot1211 : totK PD2M8K2 D2M8K2.u1211 = [1863596377836, 8840576438838, 12638709183682, 5020121496185, 360408157464, 1369150432, 0, 0] := by
  rw [show D2M8K2.u1211 = KTree.node D2M8K2.u1195 (nat_lit 2510403) (nat_lit 1668821184) (nat_lit 0) D2M8K2.u1210 from rfl, totK_node, atot1195, atot1210]
  decide +kernel

theorem arows1243 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1243 = true := by
  rw [show D2M8K2.u1243 = KTree.node D2M8K2.u1227 (nat_lit 2557193) (nat_lit 1758654790) (nat_lit 0) D2M8K2.u1242 from rfl, allE_node, arows1227, irow1243, arows1242]
  all_goals rfl

theorem atot1243 : totK PD2M8K2 D2M8K2.u1243 = [1580924078689, 7349550607256, 11512268517796, 6984810752686, 1431614862400, 56602985873, 0, 0] := by
  rw [show D2M8K2.u1243 = KTree.node D2M8K2.u1227 (nat_lit 2557193) (nat_lit 1758654790) (nat_lit 0) D2M8K2.u1242 from rfl, totK_node, atot1227, atot1242]
  decide +kernel

theorem arows1274 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1274 = true := by
  rw [show D2M8K2.u1274 = KTree.node D2M8K2.u1258 (nat_lit 2592143) (nat_lit 2754186090) (nat_lit 0) D2M8K2.u1273 from rfl, allE_node, arows1258, irow1274, arows1273]
  all_goals rfl

theorem atot1274 : totK PD2M8K2 D2M8K2.u1274 = [1733443130489, 7971590790263, 12058342510854, 6146389651379, 763299203222, 18797058808, 0, 0] := by
  rw [show D2M8K2.u1274 = KTree.node D2M8K2.u1258 (nat_lit 2592143) (nat_lit 2754186090) (nat_lit 0) D2M8K2.u1273 from rfl, totK_node, atot1258, atot1273]
  decide +kernel

theorem arows1308 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1308 = true := by
  rw [show D2M8K2.u1308 = KTree.node D2M8K2.u1292 (nat_lit 2631127) (nat_lit 2371469307) (nat_lit 0) D2M8K2.u1307 from rfl, allE_node, arows1292, irow1308, arows1307]
  all_goals rfl

theorem atot1308 : totK PD2M8K2 D2M8K2.u1308 = [1744171928677, 8185024041780, 12138229788446, 5924100263806, 740119783484, 19065934916, 0, 0] := by
  rw [show D2M8K2.u1308 = KTree.node D2M8K2.u1292 (nat_lit 2631127) (nat_lit 2371469307) (nat_lit 0) D2M8K2.u1307 from rfl, totK_node, atot1292, atot1307]
  decide +kernel

theorem arows1339 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1339 = true := by
  rw [show D2M8K2.u1339 = KTree.node D2M8K2.u1323 (nat_lit 2707417) (nat_lit 1403639144) (nat_lit 0) D2M8K2.u1338 from rfl, allE_node, arows1323, irow1339, arows1338]
  all_goals rfl

theorem atot1339 : totK PD2M8K2 D2M8K2.u1339 = [2112320242452, 9074382806993, 12115426084929, 5100715193126, 432157338415, 2385942608, 0, 0] := by
  rw [show D2M8K2.u1339 = KTree.node D2M8K2.u1323 (nat_lit 2707417) (nat_lit 1403639144) (nat_lit 0) D2M8K2.u1338 from rfl, totK_node, atot1323, atot1338]
  decide +kernel

theorem arows1371 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1371 = true := by
  rw [show D2M8K2.u1371 = KTree.node D2M8K2.u1355 (nat_lit 2746525) (nat_lit 1112142881) (nat_lit 0) D2M8K2.u1370 from rfl, allE_node, arows1355, irow1371, arows1370]
  all_goals rfl

theorem atot1371 : totK PD2M8K2 D2M8K2.u1371 = [0, 2894542007699, 10920121575007, 11445039127027, 3105202101007, 192787949786, 1369150432, 0] := by
  rw [show D2M8K2.u1371 = KTree.node D2M8K2.u1355 (nat_lit 2746525) (nat_lit 1112142881) (nat_lit 0) D2M8K2.u1370 from rfl, totK_node, atot1355, atot1370]
  decide +kernel

theorem arows1402 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1402 = true := by
  rw [show D2M8K2.u1402 = KTree.node D2M8K2.u1386 (nat_lit 2788457) (nat_lit 1759300429) (nat_lit 0) D2M8K2.u1401 from rfl, allE_node, arows1386, irow1402, arows1401]
  all_goals rfl

theorem atot1402 : totK PD2M8K2 D2M8K2.u1402 = [0, 2463644282292, 10117885803366, 12254607988322, 3788695458709, 170024275731, 0, 0] := by
  rw [show D2M8K2.u1402 = KTree.node D2M8K2.u1386 (nat_lit 2788457) (nat_lit 1759300429) (nat_lit 0) D2M8K2.u1401 from rfl, totK_node, atot1386, atot1401]
  decide +kernel

theorem arows1435 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1435 = true := by
  rw [show D2M8K2.u1435 = KTree.node D2M8K2.u1419 (nat_lit 2844649) (nat_lit 492121461) (nat_lit 0) D2M8K2.u1434 from rfl, allE_node, arows1419, irow1435, arows1434]
  all_goals rfl

theorem atot1435 : totK PD2M8K2 D2M8K2.u1435 = [0, 1987346834567, 8996967785896, 12308389045675, 4861830271750, 419757023323, 6301476269, 0] := by
  rw [show D2M8K2.u1435 = KTree.node D2M8K2.u1419 (nat_lit 2844649) (nat_lit 492121461) (nat_lit 0) D2M8K2.u1434 from rfl, totK_node, atot1419, atot1434]
  decide +kernel

theorem arows1466 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1466 = true := by
  rw [show D2M8K2.u1466 = KTree.node D2M8K2.u1450 (nat_lit 2885500) (nat_lit 3109862089) (nat_lit 0) D2M8K2.u1465 from rfl, allE_node, arows1450, irow1466, arows1465]
  all_goals rfl

theorem atot1466 : totK PD2M8K2 D2M8K2.u1466 = [0, 2015059550414, 9048294150162, 12260958321748, 4857833301123, 424375295183, 6363931553, 0] := by
  rw [show D2M8K2.u1466 = KTree.node D2M8K2.u1450 (nat_lit 2885500) (nat_lit 3109862089) (nat_lit 0) D2M8K2.u1465 from rfl, totK_node, atot1450, atot1465]
  decide +kernel

theorem arows1498 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1498 = true := by
  rw [show D2M8K2.u1498 = KTree.node D2M8K2.u1482 (nat_lit 2966731) (nat_lit 1647951822) (nat_lit 0) D2M8K2.u1497 from rfl, allE_node, arows1482, irow1498, arows1497]
  all_goals rfl

theorem atot1498 : totK PD2M8K2 D2M8K2.u1498 = [0, 1377257977655, 7115764553890, 12120734403692, 6791033619918, 997816402528, 32664957003, 0] := by
  rw [show D2M8K2.u1498 = KTree.node D2M8K2.u1482 (nat_lit 2966731) (nat_lit 1647951822) (nat_lit 0) D2M8K2.u1497 from rfl, totK_node, atot1482, atot1497]
  decide +kernel

theorem arows1529 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1529 = true := by
  rw [show D2M8K2.u1529 = KTree.node D2M8K2.u1513 (nat_lit 3003513) (nat_lit 1829384408) (nat_lit 0) D2M8K2.u1528 from rfl, allE_node, arows1513, irow1529, arows1528]
  all_goals rfl

theorem atot1529 : totK PD2M8K2 D2M8K2.u1529 = [0, 2033460658181, 9308626970299, 12516872448249, 4427297278754, 308174587443, 1369150432, 0] := by
  rw [show D2M8K2.u1529 = KTree.node D2M8K2.u1513 (nat_lit 3003513) (nat_lit 1829384408) (nat_lit 0) D2M8K2.u1528 from rfl, totK_node, atot1513, atot1528]
  decide +kernel

theorem arows1564 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1564 = true := by
  rw [show D2M8K2.u1564 = KTree.node D2M8K2.u1548 (nat_lit 3085788) (nat_lit 2994405604) (nat_lit 0) D2M8K2.u1563 from rfl, allE_node, arows1548, irow1564, arows1563]
  all_goals rfl

theorem atot1564 : totK PD2M8K2 D2M8K2.u1564 = [0, 2013486191525, 8853047980902, 12135675916269, 5043624516320, 506825130007, 14222663156, 0] := by
  rw [show D2M8K2.u1564 = KTree.node D2M8K2.u1548 (nat_lit 3085788) (nat_lit 2994405604) (nat_lit 0) D2M8K2.u1563 from rfl, totK_node, atot1548, atot1563]
  decide +kernel

theorem arows1595 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1595 = true := by
  rw [show D2M8K2.u1595 = KTree.node D2M8K2.u1579 (nat_lit 3124758) (nat_lit 3782252301) (nat_lit 0) D2M8K2.u1594 from rfl, allE_node, arows1579, irow1595, arows1594]
  all_goals rfl

theorem atot1595 : totK PD2M8K2 D2M8K2.u1595 = [0, 2013968688706, 8743358448319, 12031138781896, 5250267072523, 555382130615, 13996399881, 0] := by
  rw [show D2M8K2.u1595 = KTree.node D2M8K2.u1579 (nat_lit 3124758) (nat_lit 3782252301) (nat_lit 0) D2M8K2.u1594 from rfl, totK_node, atot1579, atot1594]
  decide +kernel

theorem arows1627 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1627 = true := by
  rw [show D2M8K2.u1627 = KTree.node D2M8K2.u1611 (nat_lit 3160519) (nat_lit 2209687468) (nat_lit 0) D2M8K2.u1626 from rfl, allE_node, arows1611, irow1627, arows1626]
  all_goals rfl

theorem atot1627 : totK PD2M8K2 D2M8K2.u1627 = [0, 2008348425205, 8874288299689, 12140507803362, 4946322708748, 457911965801, 9331050282, 0] := by
  rw [show D2M8K2.u1627 = KTree.node D2M8K2.u1611 (nat_lit 3160519) (nat_lit 2209687468) (nat_lit 0) D2M8K2.u1626 from rfl, totK_node, atot1611, atot1626]
  decide +kernel

theorem arows1658 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1658 = true := by
  rw [show D2M8K2.u1658 = KTree.node D2M8K2.u1642 (nat_lit 3201414) (nat_lit 2752167444) (nat_lit 0) D2M8K2.u1657 from rfl, allE_node, arows1642, irow1658, arows1657]
  all_goals rfl

theorem atot1658 : totK PD2M8K2 D2M8K2.u1658 = [0, 2019269348258, 8890589716547, 12216001857165, 5077851103675, 443561565923, 6287399960, 0] := by
  rw [show D2M8K2.u1658 = KTree.node D2M8K2.u1642 (nat_lit 3201414) (nat_lit 2752167444) (nat_lit 0) D2M8K2.u1657 from rfl, totK_node, atot1642, atot1657]
  decide +kernel

theorem arows1691 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1691 = true := by
  rw [show D2M8K2.u1691 = KTree.node D2M8K2.u1675 (nat_lit 3238030) (nat_lit 3708048096) (nat_lit 0) D2M8K2.u1690 from rfl, allE_node, arows1675, irow1691, arows1690]
  all_goals rfl

theorem atot1691 : totK PD2M8K2 D2M8K2.u1691 = [0, 0, 3448508475328, 12057743978951, 10662325010843, 1999210830158, 72481833906, 0] := by
  rw [show D2M8K2.u1691 = KTree.node D2M8K2.u1675 (nat_lit 3238030) (nat_lit 3708048096) (nat_lit 0) D2M8K2.u1690 from rfl, totK_node, atot1675, atot1690]
  decide +kernel

theorem arows1722 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1722 = true := by
  rw [show D2M8K2.u1722 = KTree.node D2M8K2.u1706 (nat_lit 3321678) (nat_lit 3469856854) (nat_lit 0) D2M8K2.u1721 from rfl, allE_node, arows1706, irow1722, arows1721]
  all_goals rfl

theorem atot1722 : totK PD2M8K2 D2M8K2.u1722 = [0, 0, 2418724944450, 9966597620929, 11774745707422, 3792692450074, 300652891627, 1369150432] := by
  rw [show D2M8K2.u1722 = KTree.node D2M8K2.u1706 (nat_lit 3321678) (nat_lit 3469856854) (nat_lit 0) D2M8K2.u1721 from rfl, totK_node, atot1706, atot1721]
  decide +kernel

theorem arows1754 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1754 = true := by
  rw [show D2M8K2.u1754 = KTree.node D2M8K2.u1738 (nat_lit 3401953) (nat_lit 1499270450) (nat_lit 0) D2M8K2.u1753 from rfl, allE_node, arows1738, irow1754, arows1753]
  all_goals rfl

theorem atot1754 : totK PD2M8K2 D2M8K2.u1754 = [0, 0, 3698581763099, 12478260196662, 10432139804765, 1783222714584, 64320459200, 0] := by
  rw [show D2M8K2.u1754 = KTree.node D2M8K2.u1738 (nat_lit 3401953) (nat_lit 1499270450) (nat_lit 0) D2M8K2.u1753 from rfl, totK_node, atot1738, atot1753]
  decide +kernel

theorem arows1785 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1785 = true := by
  rw [show D2M8K2.u1785 = KTree.node D2M8K2.u1769 (nat_lit 3462184) (nat_lit 3199020963) (nat_lit 0) D2M8K2.u1784 from rfl, allE_node, arows1769, irow1785, arows1784]
  all_goals rfl

theorem atot1785 : totK PD2M8K2 D2M8K2.u1785 = [0, 1636922335308, 7621445339934, 11743903387521, 6637511188235, 1016481308345, 33598280809, 0] := by
  rw [show D2M8K2.u1785 = KTree.node D2M8K2.u1769 (nat_lit 3462184) (nat_lit 3199020963) (nat_lit 0) D2M8K2.u1784 from rfl, totK_node, atot1769, atot1784]
  decide +kernel

theorem arows1819 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1819 = true := by
  rw [show D2M8K2.u1819 = KTree.node D2M8K2.u1803 (nat_lit 4020439) (nat_lit 2316706234) (nat_lit 0) D2M8K2.u1818 from rfl, allE_node, arows1803, irow1819, arows1818]
  all_goals rfl

theorem atot1819 : totK PD2M8K2 D2M8K2.u1819 = [0, 2055215580133, 9107230191313, 12424853681104, 4773307137318, 343017457479, 1369150432, 0] := by
  rw [show D2M8K2.u1819 = KTree.node D2M8K2.u1803 (nat_lit 4020439) (nat_lit 2316706234) (nat_lit 0) D2M8K2.u1818 from rfl, totK_node, atot1803, atot1818]
  decide +kernel

theorem arows1850 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1850 = true := by
  rw [show D2M8K2.u1850 = KTree.node D2M8K2.u1834 (nat_lit 4066613) (nat_lit 2399141089) (nat_lit 0) D2M8K2.u1849 from rfl, allE_node, arows1834, irow1850, arows1849]
  all_goals rfl

theorem atot1850 : totK PD2M8K2 D2M8K2.u1850 = [0, 2107096505998, 9022302258813, 12080072345253, 5157690927035, 504009268266, 6575010705, 0] := by
  rw [show D2M8K2.u1850 = KTree.node D2M8K2.u1834 (nat_lit 4066613) (nat_lit 2399141089) (nat_lit 0) D2M8K2.u1849 from rfl, totK_node, atot1834, atot1849]
  decide +kernel

theorem arows1882 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1882 = true := by
  rw [show D2M8K2.u1882 = KTree.node D2M8K2.u1866 (nat_lit 4102598) (nat_lit 4180403854) (nat_lit 0) D2M8K2.u1881 from rfl, allE_node, arows1866, irow1882, arows1881]
  all_goals rfl

theorem atot1882 : totK PD2M8K2 D2M8K2.u1882 = [0, 1545881644484, 7731177205178, 12284828796124, 6174029300527, 740112089669, 18797058808, 0] := by
  rw [show D2M8K2.u1882 = KTree.node D2M8K2.u1866 (nat_lit 4102598) (nat_lit 4180403854) (nat_lit 0) D2M8K2.u1881 from rfl, totK_node, atot1866, atot1881]
  decide +kernel

theorem arows1913 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1913 = true := by
  rw [show D2M8K2.u1913 = KTree.node D2M8K2.u1897 (nat_lit 4182631) (nat_lit 2386208983) (nat_lit 0) D2M8K2.u1912 from rfl, allE_node, arows1897, irow1913, arows1912]
  all_goals rfl

theorem atot1913 : totK PD2M8K2 D2M8K2.u1913 = [0, 1962297069091, 8812837543818, 12365089449798, 5055797719261, 444455250285, 6115358396, 0] := by
  rw [show D2M8K2.u1913 = KTree.node D2M8K2.u1897 (nat_lit 4182631) (nat_lit 2386208983) (nat_lit 0) D2M8K2.u1912 from rfl, totK_node, atot1897, atot1912]
  decide +kernel

theorem arows1946 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1946 = true := by
  rw [show D2M8K2.u1946 = KTree.node D2M8K2.u1930 (nat_lit 4219992) (nat_lit 3578061234) (nat_lit 0) D2M8K2.u1945 from rfl, allE_node, arows1930, irow1946, arows1945]
  all_goals rfl

theorem atot1946 : totK PD2M8K2 D2M8K2.u1946 = [0, 1668840655035, 8099388035291, 12221453418163, 6024990176150, 744563837977, 19976620017, 0] := by
  rw [show D2M8K2.u1946 = KTree.node D2M8K2.u1930 (nat_lit 4219992) (nat_lit 3578061234) (nat_lit 0) D2M8K2.u1945 from rfl, totK_node, atot1930, atot1945]
  decide +kernel

theorem arows1977 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u1977 = true := by
  rw [show D2M8K2.u1977 = KTree.node D2M8K2.u1961 (nat_lit 4511190) (nat_lit 3867271593) (nat_lit 0) D2M8K2.u1976 from rfl, allE_node, arows1961, irow1977, arows1976]
  all_goals rfl

theorem atot1977 : totK PD2M8K2 D2M8K2.u1977 = [0, 1991202340178, 8942730726978, 12466934634755, 4883487059644, 354037438803, 1369150432, 0] := by
  rw [show D2M8K2.u1977 = KTree.node D2M8K2.u1961 (nat_lit 4511190) (nat_lit 3867271593) (nat_lit 0) D2M8K2.u1976 from rfl, totK_node, atot1961, atot1976]
  decide +kernel

theorem arows2009 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2009 = true := by
  rw [show D2M8K2.u2009 = KTree.node D2M8K2.u1993 (nat_lit 4558584) (nat_lit 3610902917) (nat_lit 0) D2M8K2.u2008 from rfl, allE_node, arows1993, irow2009, arows2008]
  all_goals rfl

theorem atot2009 : totK PD2M8K2 D2M8K2.u2009 = [0, 2002382298488, 8882895088452, 12207809782137, 5305182413034, 518102358528, 6634014755, 0] := by
  rw [show D2M8K2.u2009 = KTree.node D2M8K2.u1993 (nat_lit 4558584) (nat_lit 3610902917) (nat_lit 0) D2M8K2.u2008 from rfl, totK_node, atot1993, atot2008]
  decide +kernel

theorem arows2040 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2040 = true := by
  rw [show D2M8K2.u2040 = KTree.node D2M8K2.u2024 (nat_lit 4637224) (nat_lit 2296222639) (nat_lit 0) D2M8K2.u2039 from rfl, allE_node, arows2024, irow2040, arows2039]
  all_goals rfl

theorem atot2040 : totK PD2M8K2 D2M8K2.u2040 = [0, 1636006255285, 7868498604720, 12156812070391, 6168903170251, 749526967790, 19065934916, 0] := by
  rw [show D2M8K2.u2040 = KTree.node D2M8K2.u2024 (nat_lit 4637224) (nat_lit 2296222639) (nat_lit 0) D2M8K2.u2039 from rfl, totK_node, atot2024, atot2039]
  decide +kernel

theorem arows2077 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2077 = true := by
  rw [show D2M8K2.u2077 = KTree.node D2M8K2.u2061 (nat_lit 4672704) (nat_lit 3573435673) (nat_lit 0) D2M8K2.u2076 from rfl, allE_node, arows2061, irow2077, arows2076]
  all_goals rfl

theorem atot2077 : totK PD2M8K2 D2M8K2.u2077 = [0, 1870160941739, 8710375495707, 12458173974202, 5117180386852, 445967007396, 6115358396, 0] := by
  rw [show D2M8K2.u2077 = KTree.node D2M8K2.u2061 (nat_lit 4672704) (nat_lit 3573435673) (nat_lit 0) D2M8K2.u2076 from rfl, totK_node, atot2061, atot2076]
  decide +kernel

theorem arows2108 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2108 = true := by
  rw [show D2M8K2.u2108 = KTree.node D2M8K2.u2092 (nat_lit 4711558) (nat_lit 2475709194) (nat_lit 0) D2M8K2.u2107 from rfl, allE_node, arows2092, irow2108, arows2107]
  all_goals rfl

theorem atot2108 : totK PD2M8K2 D2M8K2.u2108 = [0, 1807191570847, 8220423691576, 12074464623441, 5982449572237, 746004619181, 20093994127, 0] := by
  rw [show D2M8K2.u2108 = KTree.node D2M8K2.u2092 (nat_lit 4711558) (nat_lit 2475709194) (nat_lit 0) D2M8K2.u2107 from rfl, totK_node, atot2092, atot2107]
  decide +kernel

theorem arows2140 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2140 = true := by
  rw [show D2M8K2.u2140 = KTree.node D2M8K2.u2124 (nat_lit 4998728) (nat_lit 3722817438) (nat_lit 0) D2M8K2.u2139 from rfl, allE_node, arows2124, irow2140, arows2139]
  all_goals rfl

theorem atot2140 : totK PD2M8K2 D2M8K2.u2140 = [0, 1874152846765, 8842264109984, 12589405622177, 4898638835682, 354823326095, 1369150432, 0] := by
  rw [show D2M8K2.u2140 = KTree.node D2M8K2.u2124 (nat_lit 4998728) (nat_lit 3722817438) (nat_lit 0) D2M8K2.u2139 from rfl, totK_node, atot2124, atot2139]
  decide +kernel

theorem arows2171 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2171 = true := by
  rw [show D2M8K2.u2171 = KTree.node D2M8K2.u2155 (nat_lit 5049542) (nat_lit 4180272124) (nat_lit 0) D2M8K2.u2170 from rfl, allE_node, arows2155, irow2171, arows2170]
  all_goals rfl

theorem atot2171 : totK PD2M8K2 D2M8K2.u2171 = [0, 2306974459872, 9668119812029, 12102143139101, 4438436735613, 330205908321, 1415142070, 0] := by
  rw [show D2M8K2.u2171 = KTree.node D2M8K2.u2155 (nat_lit 5049542) (nat_lit 4180272124) (nat_lit 0) D2M8K2.u2170 from rfl, totK_node, atot2155, atot2170]
  decide +kernel

theorem arows2204 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2204 = true := by
  rw [show D2M8K2.u2204 = KTree.node D2M8K2.u2188 (nat_lit 5088452) (nat_lit 3397698919) (nat_lit 0) D2M8K2.u2203 from rfl, allE_node, arows2188, irow2204, arows2203]
  all_goals rfl

theorem atot2204 : totK PD2M8K2 D2M8K2.u2204 = [0, 1598032788042, 7892453910787, 12378804685735, 5950741523518, 690907695371, 18797058808, 0] := by
  rw [show D2M8K2.u2204 = KTree.node D2M8K2.u2188 (nat_lit 5088452) (nat_lit 3397698919) (nat_lit 0) D2M8K2.u2203 from rfl, totK_node, atot2188, atot2203]
  decide +kernel

theorem arows2235 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2235 = true := by
  rw [show D2M8K2.u2235 = KTree.node D2M8K2.u2219 (nat_lit 5126291) (nat_lit 2731086291) (nat_lit 0) D2M8K2.u2234 from rfl, allE_node, arows2219, irow2235, arows2234]
  all_goals rfl

theorem atot2235 : totK PD2M8K2 D2M8K2.u2235 = [0, 1908659976128, 8445053840740, 11994964190476, 5575476278471, 671156120682, 19065934916, 0] := by
  rw [show D2M8K2.u2235 = KTree.node D2M8K2.u2219 (nat_lit 5126291) (nat_lit 2731086291) (nat_lit 0) D2M8K2.u2234 from rfl, totK_node, atot2219, atot2234]
  decide +kernel

theorem arows2267 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2267 = true := by
  rw [show D2M8K2.u2267 = KTree.node D2M8K2.u2251 (nat_lit 5164154) (nat_lit 4034456359) (nat_lit 0) D2M8K2.u2266 from rfl, allE_node, arows2251, irow2267, arows2266]
  all_goals rfl

theorem atot2267 : totK PD2M8K2 D2M8K2.u2267 = [0, 1769990973643, 8502412222001, 12475559464503, 5325140734481, 486328311843, 6115358396, 0] := by
  rw [show D2M8K2.u2267 = KTree.node D2M8K2.u2251 (nat_lit 5164154) (nat_lit 4034456359) (nat_lit 0) D2M8K2.u2266 from rfl, totK_node, atot2251, atot2266]
  decide +kernel

theorem arows2298 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2298 = true := by
  rw [show D2M8K2.u2298 = KTree.node D2M8K2.u2282 (nat_lit 5494320) (nat_lit 3602122962) (nat_lit 0) D2M8K2.u2297 from rfl, allE_node, arows2282, irow2298, arows2297]
  all_goals rfl

theorem atot2298 : totK PD2M8K2 D2M8K2.u2298 = [0, 2024861666475, 9189049907682, 12444435000373, 4630059294142, 339008319961, 1369150432, 0] := by
  rw [show D2M8K2.u2298 = KTree.node D2M8K2.u2282 (nat_lit 5494320) (nat_lit 3602122962) (nat_lit 0) D2M8K2.u2297 from rfl, totK_node, atot2282, atot2297]
  decide +kernel

theorem arows2332 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2332 = true := by
  rw [show D2M8K2.u2332 = KTree.node D2M8K2.u2316 (nat_lit 5541454) (nat_lit 4014680920) (nat_lit 0) D2M8K2.u2331 from rfl, allE_node, arows2316, irow2332, arows2331]
  all_goals rfl

theorem atot2332 : totK PD2M8K2 D2M8K2.u2332 = [0, 1844775124445, 8306803022997, 12188568891274, 5943733512001, 707334301153, 12407785584, 0] := by
  rw [show D2M8K2.u2332 = KTree.node D2M8K2.u2316 (nat_lit 5541454) (nat_lit 4014680920) (nat_lit 0) D2M8K2.u2331 from rfl, totK_node, atot2316, atot2331]
  decide +kernel

theorem arows2363 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2363 = true := by
  rw [show D2M8K2.u2363 = KTree.node D2M8K2.u2347 (nat_lit 5578942) (nat_lit 3698649821) (nat_lit 0) D2M8K2.u2362 from rfl, allE_node, arows2347, irow2363, arows2362]
  all_goals rfl

theorem atot2363 : totK PD2M8K2 D2M8K2.u2363 = [0, 1790862824432, 8542389089712, 12444630923827, 5439929270271, 500099938619, 6601594569, 0] := by
  rw [show D2M8K2.u2363 = KTree.node D2M8K2.u2347 (nat_lit 5578942) (nat_lit 3698649821) (nat_lit 0) D2M8K2.u2362 from rfl, totK_node, atot2347, atot2362]
  decide +kernel

theorem arows2395 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2395 = true := by
  rw [show D2M8K2.u2395 = KTree.node D2M8K2.u2379 (nat_lit 5619368) (nat_lit 2026075450) (nat_lit 0) D2M8K2.u2394 from rfl, allE_node, arows2379, irow2395, arows2394]
  all_goals rfl

theorem atot2395 : totK PD2M8K2 D2M8K2.u2395 = [0, 1997622323045, 8700903981997, 12164196923701, 5449000528652, 510498527421, 6665697270, 0] := by
  rw [show D2M8K2.u2395 = KTree.node D2M8K2.u2379 (nat_lit 5619368) (nat_lit 2026075450) (nat_lit 0) D2M8K2.u2394 from rfl, totK_node, atot2379, atot2394]
  decide +kernel

theorem arows2426 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2426 = true := by
  rw [show D2M8K2.u2426 = KTree.node D2M8K2.u2410 (nat_lit 5700038) (nat_lit 3100979891) (nat_lit 0) D2M8K2.u2425 from rfl, allE_node, arows2410, irow2426, arows2425]
  all_goals rfl

theorem atot2426 : totK PD2M8K2 D2M8K2.u2426 = [0, 1694054093225, 8086292775105, 12330687282916, 5967532240916, 629048663817, 11121530615, 0] := by
  rw [show D2M8K2.u2426 = KTree.node D2M8K2.u2410 (nat_lit 5700038) (nat_lit 3100979891) (nat_lit 0) D2M8K2.u2425 from rfl, totK_node, atot2410, atot2425]
  decide +kernel

theorem arows2459 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2459 = true := by
  rw [show D2M8K2.u2459 = KTree.node D2M8K2.u2443 (nat_lit 6523291) (nat_lit 2239021588) (nat_lit 0) D2M8K2.u2458 from rfl, allE_node, arows2443, irow2459, arows2458]
  all_goals rfl

theorem atot2459 : totK PD2M8K2 D2M8K2.u2459 = [2141405656235, 8326105135237, 10271032111395, 5566569310553, 2291297453793, 457909095537, 21751168066, 0] := by
  rw [show D2M8K2.u2459 = KTree.node D2M8K2.u2443 (nat_lit 6523291) (nat_lit 2239021588) (nat_lit 0) D2M8K2.u2458 from rfl, totK_node, atot2443, atot2458]
  decide +kernel

theorem arows2490 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2490 = true := by
  rw [show D2M8K2.u2490 = KTree.node D2M8K2.u2474 (nat_lit 6554190) (nat_lit 3155471156) (nat_lit 0) D2M8K2.u2489 from rfl, allE_node, arows2474, irow2490, arows2489]
  all_goals rfl

theorem atot2490 : totK PD2M8K2 D2M8K2.u2490 = [1954123743270, 8004649222067, 11416842536398, 6523670760177, 1030744370354, 21096254089, 0, 0] := by
  rw [show D2M8K2.u2490 = KTree.node D2M8K2.u2474 (nat_lit 6554190) (nat_lit 3155471156) (nat_lit 0) D2M8K2.u2489 from rfl, totK_node, atot2474, atot2489]
  decide +kernel

theorem arows2522 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2522 = true := by
  rw [show D2M8K2.u2522 = KTree.node D2M8K2.u2506 (nat_lit 6590973) (nat_lit 1019040418) (nat_lit 0) D2M8K2.u2521 from rfl, allE_node, arows2506, irow2522, arows2521]
  all_goals rfl

theorem atot2522 : totK PD2M8K2 D2M8K2.u2522 = [1668108962810, 7964575560887, 12197379957553, 6145498372619, 759828925551, 18797058808, 0, 0] := by
  rw [show D2M8K2.u2522 = KTree.node D2M8K2.u2506 (nat_lit 6590973) (nat_lit 1019040418) (nat_lit 0) D2M8K2.u2521 from rfl, totK_node, atot2506, atot2521]
  decide +kernel

theorem arows2553 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2553 = true := by
  rw [show D2M8K2.u2553 = KTree.node D2M8K2.u2537 (nat_lit 6629131) (nat_lit 1742869688) (nat_lit 0) D2M8K2.u2552 from rfl, allE_node, arows2537, irow2553, arows2552]
  all_goals rfl

theorem atot2553 : totK PD2M8K2 D2M8K2.u2553 = [1580897165155, 7861855037967, 12296766489323, 6233245642094, 773339766553, 19065934916, 0, 0] := by
  rw [show D2M8K2.u2553 = KTree.node D2M8K2.u2537 (nat_lit 6629131) (nat_lit 1742869688) (nat_lit 0) D2M8K2.u2552 from rfl, totK_node, atot2537, atot2552]
  decide +kernel

theorem arows2588 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2588 = true := by
  rw [show D2M8K2.u2588 = KTree.node D2M8K2.u2572 (nat_lit 6664643) (nat_lit 2858493135) (nat_lit 0) D2M8K2.u2587 from rfl, allE_node, arows2572, irow2588, arows2587]
  all_goals rfl

theorem atot2588 : totK PD2M8K2 D2M8K2.u2588 = [1967993956142, 8762766003972, 12286968631248, 5271355975261, 499324919921, 6115358396, 0, 0] := by
  rw [show D2M8K2.u2588 = KTree.node D2M8K2.u2572 (nat_lit 6664643) (nat_lit 2858493135) (nat_lit 0) D2M8K2.u2587 from rfl, totK_node, atot2572, atot2587]
  decide +kernel

theorem arows2619 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2619 = true := by
  rw [show D2M8K2.u2619 = KTree.node D2M8K2.u2603 (nat_lit 6702892) (nat_lit 3816195462) (nat_lit 0) D2M8K2.u2618 from rfl, allE_node, arows2603, irow2619, arows2618]
  all_goals rfl

theorem atot2619 : totK PD2M8K2 D2M8K2.u2619 = [910074444546, 6112650470245, 12246433671531, 8079553116450, 1471193239262, 62267591326, 0, 0] := by
  rw [show D2M8K2.u2619 = KTree.node D2M8K2.u2603 (nat_lit 6702892) (nat_lit 3816195462) (nat_lit 0) D2M8K2.u2618 from rfl, totK_node, atot2603, atot2618]
  decide +kernel

theorem arows2651 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2651 = true := by
  rw [show D2M8K2.u2651 = KTree.node D2M8K2.u2635 (nat_lit 6779554) (nat_lit 4004572508) (nat_lit 0) D2M8K2.u2650 from rfl, allE_node, arows2635, irow2651, arows2650]
  all_goals rfl

theorem atot2651 : totK PD2M8K2 D2M8K2.u2651 = [0, 1691470793519, 7877046957287, 11783451952347, 6328472766887, 1102148126118, 47116249314, 0] := by
  rw [show D2M8K2.u2651 = KTree.node D2M8K2.u2635 (nat_lit 6779554) (nat_lit 4004572508) (nat_lit 0) D2M8K2.u2650 from rfl, totK_node, atot2635, atot2650]
  decide +kernel

theorem arows2682 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2682 = true := by
  rw [show D2M8K2.u2682 = KTree.node D2M8K2.u2666 (nat_lit 6810624) (nat_lit 3697154750) (nat_lit 0) D2M8K2.u2681 from rfl, allE_node, arows2666, irow2682, arows2681]
  all_goals rfl

theorem atot2682 : totK PD2M8K2 D2M8K2.u2682 = [0, 2020960023239, 8778532998811, 11971935819827, 5380096743247, 602160378029, 10531122277, 0] := by
  rw [show D2M8K2.u2682 = KTree.node D2M8K2.u2666 (nat_lit 6810624) (nat_lit 3697154750) (nat_lit 0) D2M8K2.u2681 from rfl, totK_node, atot2666, atot2681]
  decide +kernel

theorem arows2715 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2715 = true := by
  rw [show D2M8K2.u2715 = KTree.node D2M8K2.u2699 (nat_lit 6854579) (nat_lit 1985317167) (nat_lit 0) D2M8K2.u2714 from rfl, allE_node, arows2699, irow2715, arows2714]
  all_goals rfl

theorem atot2715 : totK PD2M8K2 D2M8K2.u2715 = [0, 2021471656860, 9098103050043, 12219057790962, 4947176767936, 467182902054, 6546549506, 0] := by
  rw [show D2M8K2.u2715 = KTree.node D2M8K2.u2699 (nat_lit 6854579) (nat_lit 1985317167) (nat_lit 0) D2M8K2.u2714 from rfl, totK_node, atot2699, atot2714]
  decide +kernel

theorem arows2746 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2746 = true := by
  rw [show D2M8K2.u2746 = KTree.node D2M8K2.u2730 (nat_lit 6891682) (nat_lit 4061391534) (nat_lit 0) D2M8K2.u2745 from rfl, allE_node, arows2730, irow2746, arows2745]
  all_goals rfl

theorem atot2746 : totK PD2M8K2 D2M8K2.u2746 = [0, 2015422827078, 8899101196638, 12138442341686, 5072661725586, 479285986832, 6624648996, 0] := by
  rw [show D2M8K2.u2746 = KTree.node D2M8K2.u2730 (nat_lit 6891682) (nat_lit 4061391534) (nat_lit 0) D2M8K2.u2745 from rfl, totK_node, atot2730, atot2745]
  decide +kernel

theorem arows2778 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2778 = true := by
  rw [show D2M8K2.u2778 = KTree.node D2M8K2.u2762 (nat_lit 6933209) (nat_lit 1700818347) (nat_lit 0) D2M8K2.u2777 from rfl, allE_node, arows2762, irow2778, arows2777]
  all_goals rfl

theorem atot2778 : totK PD2M8K2 D2M8K2.u2778 = [0, 2027159637397, 9284647712752, 12513111954419, 4726731330349, 343050067147, 1429815836, 0] := by
  rw [show D2M8K2.u2778 = KTree.node D2M8K2.u2762 (nat_lit 6933209) (nat_lit 1700818347) (nat_lit 0) D2M8K2.u2777 from rfl, totK_node, atot2762, atot2777]
  decide +kernel

theorem arows2809 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2809 = true := by
  rw [show D2M8K2.u2809 = KTree.node D2M8K2.u2793 (nat_lit 6975701) (nat_lit 2387124146) (nat_lit 0) D2M8K2.u2808 from rfl, allE_node, arows2793, irow2809, arows2808]
  all_goals rfl

theorem atot2809 : totK PD2M8K2 D2M8K2.u2809 = [1647549989118, 6687587641844, 9130218409036, 6742212825550, 3786904017054, 571797007817, 12189850367, 0] := by
  rw [show D2M8K2.u2809 = KTree.node D2M8K2.u2793 (nat_lit 6975701) (nat_lit 2387124146) (nat_lit 0) D2M8K2.u2808 from rfl, totK_node, atot2793, atot2808]
  decide +kernel

theorem arows2843 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2843 = true := by
  rw [show D2M8K2.u2843 = KTree.node D2M8K2.u2827 (nat_lit 7021885) (nat_lit 1038942003) (nat_lit 0) D2M8K2.u2842 from rfl, allE_node, arows2827, irow2843, arows2842]
  all_goals rfl

theorem atot2843 : totK PD2M8K2 D2M8K2.u2843 = [2048132857640, 8971576760524, 12079825401172, 5188130424752, 764586016250, 36921873854, 0, 0] := by
  rw [show D2M8K2.u2843 = KTree.node D2M8K2.u2827 (nat_lit 7021885) (nat_lit 1038942003) (nat_lit 0) D2M8K2.u2842 from rfl, totK_node, atot2827, atot2842]
  decide +kernel

theorem arows2874 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2874 = true := by
  rw [show D2M8K2.u2874 = KTree.node D2M8K2.u2858 (nat_lit 7053223) (nat_lit 2322719644) (nat_lit 0) D2M8K2.u2873 from rfl, allE_node, arows2858, irow2874, arows2873]
  all_goals rfl

theorem atot2874 : totK PD2M8K2 D2M8K2.u2874 = [2107128710287, 8343571199237, 11236461665044, 6217929198431, 1013882592998, 21096254089, 0, 0] := by
  rw [show D2M8K2.u2874 = KTree.node D2M8K2.u2858 (nat_lit 7053223) (nat_lit 2322719644) (nat_lit 0) D2M8K2.u2873 from rfl, totK_node, atot2858, atot2873]
  decide +kernel

theorem arows2906 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2906 = true := by
  rw [show D2M8K2.u2906 = KTree.node D2M8K2.u2890 (nat_lit 7088744) (nat_lit 3378605159) (nat_lit 0) D2M8K2.u2905 from rfl, allE_node, arows2890, irow2906, arows2905]
  all_goals rfl

theorem atot2906 : totK PD2M8K2 D2M8K2.u2906 = [1547471583796, 7703516019188, 12272636811401, 6310822609078, 769770583913, 18797058808, 0, 0] := by
  rw [show D2M8K2.u2906 = KTree.node D2M8K2.u2890 (nat_lit 7088744) (nat_lit 3378605159) (nat_lit 0) D2M8K2.u2905 from rfl, totK_node, atot2890, atot2905]
  decide +kernel

theorem arows2937 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2937 = true := by
  rw [show D2M8K2.u2937 = KTree.node D2M8K2.u2921 (nat_lit 7168594) (nat_lit 3268230195) (nat_lit 0) D2M8K2.u2936 from rfl, allE_node, arows2921, irow2937, arows2936]
  all_goals rfl

theorem atot2937 : totK PD2M8K2 D2M8K2.u2937 = [1901531782302, 8690986508746, 12370078133238, 5306620482446, 501842003275, 6115358396, 0, 0] := by
  rw [show D2M8K2.u2937 = KTree.node D2M8K2.u2921 (nat_lit 7168594) (nat_lit 3268230195) (nat_lit 0) D2M8K2.u2936 from rfl, totK_node, atot2921, atot2936]
  decide +kernel

theorem arows2970 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u2970 = true := by
  rw [show D2M8K2.u2970 = KTree.node D2M8K2.u2954 (nat_lit 7205817) (nat_lit 951927534) (nat_lit 0) D2M8K2.u2969 from rfl, allE_node, arows2954, irow2970, arows2969]
  all_goals rfl

theorem atot2970 : totK PD2M8K2 D2M8K2.u2970 = [529390851355, 5130411889883, 12388504352766, 9126514953403, 1536924236562, 47291576347, 0, 0] := by
  rw [show D2M8K2.u2970 = KTree.node D2M8K2.u2954 (nat_lit 7205817) (nat_lit 951927534) (nat_lit 0) D2M8K2.u2969 from rfl, totK_node, atot2954, atot2969]
  decide +kernel

theorem arows3001 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3001 = true := by
  rw [show D2M8K2.u3001 = KTree.node D2M8K2.u2985 (nat_lit 7255039) (nat_lit 2257254018) (nat_lit 0) D2M8K2.u3000 from rfl, allE_node, arows2985, irow3001, arows3000]
  all_goals rfl

theorem atot3001 : totK PD2M8K2 D2M8K2.u3001 = [0, 2274329284698, 9847920232799, 12393664853732, 3967105006726, 246065300780, 1275377855, 0] := by
  rw [show D2M8K2.u3001 = KTree.node D2M8K2.u2985 (nat_lit 7255039) (nat_lit 2257254018) (nat_lit 0) D2M8K2.u3000 from rfl, totK_node, atot2985, atot3000]
  decide +kernel

theorem arows3033 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3033 = true := by
  rw [show D2M8K2.u3033 = KTree.node D2M8K2.u3017 (nat_lit 7308344) (nat_lit 3744046299) (nat_lit 0) D2M8K2.u3032 from rfl, allE_node, arows3017, irow3033, arows3032]
  all_goals rfl

theorem atot3033 : totK PD2M8K2 D2M8K2.u3033 = [0, 2521089814787, 10145322291476, 11955022931719, 3808557376847, 252291317990, 1206465782, 0] := by
  rw [show D2M8K2.u3033 = KTree.node D2M8K2.u3017 (nat_lit 7308344) (nat_lit 3744046299) (nat_lit 0) D2M8K2.u3032 from rfl, totK_node, atot3017, atot3032]
  decide +kernel

theorem arows3064 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3064 = true := by
  rw [show D2M8K2.u3064 = KTree.node D2M8K2.u3048 (nat_lit 7388985) (nat_lit 1826606345) (nat_lit 0) D2M8K2.u3063 from rfl, allE_node, arows3048, irow3064, arows3063]
  all_goals rfl

theorem atot3064 : totK PD2M8K2 D2M8K2.u3064 = [0, 1981093361941, 8809151732376, 11937382560066, 5046660830601, 621564877443, 18694047957, 0] := by
  rw [show D2M8K2.u3064 = KTree.node D2M8K2.u3048 (nat_lit 7388985) (nat_lit 1826606345) (nat_lit 0) D2M8K2.u3063 from rfl, totK_node, atot3048, atot3063]
  decide +kernel

theorem arows3100 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3100 = true := by
  rw [show D2M8K2.u3100 = KTree.node D2M8K2.u3084 (nat_lit 7430934) (nat_lit 2923239546) (nat_lit 0) D2M8K2.u3099 from rfl, allE_node, arows3084, irow3100, arows3099]
  all_goals rfl

theorem atot3100 : totK PD2M8K2 D2M8K2.u3100 = [709127292956, 4167320044471, 9848150447269, 10295897114782, 3419737830163, 276499433692, 4779662215, 0] := by
  rw [show D2M8K2.u3100 = KTree.node D2M8K2.u3084 (nat_lit 7430934) (nat_lit 2923239546) (nat_lit 0) D2M8K2.u3099 from rfl, totK_node, atot3084, atot3099]
  decide +kernel

theorem arows3131 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3131 = true := by
  rw [show D2M8K2.u3131 = KTree.node D2M8K2.u3115 (nat_lit 7497366) (nat_lit 3581696511) (nat_lit 0) D2M8K2.u3130 from rfl, allE_node, arows3115, irow3131, arows3130]
  all_goals rfl

theorem atot3131 : totK PD2M8K2 D2M8K2.u3131 = [2157627817053, 9342326048333, 12344183887867, 4634877724593, 335104373944, 1369150432, 0, 0] := by
  rw [show D2M8K2.u3131 = KTree.node D2M8K2.u3115 (nat_lit 7497366) (nat_lit 3581696511) (nat_lit 0) D2M8K2.u3130 from rfl, totK_node, atot3115, atot3130]
  decide +kernel

theorem arows3163 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3163 = true := by
  rw [show D2M8K2.u3163 = KTree.node D2M8K2.u3147 (nat_lit 7535641) (nat_lit 1444519198) (nat_lit 0) D2M8K2.u3162 from rfl, allE_node, arows3147, irow3163, arows3162]
  all_goals rfl

theorem atot3163 : totK PD2M8K2 D2M8K2.u3163 = [1226959281175, 6472357568996, 11608643645873, 7981345340236, 1609145369964, 58018127943, 0, 0] := by
  rw [show D2M8K2.u3163 = KTree.node D2M8K2.u3147 (nat_lit 7535641) (nat_lit 1444519198) (nat_lit 0) D2M8K2.u3162 from rfl, totK_node, atot3147, atot3162]
  decide +kernel

theorem arows3194 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3194 = true := by
  rw [show D2M8K2.u3194 = KTree.node D2M8K2.u3178 (nat_lit 7608332) (nat_lit 1442715125) (nat_lit 0) D2M8K2.u3193 from rfl, allE_node, arows3178, irow3194, arows3193]
  all_goals rfl

theorem atot3194 : totK PD2M8K2 D2M8K2.u3194 = [1709996110766, 8085645122556, 12161015966625, 6002174981898, 748639788807, 19065934916, 0, 0] := by
  rw [show D2M8K2.u3194 = KTree.node D2M8K2.u3178 (nat_lit 7608332) (nat_lit 1442715125) (nat_lit 0) D2M8K2.u3193 from rfl, totK_node, atot3178, atot3193]
  decide +kernel

theorem arows3227 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3227 = true := by
  rw [show D2M8K2.u3227 = KTree.node D2M8K2.u3211 (nat_lit 7643053) (nat_lit 1121355226) (nat_lit 0) D2M8K2.u3226 from rfl, allE_node, arows3211, irow3227, arows3226]
  all_goals rfl

theorem atot3227 : totK PD2M8K2 D2M8K2.u3227 = [1983388085741, 9112372786694, 12542142852768, 4826662485111, 333785464888, 1138244013, 0, 0] := by
  rw [show D2M8K2.u3227 = KTree.node D2M8K2.u3211 (nat_lit 7643053) (nat_lit 1121355226) (nat_lit 0) D2M8K2.u3226 from rfl, totK_node, atot3211, atot3226]
  decide +kernel

theorem arows3258 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3258 = true := by
  rw [show D2M8K2.u3258 = KTree.node D2M8K2.u3242 (nat_lit 7683949) (nat_lit 1116440054) (nat_lit 0) D2M8K2.u3257 from rfl, allE_node, arows3242, irow3258, arows3257]
  all_goals rfl

theorem atot3258 : totK PD2M8K2 D2M8K2.u3258 = [1995420176502, 8571051398219, 11923148395871, 5734351322218, 676855048315, 11167240352, 0, 0] := by
  rw [show D2M8K2.u3258 = KTree.node D2M8K2.u3242 (nat_lit 7683949) (nat_lit 1116440054) (nat_lit 0) D2M8K2.u3257 from rfl, totK_node, atot3242, atot3257]
  decide +kernel

theorem arows3290 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3290 = true := by
  rw [show D2M8K2.u3290 = KTree.node D2M8K2.u3274 (nat_lit 7727620) (nat_lit 3761844311) (nat_lit 0) D2M8K2.u3289 from rfl, allE_node, arows3274, irow3290, arows3289]
  all_goals rfl

theorem atot3290 : totK PD2M8K2 D2M8K2.u3290 = [0, 2432639888433, 10108657691961, 12007854175801, 3657122560627, 223186435884, 1310517177, 0] := by
  rw [show D2M8K2.u3290 = KTree.node D2M8K2.u3274 (nat_lit 7727620) (nat_lit 3761844311) (nat_lit 0) D2M8K2.u3289 from rfl, totK_node, atot3274, atot3289]
  decide +kernel

theorem arows3321 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3321 = true := by
  rw [show D2M8K2.u3321 = KTree.node D2M8K2.u3305 (nat_lit 7770895) (nat_lit 2409047563) (nat_lit 0) D2M8K2.u3320 from rfl, allE_node, arows3305, irow3321, arows3320]
  all_goals rfl

theorem atot3321 : totK PD2M8K2 D2M8K2.u3321 = [0, 3315038778628, 11557163504761, 11244335038773, 2806414159900, 122091185045, 0, 0] := by
  rw [show D2M8K2.u3321 = KTree.node D2M8K2.u3305 (nat_lit 7770895) (nat_lit 2409047563) (nat_lit 0) D2M8K2.u3320 from rfl, totK_node, atot3305, atot3320]
  decide +kernel

theorem arows3355 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3355 = true := by
  rw [show D2M8K2.u3355 = KTree.node D2M8K2.u3339 (nat_lit 7869439) (nat_lit 2334025651) (nat_lit 0) D2M8K2.u3354 from rfl, allE_node, arows3339, irow3355, arows3354]
  all_goals rfl

theorem atot3355 : totK PD2M8K2 D2M8K2.u3355 = [0, 1632389674198, 8139650192829, 12245859932395, 5643061136840, 708245429150, 18953862985, 0] := by
  rw [show D2M8K2.u3355 = KTree.node D2M8K2.u3339 (nat_lit 7869439) (nat_lit 2334025651) (nat_lit 0) D2M8K2.u3354 from rfl, totK_node, atot3339, atot3354]
  decide +kernel

theorem arows3386 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3386 = true := by
  rw [show D2M8K2.u3386 = KTree.node D2M8K2.u3370 (nat_lit 7904427) (nat_lit 3663330265) (nat_lit 0) D2M8K2.u3385 from rfl, allE_node, arows3370, irow3386, arows3385]
  all_goals rfl

theorem atot3386 : totK PD2M8K2 D2M8K2.u3386 = [0, 1985889300072, 9153393616348, 12366869368558, 4603594135099, 374898617906, 6052528252, 0] := by
  rw [show D2M8K2.u3386 = KTree.node D2M8K2.u3370 (nat_lit 7904427) (nat_lit 3663330265) (nat_lit 0) D2M8K2.u3385 from rfl, totK_node, atot3370, atot3385]
  decide +kernel

theorem arows3418 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3418 = true := by
  rw [show D2M8K2.u3418 = KTree.node D2M8K2.u3402 (nat_lit 7965590) (nat_lit 3069290062) (nat_lit 0) D2M8K2.u3417 from rfl, allE_node, arows3402, irow3418, arows3417]
  all_goals rfl

theorem atot3418 : totK PD2M8K2 D2M8K2.u3418 = [1644326566028, 7490467613352, 11334812901692, 6796165441866, 1375293712611, 49785955117, 0, 0] := by
  rw [show D2M8K2.u3418 = KTree.node D2M8K2.u3402 (nat_lit 7965590) (nat_lit 3069290062) (nat_lit 0) D2M8K2.u3417 from rfl, totK_node, atot3402, atot3417]
  decide +kernel

theorem arows3449 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3449 = true := by
  rw [show D2M8K2.u3449 = KTree.node D2M8K2.u3433 (nat_lit 8014940) (nat_lit 3572411049) (nat_lit 0) D2M8K2.u3448 from rfl, allE_node, arows3433, irow3449, arows3448]
  all_goals rfl

theorem atot3449 : totK PD2M8K2 D2M8K2.u3449 = [2045971677713, 8970502162759, 12097659263835, 5118597529966, 743840608128, 36921873854, 0, 0] := by
  rw [show D2M8K2.u3449 = KTree.node D2M8K2.u3433 (nat_lit 8014940) (nat_lit 3572411049) (nat_lit 0) D2M8K2.u3448 from rfl, totK_node, atot3433, atot3448]
  decide +kernel

theorem arows3482 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3482 = true := by
  rw [show D2M8K2.u3482 = KTree.node D2M8K2.u3466 (nat_lit 8046740) (nat_lit 3290940105) (nat_lit 0) D2M8K2.u3481 from rfl, allE_node, arows3466, irow3482, arows3481]
  all_goals rfl

theorem atot3482 : totK PD2M8K2 D2M8K2.u3482 = [1879699002326, 7919474988311, 11502179520302, 6621578232319, 1049311360467, 21096254089, 0, 0] := by
  rw [show D2M8K2.u3482 = KTree.node D2M8K2.u3466 (nat_lit 8046740) (nat_lit 3290940105) (nat_lit 0) D2M8K2.u3481 from rfl, totK_node, atot3466, atot3481]
  decide +kernel

theorem arows3513 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3513 = true := by
  rw [show D2M8K2.u3513 = KTree.node D2M8K2.u3497 (nat_lit 8083729) (nat_lit 1557368512) (nat_lit 0) D2M8K2.u3512 from rfl, allE_node, arows3497, irow3513, arows3512]
  all_goals rfl

theorem atot3513 : totK PD2M8K2 D2M8K2.u3513 = [1741511974733, 8001429059832, 12051460899666, 6120302153514, 762325763274, 18797058808, 0, 0] := by
  rw [show D2M8K2.u3513 = KTree.node D2M8K2.u3497 (nat_lit 8083729) (nat_lit 1557368512) (nat_lit 0) D2M8K2.u3512 from rfl, totK_node, atot3497, atot3512]
  decide +kernel

theorem arows3545 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3545 = true := by
  rw [show D2M8K2.u3545 = KTree.node D2M8K2.u3529 (nat_lit 8122181) (nat_lit 2312801838) (nat_lit 0) D2M8K2.u3544 from rfl, allE_node, arows3529, irow3545, arows3544]
  all_goals rfl

theorem atot3545 : totK PD2M8K2 D2M8K2.u3545 = [1589615932036, 7895662702180, 12204460911908, 6211776460594, 778251465500, 19065934916, 0, 0] := by
  rw [show D2M8K2.u3545 = KTree.node D2M8K2.u3529 (nat_lit 8122181) (nat_lit 2312801838) (nat_lit 0) D2M8K2.u3544 from rfl, totK_node, atot3529, atot3544]
  decide +kernel

theorem arows3576 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3576 = true := by
  rw [show D2M8K2.u3576 = KTree.node D2M8K2.u3560 (nat_lit 8156833) (nat_lit 1473479148) (nat_lit 0) D2M8K2.u3575 from rfl, allE_node, arows3560, irow3576, arows3575]
  all_goals rfl

theorem atot3576 : totK PD2M8K2 D2M8K2.u3576 = [862019888459, 6381593494073, 12885817764834, 7493819701403, 946608789941, 20467958624, 0, 0] := by
  rw [show D2M8K2.u3576 = KTree.node D2M8K2.u3560 (nat_lit 8156833) (nat_lit 1473479148) (nat_lit 0) D2M8K2.u3575 from rfl, totK_node, atot3560, atot3575]
  decide +kernel

theorem arows3611 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3611 = true := by
  rw [show D2M8K2.u3611 = KTree.node D2M8K2.u3595 (nat_lit 8247422) (nat_lit 2959892638) (nat_lit 0) D2M8K2.u3610 from rfl, allE_node, arows3595, irow3611, arows3610]
  all_goals rfl

theorem atot3611 : totK PD2M8K2 D2M8K2.u3611 = [0, 2309020053629, 10012106147027, 12306078773513, 3794551312988, 239589226748, 1209030869, 0] := by
  rw [show D2M8K2.u3611 = KTree.node D2M8K2.u3595 (nat_lit 8247422) (nat_lit 2959892638) (nat_lit 0) D2M8K2.u3610 from rfl, totK_node, atot3595, atot3610]
  decide +kernel

theorem arows3642 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3642 = true := by
  rw [show D2M8K2.u3642 = KTree.node D2M8K2.u3626 (nat_lit 8308334) (nat_lit 3083860465) (nat_lit 0) D2M8K2.u3641 from rfl, allE_node, arows3626, irow3642, arows3641]
  all_goals rfl

theorem atot3642 : totK PD2M8K2 D2M8K2.u3642 = [0, 3431007675637, 11947021389836, 11242918098107, 2331725935184, 69223402122, 0, 0] := by
  rw [show D2M8K2.u3642 = KTree.node D2M8K2.u3626 (nat_lit 8308334) (nat_lit 3083860465) (nat_lit 0) D2M8K2.u3641 from rfl, totK_node, atot3626, atot3641]
  decide +kernel

theorem arows3674 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3674 = true := by
  rw [show D2M8K2.u3674 = KTree.node D2M8K2.u3658 (nat_lit 8382991) (nat_lit 2214005087) (nat_lit 0) D2M8K2.u3673 from rfl, allE_node, arows3658, irow3674, arows3673]
  all_goals rfl

theorem atot3674 : totK PD2M8K2 D2M8K2.u3674 = [0, 2982833836256, 11311488482280, 11646218153996, 2623610550308, 101073984920, 0, 0] := by
  rw [show D2M8K2.u3674 = KTree.node D2M8K2.u3658 (nat_lit 8382991) (nat_lit 2214005087) (nat_lit 0) D2M8K2.u3673 from rfl, totK_node, atot3658, atot3673]
  decide +kernel

theorem arows3705 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3705 = true := by
  rw [show D2M8K2.u3705 = KTree.node D2M8K2.u3689 (nat_lit 8467810) (nat_lit 3920247055) (nat_lit 0) D2M8K2.u3704 from rfl, allE_node, arows3689, irow3705, arows3704]
  all_goals rfl

theorem atot3705 : totK PD2M8K2 D2M8K2.u3705 = [1651197789013, 6444629069337, 9227623196472, 7477483495901, 3235561498032, 387011684119, 6115358396, 0] := by
  rw [show D2M8K2.u3705 = KTree.node D2M8K2.u3689 (nat_lit 8467810) (nat_lit 3920247055) (nat_lit 0) D2M8K2.u3704 from rfl, totK_node, atot3689, atot3704]
  decide +kernel

theorem arows3738 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3738 = true := by
  rw [show D2M8K2.u3738 = KTree.node D2M8K2.u3722 (nat_lit 8513221) (nat_lit 1198217687) (nat_lit 0) D2M8K2.u3737 from rfl, allE_node, arows3722, irow3738, arows3737]
  all_goals rfl

theorem atot3738 : totK PD2M8K2 D2M8K2.u3738 = [2050565017840, 8980108850997, 12089709435208, 5188740962421, 763263642038, 36921873854, 0, 0] := by
  rw [show D2M8K2.u3738 = KTree.node D2M8K2.u3722 (nat_lit 8513221) (nat_lit 1198217687) (nat_lit 0) D2M8K2.u3737 from rfl, totK_node, atot3722, atot3737]
  decide +kernel

theorem arows3769 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3769 = true := by
  rw [show D2M8K2.u3769 = KTree.node D2M8K2.u3753 (nat_lit 8544881) (nat_lit 1582362190) (nat_lit 0) D2M8K2.u3768 from rfl, allE_node, arows3753, irow3769, arows3768]
  all_goals rfl

theorem atot3769 : totK PD2M8K2 D2M8K2.u3769 = [1991252054055, 8178736593392, 11425261180273, 6379183536983, 1028006424528, 21096254089, 0, 0] := by
  rw [show D2M8K2.u3769 = KTree.node D2M8K2.u3753 (nat_lit 8544881) (nat_lit 1582362190) (nat_lit 0) D2M8K2.u3768 from rfl, totK_node, atot3753, atot3768]
  decide +kernel

theorem arows3801 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3801 = true := by
  rw [show D2M8K2.u3801 = KTree.node D2M8K2.u3785 (nat_lit 8582140) (nat_lit 3245423871) (nat_lit 0) D2M8K2.u3800 from rfl, allE_node, arows3785, irow3801, arows3800]
  all_goals rfl

theorem atot3801 : totK PD2M8K2 D2M8K2.u3801 = [1565372783170, 7885651316068, 12386394655128, 6179255589639, 756262951757, 18797058808, 0, 0] := by
  rw [show D2M8K2.u3801 = KTree.node D2M8K2.u3785 (nat_lit 8582140) (nat_lit 3245423871) (nat_lit 0) D2M8K2.u3800 from rfl, totK_node, atot3785, atot3800]
  decide +kernel

theorem arows3832 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3832 = true := by
  rw [show D2M8K2.u3832 = KTree.node D2M8K2.u3816 (nat_lit 8620520) (nat_lit 3950786586) (nat_lit 0) D2M8K2.u3831 from rfl, allE_node, arows3816, irow3832, arows3831]
  all_goals rfl

theorem atot3832 : totK PD2M8K2 D2M8K2.u3832 = [1671867613851, 7901745637785, 12145679014306, 6230691440854, 778058144557, 19065934916, 0, 0] := by
  rw [show D2M8K2.u3832 = KTree.node D2M8K2.u3816 (nat_lit 8620520) (nat_lit 3950786586) (nat_lit 0) D2M8K2.u3831 from rfl, totK_node, atot3816, atot3831]
  decide +kernel

theorem arows3866 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3866 = true := by
  rw [show D2M8K2.u3866 = KTree.node D2M8K2.u3850 (nat_lit 8696004) (nat_lit 3233391780) (nat_lit 0) D2M8K2.u3865 from rfl, allE_node, arows3850, irow3866, arows3865]
  all_goals rfl

theorem atot3866 : totK PD2M8K2 D2M8K2.u3866 = [867070346516, 5921450738823, 12360241584385, 8287092326587, 1261012124289, 34241849113, 0, 0] := by
  rw [show D2M8K2.u3866 = KTree.node D2M8K2.u3850 (nat_lit 8696004) (nat_lit 3233391780) (nat_lit 0) D2M8K2.u3865 from rfl, totK_node, atot3850, atot3865]
  decide +kernel

theorem arows3897 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3897 = true := by
  rw [show D2M8K2.u3897 = KTree.node D2M8K2.u3881 (nat_lit 8738281) (nat_lit 1452820356) (nat_lit 0) D2M8K2.u3896 from rfl, allE_node, arows3881, irow3897, arows3896]
  all_goals rfl

theorem atot3897 : totK PD2M8K2 D2M8K2.u3897 = [0, 2251270678048, 9555353541956, 12312321673017, 4302910829799, 267910471638, 1369150432, 0] := by
  rw [show D2M8K2.u3897 = KTree.node D2M8K2.u3881 (nat_lit 8738281) (nat_lit 1452820356) (nat_lit 0) D2M8K2.u3896 from rfl, totK_node, atot3881, atot3896]
  decide +kernel

theorem arows3929 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3929 = true := by
  rw [show D2M8K2.u3929 = KTree.node D2M8K2.u3913 (nat_lit 8798216) (nat_lit 3798084972) (nat_lit 0) D2M8K2.u3928 from rfl, allE_node, arows3913, irow3929, arows3928]
  all_goals rfl

theorem atot3929 : totK PD2M8K2 D2M8K2.u3929 = [0, 2764644539807, 10587967664109, 11745295941741, 3506504451723, 196132615651, 1166720416, 0] := by
  rw [show D2M8K2.u3929 = KTree.node D2M8K2.u3913 (nat_lit 8798216) (nat_lit 3798084972) (nat_lit 0) D2M8K2.u3928 from rfl, totK_node, atot3913, atot3928]
  decide +kernel

theorem arows3960 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3960 = true := by
  rw [show D2M8K2.u3960 = KTree.node D2M8K2.u3944 (nat_lit 8839666) (nat_lit 3942439521) (nat_lit 0) D2M8K2.u3959 from rfl, allE_node, arows3944, irow3960, arows3959]
  all_goals rfl

theorem atot3960 : totK PD2M8K2 D2M8K2.u3960 = [0, 1990777437037, 9018173266856, 12315082033107, 4877003340479, 418982232646, 6335121832, 0] := by
  rw [show D2M8K2.u3960 = KTree.node D2M8K2.u3944 (nat_lit 8839666) (nat_lit 3942439521) (nat_lit 0) D2M8K2.u3959 from rfl, totK_node, atot3944, atot3959]
  decide +kernel

theorem arows3993 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u3993 = true := by
  rw [show D2M8K2.u3993 = KTree.node D2M8K2.u3977 (nat_lit 8922416) (nat_lit 3550305444) (nat_lit 0) D2M8K2.u3992 from rfl, allE_node, arows3977, irow3993, arows3992]
  all_goals rfl

theorem atot3993 : totK PD2M8K2 D2M8K2.u3993 = [0, 2111405075947, 9468197398999, 12318110091294, 4412501962367, 348884610171, 5163565574, 0] := by
  rw [show D2M8K2.u3993 = KTree.node D2M8K2.u3977 (nat_lit 8922416) (nat_lit 3550305444) (nat_lit 0) D2M8K2.u3992 from rfl, totK_node, atot3977, atot3992]
  decide +kernel

theorem arows4024 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4024 = true := by
  rw [show D2M8K2.u4024 = KTree.node D2M8K2.u4008 (nat_lit 9501103) (nat_lit 2213124872) (nat_lit 0) D2M8K2.u4023 from rfl, allE_node, arows4008, irow4024, arows4023]
  all_goals rfl

theorem atot4024 : totK PD2M8K2 D2M8K2.u4024 = [0, 1716029857085, 7721421233459, 11747449587129, 6483798885276, 997056891968, 32664957003, 0] := by
  rw [show D2M8K2.u4024 = KTree.node D2M8K2.u4008 (nat_lit 9501103) (nat_lit 2213124872) (nat_lit 0) D2M8K2.u4023 from rfl, totK_node, atot4008, atot4023]
  decide +kernel

theorem arows4056 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4056 = true := by
  rw [show D2M8K2.u4056 = KTree.node D2M8K2.u4040 (nat_lit 9530018) (nat_lit 2762252210) (nat_lit 0) D2M8K2.u4055 from rfl, allE_node, arows4040, irow4056, arows4055]
  all_goals rfl

theorem atot4056 : totK PD2M8K2 D2M8K2.u4056 = [0, 1179241111938, 6329424996618, 11666015800600, 8194602257050, 1609077339081, 58018127943, 0] := by
  rw [show D2M8K2.u4056 = KTree.node D2M8K2.u4040 (nat_lit 9530018) (nat_lit 2762252210) (nat_lit 0) D2M8K2.u4055 from rfl, totK_node, atot4040, atot4055]
  decide +kernel

theorem arows4087 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4087 = true := by
  rw [show D2M8K2.u4087 = KTree.node D2M8K2.u4071 (nat_lit 9563171) (nat_lit 2962688467) (nat_lit 0) D2M8K2.u4086 from rfl, allE_node, arows4071, irow4087, arows4086]
  all_goals rfl

theorem atot4087 : totK PD2M8K2 D2M8K2.u4087 = [0, 1831154712347, 8312082955792, 12217912416272, 5814524305377, 646437694804, 11412527294, 0] := by
  rw [show D2M8K2.u4087 = KTree.node D2M8K2.u4071 (nat_lit 9563171) (nat_lit 2962688467) (nat_lit 0) D2M8K2.u4086 from rfl, totK_node, atot4071, atot4086]
  decide +kernel

theorem arows4125 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4125 = true := by
  rw [show D2M8K2.u4125 = KTree.node D2M8K2.u4109 (nat_lit 9600778) (nat_lit 3956385772) (nat_lit 0) D2M8K2.u4124 from rfl, allE_node, arows4109, irow4125, arows4124]
  all_goals rfl

theorem atot4125 : totK PD2M8K2 D2M8K2.u4125 = [0, 1648225056355, 7959497425167, 12317673289518, 6221005774788, 693504093971, 11552853615, 0] := by
  rw [show D2M8K2.u4125 = KTree.node D2M8K2.u4109 (nat_lit 9600778) (nat_lit 3956385772) (nat_lit 0) D2M8K2.u4124 from rfl, totK_node, atot4109, atot4124]
  decide +kernel

theorem arows4156 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4156 = true := by
  rw [show D2M8K2.u4156 = KTree.node D2M8K2.u4140 (nat_lit 9636144) (nat_lit 3371895068) (nat_lit 0) D2M8K2.u4155 from rfl, allE_node, arows4140, irow4156, arows4155]
  all_goals rfl

theorem atot4156 : totK PD2M8K2 D2M8K2.u4156 = [0, 1849380138681, 8762718184992, 12560833275181, 5216189632559, 441084796827, 2586295899, 0] := by
  rw [show D2M8K2.u4156 = KTree.node D2M8K2.u4140 (nat_lit 9636144) (nat_lit 3371895068) (nat_lit 0) D2M8K2.u4155 from rfl, totK_node, atot4140, atot4155]
  decide +kernel

theorem arows4188 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4188 = true := by
  rw [show D2M8K2.u4188 = KTree.node D2M8K2.u4172 (nat_lit 9680591) (nat_lit 2154287778) (nat_lit 0) D2M8K2.u4187 from rfl, allE_node, arows4172, irow4188, arows4187]
  all_goals rfl

theorem atot4188 : totK PD2M8K2 D2M8K2.u4188 = [0, 1995489986565, 8767524433455, 12193362094541, 5574532813815, 514735091239, 2516941024, 0] := by
  rw [show D2M8K2.u4188 = KTree.node D2M8K2.u4172 (nat_lit 9680591) (nat_lit 2154287778) (nat_lit 0) D2M8K2.u4187 from rfl, totK_node, atot4172, atot4187]
  decide +kernel

theorem arows4219 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4219 = true := by
  rw [show D2M8K2.u4219 = KTree.node D2M8K2.u4203 (nat_lit 9757867) (nat_lit 1614994545) (nat_lit 0) D2M8K2.u4218 from rfl, allE_node, arows4203, irow4219, arows4218]
  all_goals rfl

theorem atot4219 : totK PD2M8K2 D2M8K2.u4219 = [0, 0, 2582177718061, 9969382928825, 11391774162778, 4275034072209, 690986213256, 36921873854] := by
  rw [show D2M8K2.u4219 = KTree.node D2M8K2.u4203 (nat_lit 9757867) (nat_lit 1614994545) (nat_lit 0) D2M8K2.u4218 from rfl, totK_node, atot4203, atot4218]
  decide +kernel

theorem arows4252 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4252 = true := by
  rw [show D2M8K2.u4252 = KTree.node D2M8K2.u4236 (nat_lit 9789747) (nat_lit 3426851771) (nat_lit 0) D2M8K2.u4251 from rfl, allE_node, arows4236, irow4252, arows4251]
  all_goals rfl

theorem atot4252 : totK PD2M8K2 D2M8K2.u4252 = [0, 0, 2017238339266, 8213311619930, 11363392378079, 6215636208600, 925070096710, 20725497737] := by
  rw [show D2M8K2.u4252 = KTree.node D2M8K2.u4236 (nat_lit 9789747) (nat_lit 3426851771) (nat_lit 0) D2M8K2.u4251 from rfl, totK_node, atot4236, atot4251]
  decide +kernel

theorem arows4283 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4283 = true := by
  rw [show D2M8K2.u4283 = KTree.node D2M8K2.u4267 (nat_lit 9831456) (nat_lit 3719854113) (nat_lit 0) D2M8K2.u4282 from rfl, allE_node, arows4267, irow4283, arows4282]
  all_goals rfl

theorem atot4283 : totK PD2M8K2 D2M8K2.u4283 = [0, 0, 2017748215095, 9041364047930, 12290037675506, 4998432065621, 443921243342, 6546549506] := by
  rw [show D2M8K2.u4283 = KTree.node D2M8K2.u4267 (nat_lit 9831456) (nat_lit 3719854113) (nat_lit 0) D2M8K2.u4282 from rfl, totK_node, atot4267, atot4282]
  decide +kernel

theorem arows4315 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4315 = true := by
  rw [show D2M8K2.u4315 = KTree.node D2M8K2.u4299 (nat_lit 9872163) (nat_lit 2353823837) (nat_lit 0) D2M8K2.u4314 from rfl, allE_node, arows4299, irow4315, arows4314]
  all_goals rfl

theorem atot4315 : totK PD2M8K2 D2M8K2.u4315 = [0, 0, 2011642525759, 8988823902796, 12162788350829, 5093078321122, 460228697279, 6624648996] := by
  rw [show D2M8K2.u4315 = KTree.node D2M8K2.u4299 (nat_lit 9872163) (nat_lit 2353823837) (nat_lit 0) D2M8K2.u4314 from rfl, totK_node, atot4299, atot4314]
  decide +kernel

theorem arows4346 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4346 = true := by
  rw [show D2M8K2.u4346 = KTree.node D2M8K2.u4330 (nat_lit 9915800) (nat_lit 3848898806) (nat_lit 0) D2M8K2.u4345 from rfl, allE_node, arows4330, irow4346, arows4345]
  all_goals rfl

theorem atot4346 : totK PD2M8K2 D2M8K2.u4346 = [0, 0, 2023494260957, 9392575161994, 12728571017314, 4483829558323, 289310817375, 1429815836] := by
  rw [show D2M8K2.u4346 = KTree.node D2M8K2.u4330 (nat_lit 9915800) (nat_lit 3848898806) (nat_lit 0) D2M8K2.u4345 from rfl, totK_node, atot4330, atot4345]
  decide +kernel

theorem arows4380 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4380 = true := by
  rw [show D2M8K2.u4380 = KTree.node D2M8K2.u4364 (nat_lit 9954533) (nat_lit 2316145649) (nat_lit 0) D2M8K2.u4379 from rfl, allE_node, arows4364, irow4380, arows4379]
  all_goals rfl

theorem atot4380 : totK PD2M8K2 D2M8K2.u4380 = [0, 1647549989118, 6248244260175, 8477539918902, 7396196379874, 4345504970280, 575351781357, 12189850367] := by
  rw [show D2M8K2.u4380 = KTree.node D2M8K2.u4364 (nat_lit 9954533) (nat_lit 2316145649) (nat_lit 0) D2M8K2.u4379 from rfl, totK_node, atot4364, atot4379]
  decide +kernel

theorem arows4411 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4411 = true := by
  rw [show D2M8K2.u4411 = KTree.node D2M8K2.u4395 (nat_lit 10004024) (nat_lit 3744046299) (nat_lit 0) D2M8K2.u4410 from rfl, allE_node, arows4395, irow4411, arows4410]
  all_goals rfl

theorem atot4411 : totK PD2M8K2 D2M8K2.u4411 = [0, 2048132857640, 8985852659459, 12328714593937, 5081184326048, 567273877352, 26560708531, 0] := by
  rw [show D2M8K2.u4411 = KTree.node D2M8K2.u4395 (nat_lit 10004024) (nat_lit 3744046299) (nat_lit 0) D2M8K2.u4410 from rfl, totK_node, atot4395, atot4410]
  decide +kernel

theorem arows4443 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4443 = true := by
  rw [show D2M8K2.u4443 = KTree.node D2M8K2.u4427 (nat_lit 10036114) (nat_lit 4010957455) (nat_lit 0) D2M8K2.u4442 from rfl, allE_node, arows4427, irow4443, arows4442]
  all_goals rfl

theorem atot4443 : totK PD2M8K2 D2M8K2.u4443 = [0, 1686323782831, 7463148379830, 11409517591315, 7106861696904, 1293726617159, 32826569844, 0] := by
  rw [show D2M8K2.u4443 = KTree.node D2M8K2.u4427 (nat_lit 10036114) (nat_lit 4010957455) (nat_lit 0) D2M8K2.u4442 from rfl, totK_node, atot4427, atot4442]
  decide +kernel

theorem arows4474 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4474 = true := by
  rw [show D2M8K2.u4474 = KTree.node D2M8K2.u4458 (nat_lit 10071462) (nat_lit 3059707515) (nat_lit 0) D2M8K2.u4473 from rfl, allE_node, arows4458, irow4474, arows4473]
  all_goals rfl

theorem atot4474 : totK PD2M8K2 D2M8K2.u4474 = [0, 1641059977168, 7843549029534, 12182503878214, 6181262610076, 759077578084, 18797058808, 0] := by
  rw [show D2M8K2.u4474 = KTree.node D2M8K2.u4458 (nat_lit 10071462) (nat_lit 3059707515) (nat_lit 0) D2M8K2.u4473 from rfl, totK_node, atot4458, atot4473]
  decide +kernel

theorem arows4507 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4507 = true := by
  rw [show D2M8K2.u4507 = KTree.node D2M8K2.u4491 (nat_lit 10150292) (nat_lit 3239882713) (nat_lit 0) D2M8K2.u4506 from rfl, allE_node, arows4491, irow4507, arows4506]
  all_goals rfl

theorem atot4507 : totK PD2M8K2 D2M8K2.u4507 = [0, 1987577140659, 8850761643407, 12268276757102, 5181744323926, 491500454095, 6115358396, 0] := by
  rw [show D2M8K2.u4507 = KTree.node D2M8K2.u4491 (nat_lit 10150292) (nat_lit 3239882713) (nat_lit 0) D2M8K2.u4506 from rfl, totK_node, atot4491, atot4506]
  decide +kernel

theorem arows4538 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4538 = true := by
  rw [show D2M8K2.u4538 = KTree.node D2M8K2.u4522 (nat_lit 10188834) (nat_lit 1924035407) (nat_lit 0) D2M8K2.u4537 from rfl, allE_node, arows4522, irow4538, arows4537]
  all_goals rfl

theorem atot4538 : totK PD2M8K2 D2M8K2.u4538 = [0, 770562027082, 5983532195917, 12771997421830, 8172367253033, 1122796435056, 27017989806, 0] := by
  rw [show D2M8K2.u4538 = KTree.node D2M8K2.u4522 (nat_lit 10188834) (nat_lit 1924035407) (nat_lit 0) D2M8K2.u4537 from rfl, totK_node, atot4522, atot4537]
  decide +kernel

theorem arows4570 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4570 = true := by
  rw [show D2M8K2.u4570 = KTree.node D2M8K2.u4554 (nat_lit 10254414) (nat_lit 3873074325) (nat_lit 0) D2M8K2.u4569 from rfl, allE_node, arows4554, irow4570, arows4569]
  all_goals rfl

theorem atot4570 : totK PD2M8K2 D2M8K2.u4570 = [0, 0, 3573580640377, 12267516808849, 10958655990645, 2139280906656, 71840821215, 0] := by
  rw [show D2M8K2.u4570 = KTree.node D2M8K2.u4554 (nat_lit 10254414) (nat_lit 3873074325) (nat_lit 0) D2M8K2.u4569 from rfl, totK_node, atot4554, atot4569]
  decide +kernel

theorem arows4601 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4601 = true := by
  rw [show D2M8K2.u4601 = KTree.node D2M8K2.u4585 (nat_lit 10306948) (nat_lit 3731426758) (nat_lit 0) D2M8K2.u4600 from rfl, allE_node, arows4585, irow4601, arows4600]
  all_goals rfl

theorem atot4601 : totK PD2M8K2 D2M8K2.u4601 = [0, 0, 1843470019691, 8830028234047, 12484279769343, 4908311426361, 464788753096, 7048116272] := by
  rw [show D2M8K2.u4601 = KTree.node D2M8K2.u4585 (nat_lit 10306948) (nat_lit 3731426758) (nat_lit 0) D2M8K2.u4600 from rfl, totK_node, atot4585, atot4600]
  decide +kernel

theorem arows4636 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4636 = true := by
  rw [show D2M8K2.u4636 = KTree.node D2M8K2.u4620 (nat_lit 10390081) (nat_lit 1411258368) (nat_lit 0) D2M8K2.u4635 from rfl, allE_node, arows4620, irow4636, arows4635]
  all_goals rfl

theorem atot4636 : totK PD2M8K2 D2M8K2.u4636 = [0, 0, 2295920746448, 10092465900071, 12352140699758, 3810613077093, 227272726353, 1394496256] := by
  rw [show D2M8K2.u4636 = KTree.node D2M8K2.u4620 (nat_lit 10390081) (nat_lit 1411258368) (nat_lit 0) D2M8K2.u4635 from rfl, totK_node, atot4620, atot4635]
  decide +kernel

theorem arows4667 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4667 = true := by
  rw [show D2M8K2.u4667 = KTree.node D2M8K2.u4651 (nat_lit 10462196) (nat_lit 3216892531) (nat_lit 0) D2M8K2.u4666 from rfl, allE_node, arows4651, irow4667, arows4666]
  all_goals rfl

theorem atot4667 : totK PD2M8K2 D2M8K2.u4667 = [0, 1647845184997, 7775112812702, 11802638946447, 6458785136234, 1115840826523, 36065015899, 0] := by
  rw [show D2M8K2.u4667 = KTree.node D2M8K2.u4651 (nat_lit 10462196) (nat_lit 3216892531) (nat_lit 0) D2M8K2.u4666 from rfl, totK_node, atot4651, atot4666]
  decide +kernel

theorem arows4699 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4699 = true := by
  rw [show D2M8K2.u4699 = KTree.node D2M8K2.u4683 (nat_lit 10504868) (nat_lit 3179901253) (nat_lit 0) D2M8K2.u4698 from rfl, allE_node, arows4683, irow4699, arows4698]
  all_goals rfl

theorem atot4699 : totK PD2M8K2 D2M8K2.u4699 = [0, 2048304457059, 8999317147654, 12147823075030, 5155653275250, 755626569435, 36921873854, 0] := by
  rw [show D2M8K2.u4699 = KTree.node D2M8K2.u4683 (nat_lit 10504868) (nat_lit 3179901253) (nat_lit 0) D2M8K2.u4698 from rfl, totK_node, atot4683, atot4698]
  decide +kernel

theorem arows4730 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4730 = true := by
  rw [show D2M8K2.u4730 = KTree.node D2M8K2.u4714 (nat_lit 10578033) (nat_lit 1836478434) (nat_lit 0) D2M8K2.u4729 from rfl, allE_node, arows4714, irow4730, arows4729]
  all_goals rfl

theorem atot4730 : totK PD2M8K2 D2M8K2.u4730 = [0, 2107560859894, 8363260323379, 11283982679494, 6209613276046, 990650979661, 21096254089, 0] := by
  rw [show D2M8K2.u4730 = KTree.node D2M8K2.u4714 (nat_lit 10578033) (nat_lit 1836478434) (nat_lit 0) D2M8K2.u4729 from rfl, totK_node, atot4714, atot4729]
  decide +kernel

theorem arows4763 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4763 = true := by
  rw [show D2M8K2.u4763 = KTree.node D2M8K2.u4747 (nat_lit 10613617) (nat_lit 1477653589) (nat_lit 0) D2M8K2.u4762 from rfl, allE_node, arows4747, irow4763, arows4762]
  all_goals rfl

theorem atot4763 : totK PD2M8K2 D2M8K2.u4763 = [0, 1547648331122, 7696840446728, 12268589549611, 6364770349613, 784619977389, 19065934916, 0] := by
  rw [show D2M8K2.u4763 = KTree.node D2M8K2.u4747 (nat_lit 10613617) (nat_lit 1477653589) (nat_lit 0) D2M8K2.u4762 from rfl, totK_node, atot4747, atot4762]
  decide +kernel

theorem arows4794 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4794 = true := by
  rw [show D2M8K2.u4794 = KTree.node D2M8K2.u4778 (nat_lit 10652132) (nat_lit 2827845027) (nat_lit 0) D2M8K2.u4793 from rfl, allE_node, arows4778, irow4794, arows4793]
  all_goals rfl

theorem atot4794 : totK PD2M8K2 D2M8K2.u4794 = [0, 1990871917012, 8856541077998, 12313567349373, 5186331400998, 488213266624, 6115358396, 0] := by
  rw [show D2M8K2.u4794 = KTree.node D2M8K2.u4778 (nat_lit 10652132) (nat_lit 2827845027) (nat_lit 0) D2M8K2.u4793 from rfl, totK_node, atot4778, atot4793]
  decide +kernel

theorem arows4826 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4826 = true := by
  rw [show D2M8K2.u4826 = KTree.node D2M8K2.u4810 (nat_lit 10689978) (nat_lit 3564203674) (nat_lit 0) D2M8K2.u4825 from rfl, allE_node, arows4810, irow4826, arows4825]
  all_goals rfl

theorem atot4826 : totK PD2M8K2 D2M8K2.u4826 = [0, 440288014109, 5287858152893, 12978349090161, 8793152902587, 1214255513333, 28226833869, 0] := by
  rw [show D2M8K2.u4826 = KTree.node D2M8K2.u4810 (nat_lit 10689978) (nat_lit 3564203674) (nat_lit 0) D2M8K2.u4825 from rfl, totK_node, atot4810, atot4825]
  decide +kernel

theorem arows4857 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4857 = true := by
  rw [show D2M8K2.u4857 = KTree.node D2M8K2.u4841 (nat_lit 10755854) (nat_lit 3063623536) (nat_lit 0) D2M8K2.u4856 from rfl, allE_node, arows4841, irow4857, arows4856]
  all_goals rfl

theorem atot4857 : totK PD2M8K2 D2M8K2.u4857 = [0, 0, 3534235094826, 11920648307021, 11000564283505, 2534354238691, 99817406269, 0] := by
  rw [show D2M8K2.u4857 = KTree.node D2M8K2.u4841 (nat_lit 10755854) (nat_lit 3063623536) (nat_lit 0) D2M8K2.u4856 from rfl, totK_node, atot4841, atot4856]
  decide +kernel

theorem arows4891 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4891 = true := by
  rw [show D2M8K2.u4891 = KTree.node D2M8K2.u4875 (nat_lit 10856256) (nat_lit 3507538042) (nat_lit 0) D2M8K2.u4890 from rfl, allE_node, arows4875, irow4891, arows4890]
  all_goals rfl

theorem atot4891 : totK PD2M8K2 D2M8K2.u4891 = [0, 0, 1908854709179, 8939045640637, 12405844449668, 4867044597627, 461135898583, 7105533120] := by
  rw [show D2M8K2.u4891 = KTree.node D2M8K2.u4875 (nat_lit 10856256) (nat_lit 3507538042) (nat_lit 0) D2M8K2.u4890 from rfl, totK_node, atot4875, atot4890]
  decide +kernel

theorem arows4922 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4922 = true := by
  rw [show D2M8K2.u4922 = KTree.node D2M8K2.u4906 (nat_lit 10897310) (nat_lit 3542804028) (nat_lit 0) D2M8K2.u4921 from rfl, allE_node, arows4906, irow4922, arows4921]
  all_goals rfl

theorem atot4922 : totK PD2M8K2 D2M8K2.u4922 = [0, 0, 2388882468856, 10124986220824, 12259695900198, 3797695190807, 225873544967, 1430229726] := by
  rw [show D2M8K2.u4922 = KTree.node D2M8K2.u4906 (nat_lit 10897310) (nat_lit 3542804028) (nat_lit 0) D2M8K2.u4921 from rfl, totK_node, atot4906, atot4921]
  decide +kernel

theorem arows4954 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4954 = true := by
  rw [show D2M8K2.u4954 = KTree.node D2M8K2.u4938 (nat_lit 10959501) (nat_lit 1153254776) (nat_lit 0) D2M8K2.u4953 from rfl, allE_node, arows4938, irow4954, arows4953]
  all_goals rfl

theorem atot4954 : totK PD2M8K2 D2M8K2.u4954 = [0, 1644326566028, 7960783117605, 12109742079527, 5975758587125, 925749721529, 29221921972, 0] := by
  rw [show D2M8K2.u4954 = KTree.node D2M8K2.u4938 (nat_lit 10959501) (nat_lit 1153254776) (nat_lit 0) D2M8K2.u4953 from rfl, totK_node, atot4938, atot4953]
  decide +kernel

theorem arows4985 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4985 = true := by
  rw [show D2M8K2.u4985 = KTree.node D2M8K2.u4969 (nat_lit 11005130) (nat_lit 4022612714) (nat_lit 0) D2M8K2.u4984 from rfl, allE_node, arows4969, irow4985, arows4984]
  all_goals rfl

theorem atot4985 : totK PD2M8K2 D2M8K2.u4985 = [0, 2045971677713, 8693623714658, 11765305374939, 5637185539688, 952945102948, 42081742489, 0] := by
  rw [show D2M8K2.u4985 = KTree.node D2M8K2.u4969 (nat_lit 11005130) (nat_lit 4022612714) (nat_lit 0) D2M8K2.u4984 from rfl, totK_node, atot4969, atot4984]
  decide +kernel

theorem arows5018 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5018 = true := by
  rw [show D2M8K2.u5018 = KTree.node D2M8K2.u5002 (nat_lit 11037714) (nat_lit 3422342630) (nat_lit 0) D2M8K2.u5017 from rfl, allE_node, arows5002, irow5018, arows5017]
  all_goals rfl

theorem atot5018 : totK PD2M8K2 D2M8K2.u5018 = [0, 1986782653346, 8294932265769, 11582021836924, 6133958323051, 874296278407, 17142851236, 0] := by
  rw [show D2M8K2.u5018 = KTree.node D2M8K2.u5002 (nat_lit 11037714) (nat_lit 3422342630) (nat_lit 0) D2M8K2.u5017 from rfl, totK_node, atot5002, atot5017]
  decide +kernel

theorem arows5049 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5049 = true := by
  rw [show D2M8K2.u5049 = KTree.node D2M8K2.u5033 (nat_lit 11077183) (nat_lit 1666812130) (nat_lit 0) D2M8K2.u5048 from rfl, allE_node, arows5033, irow5049, arows5048]
  all_goals rfl

theorem atot5049 : totK PD2M8K2 D2M8K2.u5049 = [0, 1987314446367, 8754368508763, 12065854996322, 5345006334786, 644319063831, 17590593026, 0] := by
  rw [show D2M8K2.u5049 = KTree.node D2M8K2.u5033 (nat_lit 11077183) (nat_lit 1666812130) (nat_lit 0) D2M8K2.u5048 from rfl, totK_node, atot5033, atot5048]
  decide +kernel

theorem arows5081 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5081 = true := by
  rw [show D2M8K2.u5081 = KTree.node D2M8K2.u5065 (nat_lit 11115509) (nat_lit 1198518544) (nat_lit 0) D2M8K2.u5080 from rfl, allE_node, arows5065, irow5081, arows5080]
  all_goals rfl

theorem atot5081 : totK PD2M8K2 D2M8K2.u5081 = [0, 1833173780270, 8101710493908, 11888459147618, 6044220137658, 763794617492, 19065934916, 0] := by
  rw [show D2M8K2.u5081 = KTree.node D2M8K2.u5065 (nat_lit 11115509) (nat_lit 1198518544) (nat_lit 0) D2M8K2.u5080 from rfl, totK_node, atot5065, atot5080]
  decide +kernel

theorem arows5112 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5112 = true := by
  rw [show D2M8K2.u5112 = KTree.node D2M8K2.u5096 (nat_lit 11150862) (nat_lit 3942114232) (nat_lit 0) D2M8K2.u5111 from rfl, allE_node, arows5096, irow5112, arows5111]
  all_goals rfl

theorem atot5112 : totK PD2M8K2 D2M8K2.u5112 = [0, 269119064056, 5043558441164, 13425452056390, 8924041099262, 966877998724, 10943406944, 0] := by
  rw [show D2M8K2.u5112 = KTree.node D2M8K2.u5096 (nat_lit 11150862) (nat_lit 3942114232) (nat_lit 0) D2M8K2.u5111 from rfl, totK_node, atot5096, atot5111]
  decide +kernel

theorem arows5148 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5148 = true := by
  rw [show D2M8K2.u5148 = KTree.node D2M8K2.u5132 (nat_lit 11255856) (nat_lit 3316855310) (nat_lit 0) D2M8K2.u5147 from rfl, allE_node, arows5132, irow5148, arows5147]
  all_goals rfl

theorem atot5148 : totK PD2M8K2 D2M8K2.u5148 = [0, 0, 3352120198396, 11853041709948, 11284570662996, 2520086258246, 97484528777, 0] := by
  rw [show D2M8K2.u5148 = KTree.node D2M8K2.u5132 (nat_lit 11255856) (nat_lit 3316855310) (nat_lit 0) D2M8K2.u5147 from rfl, totK_node, atot5132, atot5147]
  decide +kernel

theorem arows5179 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5179 = true := by
  rw [show D2M8K2.u5179 = KTree.node D2M8K2.u5163 (nat_lit 11333962) (nat_lit 3911596471) (nat_lit 0) D2M8K2.u5178 from rfl, allE_node, arows5163, irow5179, arows5178]
  all_goals rfl

theorem atot5179 : totK PD2M8K2 D2M8K2.u5179 = [0, 0, 3385504276650, 12106008936549, 11217997328445, 2161214001579, 65926487982, 0] := by
  rw [show D2M8K2.u5179 = KTree.node D2M8K2.u5163 (nat_lit 11333962) (nat_lit 3911596471) (nat_lit 0) D2M8K2.u5178 from rfl, totK_node, atot5163, atot5178]
  decide +kernel

theorem arows5211 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5211 = true := by
  rw [show D2M8K2.u5211 = KTree.node D2M8K2.u5195 (nat_lit 11388536) (nat_lit 3413304591) (nat_lit 0) D2M8K2.u5210 from rfl, allE_node, arows5195, irow5211, arows5210]
  all_goals rfl

theorem atot5211 : totK PD2M8K2 D2M8K2.u5211 = [0, 823190571224, 4176294174223, 9277133075163, 10356937908908, 3691363956529, 286328459286, 1493059870] := by
  rw [show D2M8K2.u5211 = KTree.node D2M8K2.u5195 (nat_lit 11388536) (nat_lit 3413304591) (nat_lit 0) D2M8K2.u5210 from rfl, totK_node, atot5195, atot5210]
  decide +kernel

theorem arows5242 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5242 = true := by
  rw [show D2M8K2.u5242 = KTree.node D2M8K2.u5226 (nat_lit 11478973) (nat_lit 1208780007) (nat_lit 0) D2M8K2.u5241 from rfl, allE_node, arows5226, irow5242, arows5241]
  all_goals rfl

theorem atot5242 : totK PD2M8K2 D2M8K2.u5242 = [0, 2207291663848, 9410640552777, 12409379136559, 4582183676817, 300626285926, 1369150432, 0] := by
  rw [show D2M8K2.u5242 = KTree.node D2M8K2.u5226 (nat_lit 11478973) (nat_lit 1208780007) (nat_lit 0) D2M8K2.u5241 from rfl, totK_node, atot5226, atot5241]
  decide +kernel

theorem arows5275 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5275 = true := by
  rw [show D2M8K2.u5275 = KTree.node D2M8K2.u5259 (nat_lit 11519194) (nat_lit 3800073579) (nat_lit 0) D2M8K2.u5274 from rfl, allE_node, arows5259, irow5275, arows5274]
  all_goals rfl

theorem atot5275 : totK PD2M8K2 D2M8K2.u5275 = [0, 1466625853731, 6874887204119, 11435617481638, 7725724273053, 1566737135737, 58018127943, 0] := by
  rw [show D2M8K2.u5275 = KTree.node D2M8K2.u5259 (nat_lit 11519194) (nat_lit 3800073579) (nat_lit 0) D2M8K2.u5274 from rfl, totK_node, atot5259, atot5274]
  decide +kernel

theorem arows5306 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5306 = true := by
  rw [show D2M8K2.u5306 = KTree.node D2M8K2.u5290 (nat_lit 11551541) (nat_lit 1835578070) (nat_lit 0) D2M8K2.u5305 from rfl, allE_node, arows5290, irow5306, arows5305]
  all_goals rfl

theorem atot5306 : totK PD2M8K2 D2M8K2.u5306 = [0, 1570626386177, 7990922205371, 12457691164316, 6096878772274, 685988839291, 12004276665, 0] := by
  rw [show D2M8K2.u5306 = KTree.node D2M8K2.u5290 (nat_lit 11551541) (nat_lit 1835578070) (nat_lit 0) D2M8K2.u5305 from rfl, totK_node, atot5290, atot5305]
  decide +kernel

theorem arows5338 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5338 = true := by
  rw [show D2M8K2.u5338 = KTree.node D2M8K2.u5322 (nat_lit 11590785) (nat_lit 1582974707) (nat_lit 0) D2M8K2.u5337 from rfl, allE_node, arows5322, irow5338, arows5337]
  all_goals rfl

theorem atot5338 : totK PD2M8K2 D2M8K2.u5338 = [0, 1734832317818, 8102503998854, 12258014678701, 6139279969516, 702652134776, 12143333308, 0] := by
  rw [show D2M8K2.u5338 = KTree.node D2M8K2.u5322 (nat_lit 11590785) (nat_lit 1582974707) (nat_lit 0) D2M8K2.u5337 from rfl, totK_node, atot5322, atot5337]
  decide +kernel

theorem arows5369 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5369 = true := by
  rw [show D2M8K2.u5369 = KTree.node D2M8K2.u5353 (nat_lit 11670934) (nat_lit 3553329980) (nat_lit 0) D2M8K2.u5368 from rfl, allE_node, arows5353, irow5369, arows5368]
  all_goals rfl

theorem atot5369 : totK PD2M8K2 D2M8K2.u5369 = [0, 1990563963679, 8823746805078, 12192214794846, 5315383945781, 503899558484, 6190125969, 0] := by
  rw [show D2M8K2.u5369 = KTree.node D2M8K2.u5353 (nat_lit 11670934) (nat_lit 3553329980) (nat_lit 0) D2M8K2.u5368 from rfl, totK_node, atot5353, atot5368]
  decide +kernel

theorem arows5403 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5403 = true := by
  rw [show D2M8K2.u5403 = KTree.node D2M8K2.u5387 (nat_lit 11713904) (nat_lit 2886136491) (nat_lit 0) D2M8K2.u5402 from rfl, allE_node, arows5387, irow5403, arows5402]
  all_goals rfl

theorem atot5403 : totK PD2M8K2 D2M8K2.u5403 = [0, 0, 3785018021722, 12364627310565, 10578556917804, 2153794128838, 78792549776, 0] := by
  rw [show D2M8K2.u5403 = KTree.node D2M8K2.u5387 (nat_lit 11713904) (nat_lit 2886136491) (nat_lit 0) D2M8K2.u5402 from rfl, totK_node, atot5387, atot5402]
  decide +kernel

theorem arows5434 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5434 = true := by
  rw [show D2M8K2.u5434 = KTree.node D2M8K2.u5418 (nat_lit 11788188) (nat_lit 3155367300) (nat_lit 0) D2M8K2.u5433 from rfl, allE_node, arows5418, irow5434, arows5433]
  all_goals rfl

theorem atot5434 : totK PD2M8K2 D2M8K2.u5434 = [0, 0, 2406457968979, 10005878900249, 12207747565500, 3960256760513, 245984221723, 1501162176] := by
  rw [show D2M8K2.u5434 = KTree.node D2M8K2.u5418 (nat_lit 11788188) (nat_lit 3155367300) (nat_lit 0) D2M8K2.u5433 from rfl, totK_node, atot5418, atot5433]
  decide +kernel

theorem arows5466 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5466 = true := by
  rw [show D2M8K2.u5466 = KTree.node D2M8K2.u5450 (nat_lit 11836962) (nat_lit 2819827655) (nat_lit 0) D2M8K2.u5465 from rfl, allE_node, arows5450, irow5466, arows5465]
  all_goals rfl

theorem atot5466 : totK PD2M8K2 D2M8K2.u5466 = [0, 0, 2373172089294, 9883875219386, 12156757285807, 4185677677479, 272019821102, 1510868091] := by
  rw [show D2M8K2.u5466 = KTree.node D2M8K2.u5450 (nat_lit 11836962) (nat_lit 2819827655) (nat_lit 0) D2M8K2.u5465 from rfl, totK_node, atot5450, atot5465]
  decide +kernel

theorem arows5497 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5497 = true := by
  rw [show D2M8K2.u5497 = KTree.node D2M8K2.u5481 (nat_lit 11921218) (nat_lit 4097396695) (nat_lit 0) D2M8K2.u5496 from rfl, allE_node, arows5481, irow5497, arows5496]
  all_goals rfl

theorem atot5497 : totK PD2M8K2 D2M8K2.u5497 = [0, 0, 1704008227985, 8528865443338, 12796754831310, 5269395148795, 421718937677, 2822133622] := by
  rw [show D2M8K2.u5497 = KTree.node D2M8K2.u5481 (nat_lit 11921218) (nat_lit 4097396695) (nat_lit 0) D2M8K2.u5496 from rfl, totK_node, atot5481, atot5496]
  decide +kernel

theorem arows5530 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5530 = true := by
  rw [show D2M8K2.u5530 = KTree.node D2M8K2.u5514 (nat_lit 11959818) (nat_lit 2932517314) (nat_lit 0) D2M8K2.u5529 from rfl, allE_node, arows5514, irow5530, arows5529]
  all_goals rfl

theorem atot5530 : totK PD2M8K2 D2M8K2.u5530 = [2096993147398, 9108417296717, 11747825362477, 4151892227689, 541990347615, 619028554546, 235492752849, 10297110227] := by
  rw [show D2M8K2.u5530 = KTree.node D2M8K2.u5514 (nat_lit 11959818) (nat_lit 2932517314) (nat_lit 0) D2M8K2.u5529 from rfl, totK_node, atot5514, atot5529]
  decide +kernel

theorem arows5561 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5561 = true := by
  rw [show D2M8K2.u5561 = KTree.node D2M8K2.u5545 (nat_lit 12041897) (nat_lit 1800102768) (nat_lit 0) D2M8K2.u5560 from rfl, allE_node, arows5545, irow5561, arows5560]
  all_goals rfl

theorem atot5561 : totK PD2M8K2 D2M8K2.u5561 = [2034459393298, 8889231785428, 12098300880664, 5212234502198, 576303678771, 14222663156, 0, 0] := by
  rw [show D2M8K2.u5561 = KTree.node D2M8K2.u5545 (nat_lit 12041897) (nat_lit 1800102768) (nat_lit 0) D2M8K2.u5560 from rfl, totK_node, atot5545, atot5560]
  decide +kernel

theorem arows5593 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5593 = true := by
  rw [show D2M8K2.u5593 = KTree.node D2M8K2.u5577 (nat_lit 12083915) (nat_lit 2735669354) (nat_lit 0) D2M8K2.u5592 from rfl, allE_node, arows5577, irow5593, arows5592]
  all_goals rfl

theorem atot5593 : totK PD2M8K2 D2M8K2.u5593 = [1648442144398, 7874567203878, 12067475814770, 6127677586415, 777776471801, 19973123287, 0, 0] := by
  rw [show D2M8K2.u5593 = KTree.node D2M8K2.u5577 (nat_lit 12083915) (nat_lit 2735669354) (nat_lit 0) D2M8K2.u5592 from rfl, totK_node, atot5577, atot5592]
  decide +kernel

theorem arows5624 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5624 = true := by
  rw [show D2M8K2.u5624 = KTree.node D2M8K2.u5608 (nat_lit 12121312) (nat_lit 1792061012) (nat_lit 0) D2M8K2.u5623 from rfl, allE_node, arows5608, irow5624, arows5623]
  all_goals rfl

theorem atot5624 : totK PD2M8K2 D2M8K2.u5624 = [1977850742301, 8952058287037, 12343624512472, 4975026919657, 417286116822, 4805451294, 0, 0] := by
  rw [show D2M8K2.u5624 = KTree.node D2M8K2.u5608 (nat_lit 12121312) (nat_lit 1792061012) (nat_lit 0) D2M8K2.u5623 from rfl, totK_node, atot5608, atot5623]
  decide +kernel

theorem arows5659 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5659 = true := by
  rw [show D2M8K2.u5659 = KTree.node D2M8K2.u5643 (nat_lit 12161987) (nat_lit 2852505898) (nat_lit 0) D2M8K2.u5658 from rfl, allE_node, arows5643, irow5659, arows5658]
  all_goals rfl

theorem atot5659 : totK PD2M8K2 D2M8K2.u5659 = [1988996583632, 8675978874591, 12067941923456, 5493875152069, 562991642497, 7363056991, 0, 0] := by
  rw [show D2M8K2.u5659 = KTree.node D2M8K2.u5643 (nat_lit 12161987) (nat_lit 2852505898) (nat_lit 0) D2M8K2.u5658 from rfl, totK_node, atot5643, atot5658]
  decide +kernel

theorem arows5690 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5690 = true := by
  rw [show D2M8K2.u5690 = KTree.node D2M8K2.u5674 (nat_lit 12201985) (nat_lit 1549404043) (nat_lit 0) D2M8K2.u5689 from rfl, allE_node, arows5674, irow5690, arows5689]
  all_goals rfl

theorem atot5690 : totK PD2M8K2 D2M8K2.u5690 = [0, 2906110657113, 11044065477026, 11496984159137, 2796230089525, 166533066126, 1369150432, 0] := by
  rw [show D2M8K2.u5690 = KTree.node D2M8K2.u5674 (nat_lit 12201985) (nat_lit 1549404043) (nat_lit 0) D2M8K2.u5689 from rfl, totK_node, atot5674, atot5689]
  decide +kernel

theorem arows5722 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5722 = true := by
  rw [show D2M8K2.u5722 = KTree.node D2M8K2.u5706 (nat_lit 12282378) (nat_lit 3591557172) (nat_lit 0) D2M8K2.u5721 from rfl, allE_node, arows5706, irow5722, arows5721]
  all_goals rfl

theorem atot5722 : totK PD2M8K2 D2M8K2.u5722 = [0, 2448498480453, 10290909867357, 12175396102912, 3465689854281, 210810351441, 0, 0] := by
  rw [show D2M8K2.u5722 = KTree.node D2M8K2.u5706 (nat_lit 12282378) (nat_lit 3591557172) (nat_lit 0) D2M8K2.u5721 from rfl, totK_node, atot5706, atot5721]
  decide +kernel

theorem arows5753 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5753 = true := by
  rw [show D2M8K2.u5753 = KTree.node D2M8K2.u5737 (nat_lit 12362576) (nat_lit 3725915661) (nat_lit 0) D2M8K2.u5752 from rfl, allE_node, arows5737, irow5753, arows5752]
  all_goals rfl

theorem atot5753 : totK PD2M8K2 D2M8K2.u5753 = [0, 3476282221055, 12041467238635, 10999246386691, 2112591038077, 65730020013, 0, 0] := by
  rw [show D2M8K2.u5753 = KTree.node D2M8K2.u5737 (nat_lit 12362576) (nat_lit 3725915661) (nat_lit 0) D2M8K2.u5752 from rfl, totK_node, atot5737, atot5752]
  decide +kernel

theorem arows5786 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5786 = true := by
  rw [show D2M8K2.u5786 = KTree.node D2M8K2.u5770 (nat_lit 12419404) (nat_lit 3715213369) (nat_lit 0) D2M8K2.u5785 from rfl, allE_node, arows5770, irow5786, arows5785]
  all_goals rfl

theorem atot5786 : totK PD2M8K2 D2M8K2.u5786 = [1518795441172, 6859982825032, 11351613996781, 7777900792791, 1467449059639, 43173908432, 0, 0] := by
  rw [show D2M8K2.u5786 = KTree.node D2M8K2.u5770 (nat_lit 12419404) (nat_lit 3715213369) (nat_lit 0) D2M8K2.u5785 from rfl, totK_node, atot5770, atot5785]
  decide +kernel

theorem arows5817 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5817 = true := by
  rw [show D2M8K2.u5817 = KTree.node D2M8K2.u5801 (nat_lit 12514503) (nat_lit 3638020786) (nat_lit 0) D2M8K2.u5816 from rfl, allE_node, arows5801, irow5817, arows5816]
  all_goals rfl

theorem atot5817 : totK PD2M8K2 D2M8K2.u5817 = [1282786411987, 6514081905948, 11530406287704, 7926322482350, 1599919078487, 58018127943, 0, 0] := by
  rw [show D2M8K2.u5817 = KTree.node D2M8K2.u5801 (nat_lit 12514503) (nat_lit 3638020786) (nat_lit 0) D2M8K2.u5816 from rfl, totK_node, atot5801, atot5816]
  decide +kernel

theorem arows5849 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5849 = true := by
  rw [show D2M8K2.u5849 = KTree.node D2M8K2.u5833 (nat_lit 12545901) (nat_lit 1400379770) (nat_lit 0) D2M8K2.u5848 from rfl, allE_node, arows5833, irow5849, arows5848]
  all_goals rfl

theorem atot5849 : totK PD2M8K2 D2M8K2.u5849 = [1588061069923, 7805085282781, 12357094289911, 6284291056954, 769326912638, 18797058808, 0, 0] := by
  rw [show D2M8K2.u5849 = KTree.node D2M8K2.u5833 (nat_lit 12545901) (nat_lit 1400379770) (nat_lit 0) D2M8K2.u5848 from rfl, totK_node, atot5833, atot5848]
  decide +kernel

theorem arows5880 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5880 = true := by
  rw [show D2M8K2.u5880 = KTree.node D2M8K2.u5864 (nat_lit 12590617) (nat_lit 1176297280) (nat_lit 0) D2M8K2.u5879 from rfl, allE_node, arows5864, irow5880, arows5879]
  all_goals rfl

theorem atot5880 : totK PD2M8K2 D2M8K2.u5880 = [1943567509772, 8671056631627, 12046314069538, 5496798291425, 666931849548, 17826068843, 0, 0] := by
  rw [show D2M8K2.u5880 = KTree.node D2M8K2.u5864 (nat_lit 12590617) (nat_lit 1176297280) (nat_lit 0) D2M8K2.u5879 from rfl, totK_node, atot5864, atot5879]
  decide +kernel

theorem arows5914 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5914 = true := by
  rw [show D2M8K2.u5914 = KTree.node D2M8K2.u5898 (nat_lit 12628446) (nat_lit 3969889731) (nat_lit 0) D2M8K2.u5913 from rfl, allE_node, arows5898, irow5914, arows5913]
  all_goals rfl

theorem atot5914 : totK PD2M8K2 D2M8K2.u5914 = [1826751747728, 8627729631574, 12439985742355, 5355667459702, 503001606561, 6115358396, 0, 0] := by
  rw [show D2M8K2.u5914 = KTree.node D2M8K2.u5898 (nat_lit 12628446) (nat_lit 3969889731) (nat_lit 0) D2M8K2.u5913 from rfl, totK_node, atot5898, atot5913]
  decide +kernel

theorem arows5945 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5945 = true := by
  rw [show D2M8K2.u5945 = KTree.node D2M8K2.u5929 (nat_lit 12668740) (nat_lit 4026864470) (nat_lit 0) D2M8K2.u5944 from rfl, allE_node, arows5929, irow5945, arows5944]
  all_goals rfl

theorem atot5945 : totK PD2M8K2 D2M8K2.u5945 = [1641561038001, 7916257690007, 12335478135727, 6348295467997, 721266937469, 11121530615, 0, 0] := by
  rw [show D2M8K2.u5945 = KTree.node D2M8K2.u5929 (nat_lit 12668740) (nat_lit 4026864470) (nat_lit 0) D2M8K2.u5944 from rfl, totK_node, atot5929, atot5944]
  decide +kernel

theorem arows5977 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5977 = true := by
  rw [show D2M8K2.u5977 = KTree.node D2M8K2.u5961 (nat_lit 12746357) (nat_lit 2400409922) (nat_lit 0) D2M8K2.u5976 from rfl, allE_node, arows5961, irow5977, arows5976]
  all_goals rfl

theorem atot5977 : totK PD2M8K2 D2M8K2.u5977 = [0, 2117708296215, 8882950040401, 11588350685436, 5296690543564, 891275849646, 41989737272, 0] := by
  rw [show D2M8K2.u5977 = KTree.node D2M8K2.u5961 (nat_lit 12746357) (nat_lit 2400409922) (nat_lit 0) D2M8K2.u5976 from rfl, totK_node, atot5961, atot5976]
  decide +kernel

theorem arows6008 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6008 = true := by
  rw [show D2M8K2.u6008 = KTree.node D2M8K2.u5992 (nat_lit 12778227) (nat_lit 2995946266) (nat_lit 0) D2M8K2.u6007 from rfl, allE_node, arows5992, irow6008, arows6007]
  all_goals rfl

theorem atot6008 : totK PD2M8K2 D2M8K2.u6008 = [0, 2042346936617, 8604238184077, 11669905481133, 5676876008341, 754681635007, 15657634319, 0] := by
  rw [show D2M8K2.u6008 = KTree.node D2M8K2.u5992 (nat_lit 12778227) (nat_lit 2995946266) (nat_lit 0) D2M8K2.u6007 from rfl, totK_node, atot5992, atot6007]
  decide +kernel

theorem arows6041 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6041 = true := by
  rw [show D2M8K2.u6041 = KTree.node D2M8K2.u6025 (nat_lit 12820875) (nat_lit 3439577478) (nat_lit 0) D2M8K2.u6040 from rfl, allE_node, arows6025, irow6041, arows6040]
  all_goals rfl

theorem atot6041 : totK PD2M8K2 D2M8K2.u6041 = [0, 1662341342203, 8238213332582, 12569650346208, 5772604104874, 543437681735, 6546549506, 0] := by
  rw [show D2M8K2.u6041 = KTree.node D2M8K2.u6025 (nat_lit 12820875) (nat_lit 3439577478) (nat_lit 0) D2M8K2.u6040 from rfl, totK_node, atot6025, atot6040]
  decide +kernel

theorem arows6072 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6072 = true := by
  rw [show D2M8K2.u6072 = KTree.node D2M8K2.u6056 (nat_lit 12862636) (nat_lit 2606325706) (nat_lit 0) D2M8K2.u6071 from rfl, allE_node, arows6056, irow6072, arows6071]
  all_goals rfl

theorem atot6072 : totK PD2M8K2 D2M8K2.u6072 = [0, 1987424597332, 8842983852769, 12144208805326, 5168602383191, 498129023976, 6624648996, 0] := by
  rw [show D2M8K2.u6072 = KTree.node D2M8K2.u6056 (nat_lit 12862636) (nat_lit 2606325706) (nat_lit 0) D2M8K2.u6071 from rfl, totK_node, atot6056, atot6071]
  decide +kernel

theorem arows6104 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6104 = true := by
  rw [show D2M8K2.u6104 = KTree.node D2M8K2.u6088 (nat_lit 12904442) (nat_lit 4243551115) (nat_lit 0) D2M8K2.u6103 from rfl, allE_node, arows6088, irow6104, arows6103]
  all_goals rfl

theorem atot6104 : totK PD2M8K2 D2M8K2.u6104 = [0, 1999268849286, 9212532761186, 12560577055691, 4763715811342, 341279516639, 1429815836, 0] := by
  rw [show D2M8K2.u6104 = KTree.node D2M8K2.u6088 (nat_lit 12904442) (nat_lit 4243551115) (nat_lit 0) D2M8K2.u6103 from rfl, totK_node, atot6088, atot6103]
  decide +kernel

theorem arows6135 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6135 = true := by
  rw [show D2M8K2.u6135 = KTree.node D2M8K2.u6119 (nat_lit 12946855) (nat_lit 1949934295) (nat_lit 0) D2M8K2.u6134 from rfl, allE_node, arows6119, irow6135, arows6134]
  all_goals rfl

theorem atot6135 : totK PD2M8K2 D2M8K2.u6135 = [2005649722024, 7387467190409, 8693353492074, 6137552121150, 3832212219119, 582836050331, 12189850367, 0] := by
  rw [show D2M8K2.u6135 = KTree.node D2M8K2.u6119 (nat_lit 12946855) (nat_lit 1949934295) (nat_lit 0) D2M8K2.u6134 from rfl, totK_node, atot6119, atot6134]
  decide +kernel

theorem arows6172 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6172 = true := by
  rw [show D2M8K2.u6172 = KTree.node D2M8K2.u6156 (nat_lit 12987971) (nat_lit 2852455945) (nat_lit 0) D2M8K2.u6171 from rfl, allE_node, arows6156, irow6172, arows6171]
  all_goals rfl

theorem atot6172 : totK PD2M8K2 D2M8K2.u6172 = [2028884253974, 9139376714823, 12519774401928, 4834657271565, 358853483883, 1369150432, 0, 0] := by
  rw [show D2M8K2.u6172 = KTree.node D2M8K2.u6156 (nat_lit 12987971) (nat_lit 2852455945) (nat_lit 0) D2M8K2.u6171 from rfl, totK_node, atot6156, atot6171]
  decide +kernel

theorem arows6203 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6203 = true := by
  rw [show D2M8K2.u6203 = KTree.node D2M8K2.u6187 (nat_lit 13019569) (nat_lit 1152982993) (nat_lit 0) D2M8K2.u6202 from rfl, allE_node, arows6187, irow6203, arows6202]
  all_goals rfl

theorem atot6203 : totK PD2M8K2 D2M8K2.u6203 = [1425524695379, 6705623762500, 11379554532172, 7824553330194, 1588223757062, 58018127943, 0, 0] := by
  rw [show D2M8K2.u6203 = KTree.node D2M8K2.u6187 (nat_lit 13019569) (nat_lit 1152982993) (nat_lit 0) D2M8K2.u6202 from rfl, totK_node, atot6187, atot6202]
  decide +kernel

theorem arows6235 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6235 = true := by
  rw [show D2M8K2.u6235 = KTree.node D2M8K2.u6219 (nat_lit 13051606) (nat_lit 3273917013) (nat_lit 0) D2M8K2.u6234 from rfl, allE_node, arows6219, irow6235, arows6234]
  all_goals rfl

theorem atot6235 : totK PD2M8K2 D2M8K2.u6235 = [1531121744059, 7763963622409, 12366978848049, 6246990653933, 756985413433, 18797058808, 0, 0] := by
  rw [show D2M8K2.u6235 = KTree.node D2M8K2.u6219 (nat_lit 13051606) (nat_lit 3273917013) (nat_lit 0) D2M8K2.u6234 from rfl, totK_node, atot6219, atot6234]
  decide +kernel

theorem arows6266 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6266 = true := by
  rw [show D2M8K2.u6266 = KTree.node D2M8K2.u6250 (nat_lit 13130236) (nat_lit 3356675371) (nat_lit 0) D2M8K2.u6265 from rfl, allE_node, arows6250, irow6266, arows6265]
  all_goals rfl

theorem atot6266 : totK PD2M8K2 D2M8K2.u6266 = [2014561339350, 8921627722530, 12185734702268, 5077692728865, 490961718069, 6115358396, 0, 0] := by
  rw [show D2M8K2.u6266 = KTree.node D2M8K2.u6250 (nat_lit 13130236) (nat_lit 3356675371) (nat_lit 0) D2M8K2.u6265 from rfl, totK_node, atot6250, atot6265]
  decide +kernel

theorem arows6299 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6299 = true := by
  rw [show D2M8K2.u6299 = KTree.node D2M8K2.u6283 (nat_lit 13169697) (nat_lit 1508951237) (nat_lit 0) D2M8K2.u6298 from rfl, allE_node, arows6283, irow6299, arows6298]
  all_goals rfl

theorem atot6299 : totK PD2M8K2 D2M8K2.u6299 = [1195523425885, 6789837900318, 12336384149884, 7373392260044, 1082649455486, 32872698681, 0, 0] := by
  rw [show D2M8K2.u6299 = KTree.node D2M8K2.u6283 (nat_lit 13169697) (nat_lit 1508951237) (nat_lit 0) D2M8K2.u6298 from rfl, totK_node, atot6283, atot6298]
  decide +kernel

theorem arows6330 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6330 = true := by
  rw [show D2M8K2.u6330 = KTree.node D2M8K2.u6314 (nat_lit 13207460) (nat_lit 2689666247) (nat_lit 0) D2M8K2.u6329 from rfl, allE_node, arows6314, irow6330, arows6329]
  all_goals rfl

theorem atot6330 : totK PD2M8K2 D2M8K2.u6330 = [0, 2165785150751, 9785940498540, 12456925356105, 3850965024027, 234691630663, 1275377855, 0] := by
  rw [show D2M8K2.u6330 = KTree.node D2M8K2.u6314 (nat_lit 13207460) (nat_lit 2689666247) (nat_lit 0) D2M8K2.u6329 from rfl, totK_node, atot6314, atot6329]
  decide +kernel

theorem arows6362 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6362 = true := by
  rw [show D2M8K2.u6362 = KTree.node D2M8K2.u6346 (nat_lit 13250169) (nat_lit 750345718) (nat_lit 0) D2M8K2.u6361 from rfl, allE_node, arows6346, irow6362, arows6361]
  all_goals rfl

theorem atot6362 : totK PD2M8K2 D2M8K2.u6362 = [0, 3286796051049, 11763548393680, 11319795302690, 2507244221694, 90645781599, 0, 0] := by
  rw [show D2M8K2.u6362 = KTree.node D2M8K2.u6346 (nat_lit 13250169) (nat_lit 750345718) (nat_lit 0) D2M8K2.u6361 from rfl, totK_node, atot6346, atot6361]
  decide +kernel

theorem arows6393 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6393 = true := by
  rw [show D2M8K2.u6393 = KTree.node D2M8K2.u6377 (nat_lit 13306682) (nat_lit 2947776661) (nat_lit 0) D2M8K2.u6392 from rfl, allE_node, arows6377, irow6393, arows6392]
  all_goals rfl

theorem atot6393 : totK PD2M8K2 D2M8K2.u6393 = [0, 1695647637035, 8145066702396, 12227201909389, 5643921539907, 702035805946, 18797058808, 0] := by
  rw [show D2M8K2.u6393 = KTree.node D2M8K2.u6377 (nat_lit 13306682) (nat_lit 2947776661) (nat_lit 0) D2M8K2.u6392 from rfl, totK_node, atot6377, atot6392]
  decide +kernel

theorem arows6427 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6427 = true := by
  rw [show D2M8K2.u6427 = KTree.node D2M8K2.u6411 (nat_lit 13388885) (nat_lit 2377552506) (nat_lit 0) D2M8K2.u6426 from rfl, allE_node, arows6411, irow6427, arows6426]
  all_goals rfl

theorem atot6427 : totK PD2M8K2 D2M8K2.u6427 = [0, 2138086297441, 9388865686618, 12184031042132, 4387792281567, 359900505272, 5883117146, 0] := by
  rw [show D2M8K2.u6427 = KTree.node D2M8K2.u6411 (nat_lit 13388885) (nat_lit 2377552506) (nat_lit 0) D2M8K2.u6426 from rfl, totK_node, atot6411, atot6426]
  decide +kernel

theorem arows6458 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6458 = true := by
  rw [show D2M8K2.u6458 = KTree.node D2M8K2.u6442 (nat_lit 13945969) (nat_lit 1531474698) (nat_lit 0) D2M8K2.u6457 from rfl, allE_node, arows6442, irow6458, arows6457]
  all_goals rfl

theorem atot6458 : totK PD2M8K2 D2M8K2.u6458 = [1973854997411, 8444839706029, 11580216769453, 5683949983202, 907765370093, 28580542600, 0, 0] := by
  rw [show D2M8K2.u6458 = KTree.node D2M8K2.u6442 (nat_lit 13945969) (nat_lit 1531474698) (nat_lit 0) D2M8K2.u6457 from rfl, totK_node, atot6442, atot6457]
  decide +kernel

theorem arows6490 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6490 = true := by
  rw [show D2M8K2.u6490 = KTree.node D2M8K2.u6474 (nat_lit 13987304) (nat_lit 3557639411) (nat_lit 0) D2M8K2.u6489 from rfl, allE_node, arows6474, irow6490, arows6489]
  all_goals rfl

theorem atot6490 : totK PD2M8K2 D2M8K2.u6490 = [1998065620822, 8847407893415, 12087837892759, 5225940304686, 765706454846, 36921873854, 0, 0] := by
  rw [show D2M8K2.u6490 = KTree.node D2M8K2.u6474 (nat_lit 13987304) (nat_lit 3557639411) (nat_lit 0) D2M8K2.u6489 from rfl, totK_node, atot6474, atot6489]
  decide +kernel

theorem arows6521 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6521 = true := by
  rw [show D2M8K2.u6521 = KTree.node D2M8K2.u6505 (nat_lit 14019257) (nat_lit 1516010659) (nat_lit 0) D2M8K2.u6520 from rfl, allE_node, arows6505, irow6521, arows6520]
  all_goals rfl

theorem atot6521 : totK PD2M8K2 D2M8K2.u6521 = [2036458072821, 8231667656687, 11339693424782, 6338954320032, 1021713534566, 21096254089, 0, 0] := by
  rw [show D2M8K2.u6521 = KTree.node D2M8K2.u6505 (nat_lit 14019257) (nat_lit 1516010659) (nat_lit 0) D2M8K2.u6520 from rfl, totK_node, atot6505, atot6520]
  decide +kernel

theorem arows6554 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6554 = true := by
  rw [show D2M8K2.u6554 = KTree.node D2M8K2.u6538 (nat_lit 14055934) (nat_lit 3809195105) (nat_lit 0) D2M8K2.u6553 from rfl, allE_node, arows6538, irow6554, arows6553]
  all_goals rfl

theorem atot6554 : totK PD2M8K2 D2M8K2.u6554 = [1651943885261, 7907734928410, 12167340954829, 6180976173973, 762191832237, 18797058808, 0, 0] := by
  rw [show D2M8K2.u6554 = KTree.node D2M8K2.u6538 (nat_lit 14055934) (nat_lit 3809195105) (nat_lit 0) D2M8K2.u6553 from rfl, totK_node, atot6538, atot6553]
  decide +kernel

theorem arows6585 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6585 = true := by
  rw [show D2M8K2.u6585 = KTree.node D2M8K2.u6569 (nat_lit 14101354) (nat_lit 3787308162) (nat_lit 0) D2M8K2.u6584 from rfl, allE_node, arows6569, irow6585, arows6584]
  all_goals rfl

theorem atot6585 : totK PD2M8K2 D2M8K2.u6585 = [1744533305976, 8122313080857, 12029034018430, 5889098385605, 740172396350, 19065934916, 0, 0] := by
  rw [show D2M8K2.u6585 = KTree.node D2M8K2.u6569 (nat_lit 14101354) (nat_lit 3787308162) (nat_lit 0) D2M8K2.u6584 from rfl, totK_node, atot6569, atot6584]
  decide +kernel

theorem arows6617 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6617 = true := by
  rw [show D2M8K2.u6617 = KTree.node D2M8K2.u6601 (nat_lit 14136301) (nat_lit 1127593384) (nat_lit 0) D2M8K2.u6616 from rfl, allE_node, arows6601, irow6617, arows6616]
  all_goals rfl

theorem atot6617 : totK PD2M8K2 D2M8K2.u6617 = [357800183586, 5105312178914, 12987930119116, 8793313770415, 1276015231042, 34748781128, 0, 0] := by
  rw [show D2M8K2.u6617 = KTree.node D2M8K2.u6601 (nat_lit 14136301) (nat_lit 1127593384) (nat_lit 0) D2M8K2.u6616 from rfl, totK_node, atot6601, atot6616]
  decide +kernel

theorem arows6648 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6648 = true := by
  rw [show D2M8K2.u6648 = KTree.node D2M8K2.u6632 (nat_lit 14229546) (nat_lit 3829457552) (nat_lit 0) D2M8K2.u6647 from rfl, allE_node, arows6632, irow6648, arows6647]
  all_goals rfl

theorem atot6648 : totK PD2M8K2 D2M8K2.u6648 = [0, 2231862597549, 9968213003713, 12458596371097, 3804311668403, 231827447631, 1209030869, 0] := by
  rw [show D2M8K2.u6648 = KTree.node D2M8K2.u6632 (nat_lit 14229546) (nat_lit 3829457552) (nat_lit 0) D2M8K2.u6647 from rfl, totK_node, atot6632, atot6647]
  decide +kernel

theorem arows6683 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6683 = true := by
  rw [show D2M8K2.u6683 = KTree.node D2M8K2.u6667 (nat_lit 14281392) (nat_lit 3515465258) (nat_lit 0) D2M8K2.u6682 from rfl, allE_node, arows6667, irow6683, arows6682]
  all_goals rfl

theorem atot6683 : totK PD2M8K2 D2M8K2.u6683 = [0, 3343170749262, 11926437904316, 11302987021599, 2320366518034, 66521436777, 0, 0] := by
  rw [show D2M8K2.u6683 = KTree.node D2M8K2.u6667 (nat_lit 14281392) (nat_lit 3515465258) (nat_lit 0) D2M8K2.u6682 from rfl, totK_node, atot6667, atot6682]
  decide +kernel

theorem arows6714 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6714 = true := by
  rw [show D2M8K2.u6714 = KTree.node D2M8K2.u6698 (nat_lit 14358537) (nat_lit 1794421657) (nat_lit 0) D2M8K2.u6713 from rfl, allE_node, arows6698, irow6714, arows6713]
  all_goals rfl

theorem atot6714 : totK PD2M8K2 D2M8K2.u6714 = [0, 2516699505921, 10229201347361, 11960761276610, 3545249197729, 229179999142, 1138244013, 0] := by
  rw [show D2M8K2.u6714 = KTree.node D2M8K2.u6698 (nat_lit 14358537) (nat_lit 1794421657) (nat_lit 0) D2M8K2.u6713 from rfl, totK_node, atot6698, atot6713]
  decide +kernel

theorem arows6746 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6746 = true := by
  rw [show D2M8K2.u6746 = KTree.node D2M8K2.u6730 (nat_lit 14444029) (nat_lit 1090264564) (nat_lit 0) D2M8K2.u6745 from rfl, allE_node, arows6730, irow6746, arows6745]
  all_goals rfl

theorem atot6746 : totK PD2M8K2 D2M8K2.u6746 = [1978604257116, 7944099100858, 10367725474741, 5926782860836, 2001625381813, 252792364780, 4977114383, 0] := by
  rw [show D2M8K2.u6746 = KTree.node D2M8K2.u6730 (nat_lit 14444029) (nat_lit 1090264564) (nat_lit 0) D2M8K2.u6745 from rfl, totK_node, atot6730, atot6745]
  decide +kernel

theorem arows6777 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6777 = true := by
  rw [show D2M8K2.u6777 = KTree.node D2M8K2.u6761 (nat_lit 14485225) (nat_lit 1421348092) (nat_lit 0) D2M8K2.u6776 from rfl, allE_node, arows6761, irow6777, arows6776]
  all_goals rfl

theorem atot6777 : totK PD2M8K2 D2M8K2.u6777 = [2003498705682, 8880121086237, 12111743193404, 5234639084026, 766462293630, 36921873854, 0, 0] := by
  rw [show D2M8K2.u6777 = KTree.node D2M8K2.u6761 (nat_lit 14485225) (nat_lit 1421348092) (nat_lit 0) D2M8K2.u6776 from rfl, totK_node, atot6761, atot6776]
  decide +kernel

theorem arows6810 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6810 = true := by
  rw [show D2M8K2.u6810 = KTree.node D2M8K2.u6794 (nat_lit 14517548) (nat_lit 3093399477) (nat_lit 0) D2M8K2.u6809 from rfl, allE_node, arows6794, irow6810, arows6809]
  all_goals rfl

theorem atot6810 : totK PD2M8K2 D2M8K2.u6810 = [2039724967466, 8287080030714, 11410747283645, 6259383898485, 1012719590345, 21096254089, 0, 0] := by
  rw [show D2M8K2.u6810 = KTree.node D2M8K2.u6794 (nat_lit 14517548) (nat_lit 3093399477) (nat_lit 0) D2M8K2.u6809 from rfl, totK_node, atot6794, atot6809]
  decide +kernel

theorem arows6841 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6841 = true := by
  rw [show D2M8K2.u6841 = KTree.node D2M8K2.u6825 (nat_lit 14554154) (nat_lit 4007700108) (nat_lit 0) D2M8K2.u6840 from rfl, allE_node, arows6825, irow6841, arows6840]
  all_goals rfl

theorem atot6841 : totK PD2M8K2 D2M8K2.u6841 = [1658021316512, 7919384354268, 12215363097728, 6199772340367, 762513226429, 18797058808, 0, 0] := by
  rw [show D2M8K2.u6841 = KTree.node D2M8K2.u6825 (nat_lit 14554154) (nat_lit 4007700108) (nat_lit 0) D2M8K2.u6840 from rfl, totK_node, atot6825, atot6840]
  decide +kernel

theorem arows6873 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6873 = true := by
  rw [show D2M8K2.u6873 = KTree.node D2M8K2.u6857 (nat_lit 14641413) (nat_lit 1402310722) (nat_lit 0) D2M8K2.u6872 from rfl, allE_node, arows6857, irow6873, arows6872]
  all_goals rfl

theorem atot6873 : totK PD2M8K2 D2M8K2.u6873 = [2017981443078, 8756468784350, 12002488197527, 5398875997868, 611852345647, 14345316470, 0, 0] := by
  rw [show D2M8K2.u6873 = KTree.node D2M8K2.u6857 (nat_lit 14641413) (nat_lit 1402310722) (nat_lit 0) D2M8K2.u6872 from rfl, totK_node, atot6857, atot6872]
  decide +kernel

theorem arows6904 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6904 = true := by
  rw [show D2M8K2.u6904 = KTree.node D2M8K2.u6888 (nat_lit 14673939) (nat_lit 3249589299) (nat_lit 0) D2M8K2.u6903 from rfl, allE_node, arows6888, irow6904, arows6903]
  all_goals rfl

theorem atot6904 : totK PD2M8K2 D2M8K2.u6904 = [93924006320, 4046709290529, 12562907379523, 10195239104029, 1712765134783, 44643596771, 0, 0] := by
  rw [show D2M8K2.u6904 = KTree.node D2M8K2.u6888 (nat_lit 14673939) (nat_lit 3249589299) (nat_lit 0) D2M8K2.u6903 from rfl, totK_node, atot6888, atot6903]
  decide +kernel

theorem arows6938 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6938 = true := by
  rw [show D2M8K2.u6938 = KTree.node D2M8K2.u6922 (nat_lit 14716604) (nat_lit 3394111771) (nat_lit 0) D2M8K2.u6937 from rfl, allE_node, arows6922, irow6938, arows6937]
  all_goals rfl

theorem atot6938 : totK PD2M8K2 D2M8K2.u6938 = [0, 2069539300890, 9238519036737, 12525543022899, 4491651485468, 272563518469, 1369150432, 0] := by
  rw [show D2M8K2.u6938 = KTree.node D2M8K2.u6922 (nat_lit 14716604) (nat_lit 3394111771) (nat_lit 0) D2M8K2.u6937 from rfl, totK_node, atot6922, atot6937]
  decide +kernel

theorem arows6969 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6969 = true := by
  rw [show D2M8K2.u6969 = KTree.node D2M8K2.u6953 (nat_lit 14771433) (nat_lit 1810823113) (nat_lit 0) D2M8K2.u6968 from rfl, allE_node, arows6953, irow6969, arows6968]
  all_goals rfl

theorem atot6969 : totK PD2M8K2 D2M8K2.u6969 = [0, 2705026550977, 10567962038138, 11801153190528, 3530738993918, 200085380734, 1166720416, 0] := by
  rw [show D2M8K2.u6969 = KTree.node D2M8K2.u6953 (nat_lit 14771433) (nat_lit 1810823113) (nat_lit 0) D2M8K2.u6968 from rfl, totK_node, atot6953, atot6968]
  decide +kernel

theorem arows7001 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7001 = true := by
  rw [show D2M8K2.u7001 = KTree.node D2M8K2.u6985 (nat_lit 14816021) (nat_lit 2047994065) (nat_lit 0) D2M8K2.u7000 from rfl, allE_node, arows6985, irow7001, arows7000]
  all_goals rfl

theorem atot7001 : totK PD2M8K2 D2M8K2.u7001 = [0, 1656673409961, 8301331757693, 12591225590514, 5517121955469, 501616169029, 7470648528, 0] := by
  rw [show D2M8K2.u7001 = KTree.node D2M8K2.u6985 (nat_lit 14816021) (nat_lit 2047994065) (nat_lit 0) D2M8K2.u7000 from rfl, totK_node, atot6985, atot7000]
  decide +kernel

theorem arows7032 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7032 = true := by
  rw [show D2M8K2.u7032 = KTree.node D2M8K2.u7016 (nat_lit 14898928) (nat_lit 2153611970) (nat_lit 0) D2M8K2.u7031 from rfl, allE_node, arows7016, irow7032, arows7031]
  all_goals rfl

theorem atot7032 : totK PD2M8K2 D2M8K2.u7032 = [0, 2110064696536, 9168108797409, 12161876542681, 4775438696002, 414317579604, 5316530232, 0] := by
  rw [show D2M8K2.u7032 = KTree.node D2M8K2.u7016 (nat_lit 14898928) (nat_lit 2153611970) (nat_lit 0) D2M8K2.u7031 from rfl, totK_node, atot7016, atot7031]
  decide +kernel

theorem arows7065 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7065 = true := by
  rw [show D2M8K2.u7065 = KTree.node D2M8K2.u7049 (nat_lit 14938650) (nat_lit 3405882195) (nat_lit 0) D2M8K2.u7064 from rfl, allE_node, arows7049, irow7065, arows7064]
  all_goals rfl

theorem atot7065 : totK PD2M8K2 D2M8K2.u7065 = [0, 2096993147398, 8687991278029, 11450034730972, 5333678883777, 841928136310, 31376465649, 0] := by
  rw [show D2M8K2.u7065 = KTree.node D2M8K2.u7049 (nat_lit 14938650) (nat_lit 3405882195) (nat_lit 0) D2M8K2.u7064 from rfl, totK_node, atot7049, atot7064]
  decide +kernel

theorem arows7096 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7096 = true := by
  rw [show D2M8K2.u7096 = KTree.node D2M8K2.u7080 (nat_lit 15017893) (nat_lit 1311703265) (nat_lit 0) D2M8K2.u7095 from rfl, allE_node, arows7080, irow7096, arows7095]
  all_goals rfl

theorem atot7096 : totK PD2M8K2 D2M8K2.u7096 = [0, 2034459393298, 9230901593610, 12535849910868, 4569921369929, 314916930109, 1369150432, 0] := by
  rw [show D2M8K2.u7096 = KTree.node D2M8K2.u7080 (nat_lit 15017893) (nat_lit 1311703265) (nat_lit 0) D2M8K2.u7095 from rfl, totK_node, atot7080, atot7095]
  decide +kernel

theorem arows7128 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7128 = true := by
  rw [show D2M8K2.u7128 = KTree.node D2M8K2.u7112 (nat_lit 15055942) (nat_lit 3483469637) (nat_lit 0) D2M8K2.u7127 from rfl, allE_node, arows7112, irow7128, arows7127]
  all_goals rfl

theorem atot7128 : totK PD2M8K2 D2M8K2.u7128 = [0, 1648442144398, 7958390600074, 12243451194637, 5963453094927, 728576416949, 18797058808, 0] := by
  rw [show D2M8K2.u7128 = KTree.node D2M8K2.u7112 (nat_lit 15055942) (nat_lit 3483469637) (nat_lit 0) D2M8K2.u7127 from rfl, totK_node, atot7112, atot7127]
  decide +kernel

theorem arows7159 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7159 = true := by
  rw [show D2M8K2.u7159 = KTree.node D2M8K2.u7143 (nat_lit 15103452) (nat_lit 3149023000) (nat_lit 0) D2M8K2.u7158 from rfl, allE_node, arows7143, irow7159, arows7158]
  all_goals rfl

theorem atot7159 : totK PD2M8K2 D2M8K2.u7159 = [0, 1977850742301, 9043301119171, 12480606613008, 4764682263712, 344429393027, 2378110086, 0] := by
  rw [show D2M8K2.u7159 = KTree.node D2M8K2.u7143 (nat_lit 15103452) (nat_lit 3149023000) (nat_lit 0) D2M8K2.u7158 from rfl, totK_node, atot7143, atot7158]
  decide +kernel

theorem arows7195 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7195 = true := by
  rw [show D2M8K2.u7195 = KTree.node D2M8K2.u7179 (nat_lit 15144682) (nat_lit 3919268871) (nat_lit 0) D2M8K2.u7194 from rfl, allE_node, arows7179, irow7195, arows7194]
  all_goals rfl

theorem atot7195 : totK PD2M8K2 D2M8K2.u7195 = [0, 1988996583632, 8824710212106, 12283788369217, 5157190815119, 471909671381, 6287399960, 0] := by
  rw [show D2M8K2.u7195 = KTree.node D2M8K2.u7179 (nat_lit 15144682) (nat_lit 3919268871) (nat_lit 0) D2M8K2.u7194 from rfl, totK_node, atot7179, atot7194]
  decide +kernel

theorem arows7226 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7226 = true := by
  rw [show D2M8K2.u7226 = KTree.node D2M8K2.u7210 (nat_lit 15186498) (nat_lit 1450346917) (nat_lit 0) D2M8K2.u7225 from rfl, allE_node, arows7210, irow7226, arows7225]
  all_goals rfl

theorem atot7226 : totK PD2M8K2 D2M8K2.u7226 = [0, 0, 3461719524390, 12094377766021, 10827468841042, 2033621548786, 71284412220, 0] := by
  rw [show D2M8K2.u7226 = KTree.node D2M8K2.u7210 (nat_lit 15186498) (nat_lit 1450346917) (nat_lit 0) D2M8K2.u7225 from rfl, totK_node, atot7210, atot7225]
  decide +kernel

theorem arows7258 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7258 = true := by
  rw [show D2M8K2.u7258 = KTree.node D2M8K2.u7242 (nat_lit 15269082) (nat_lit 2987560140) (nat_lit 128) D2M8K2.u7257 from rfl, allE_node, arows7242, irow7258, arows7257]
  all_goals rfl

theorem atot7258 : totK PD2M8K2 D2M8K2.u7258 = [0, 0, 2689678646797, 10768216828314, 11835155981481, 3045582170527, 193306051822, 1369150432] := by
  rw [show D2M8K2.u7258 = KTree.node D2M8K2.u7242 (nat_lit 15269082) (nat_lit 2987560140) (nat_lit 128) D2M8K2.u7257 from rfl, totK_node, atot7242, atot7257]
  decide +kernel

theorem arows7289 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7289 = true := by
  rw [show D2M8K2.u7289 = KTree.node D2M8K2.u7273 (nat_lit 15353909) (nat_lit 2404007425) (nat_lit 0) D2M8K2.u7288 from rfl, allE_node, arows7273, irow7289, arows7288]
  all_goals rfl

theorem atot7289 : totK PD2M8K2 D2M8K2.u7289 = [0, 0, 4096636157505, 13191322881760, 10056140668160, 1308400228898, 24406404928, 0] := by
  rw [show D2M8K2.u7289 = KTree.node D2M8K2.u7273 (nat_lit 15353909) (nat_lit 2404007425) (nat_lit 0) D2M8K2.u7288 from rfl, totK_node, atot7273, atot7288]
  decide +kernel

theorem arows7322 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7322 = true := by
  rw [show D2M8K2.u7322 = KTree.node D2M8K2.u7306 (nat_lit 15478953) (nat_lit 1918752217) (nat_lit 0) D2M8K2.u7321 from rfl, allE_node, arows7306, irow7322, arows7321]
  all_goals rfl

theorem atot7322 : totK PD2M8K2 D2M8K2.u7322 = [0, 2117708296215, 8811956707574, 11724612881366, 5548664764085, 846167423701, 40388354358, 0] := by
  rw [show D2M8K2.u7322 = KTree.node D2M8K2.u7306 (nat_lit 15478953) (nat_lit 1918752217) (nat_lit 0) D2M8K2.u7321 from rfl, totK_node, atot7306, atot7321]
  decide +kernel

theorem arows7353 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7353 = true := by
  rw [show D2M8K2.u7353 = KTree.node D2M8K2.u7337 (nat_lit 15509694) (nat_lit 3948791991) (nat_lit 0) D2M8K2.u7352 from rfl, allE_node, arows7337, irow7353, arows7352]
  all_goals rfl

theorem atot7353 : totK PD2M8K2 D2M8K2.u7353 = [0, 1625231011170, 7275007514639, 11393620036256, 7247288032851, 1362194878176, 36632523021, 0] := by
  rw [show D2M8K2.u7353 = KTree.node D2M8K2.u7337 (nat_lit 15509694) (nat_lit 3948791991) (nat_lit 0) D2M8K2.u7352 from rfl, totK_node, atot7337, atot7352]
  decide +kernel

theorem arows7385 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7385 = true := by
  rw [show D2M8K2.u7385 = KTree.node D2M8K2.u7369 (nat_lit 15547209) (nat_lit 1905615121) (nat_lit 0) D2M8K2.u7384 from rfl, allE_node, arows7369, irow7385, arows7384]
  all_goals rfl

theorem atot7385 : totK PD2M8K2 D2M8K2.u7385 = [0, 1741668805004, 8305375014658, 12368230113274, 5724011929952, 670150365481, 17590593026, 0] := by
  rw [show D2M8K2.u7385 = KTree.node D2M8K2.u7369 (nat_lit 15547209) (nat_lit 1905615121) (nat_lit 0) D2M8K2.u7384 from rfl, totK_node, atot7369, atot7384]
  decide +kernel

theorem arows7416 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7416 = true := by
  rw [show D2M8K2.u7416 = KTree.node D2M8K2.u7400 (nat_lit 15593629) (nat_lit 1369820453) (nat_lit 0) D2M8K2.u7415 from rfl, allE_node, arows7400, irow7416, arows7415]
  all_goals rfl

theorem atot7416 : totK PD2M8K2 D2M8K2.u7416 = [0, 2059526897782, 8890042908728, 12095300427688, 5314459414577, 526043187456, 7133208874, 0] := by
  rw [show D2M8K2.u7416 = KTree.node D2M8K2.u7400 (nat_lit 15593629) (nat_lit 1369820453) (nat_lit 0) D2M8K2.u7415 from rfl, totK_node, atot7400, atot7415]
  decide +kernel

theorem arows7450 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7450 = true := by
  rw [show D2M8K2.u7450 = KTree.node D2M8K2.u7434 (nat_lit 15635664) (nat_lit 3691793810) (nat_lit 0) D2M8K2.u7449 from rfl, allE_node, arows7434, irow7450, arows7449]
  all_goals rfl

theorem atot7450 : totK PD2M8K2 D2M8K2.u7450 = [0, 2084767171607, 9238962860952, 12415003510828, 4765468330880, 403383330449, 4977114383, 0] := by
  rw [show D2M8K2.u7450 = KTree.node D2M8K2.u7434 (nat_lit 15635664) (nat_lit 3691793810) (nat_lit 0) D2M8K2.u7449 from rfl, totK_node, atot7434, atot7449]
  decide +kernel

theorem arows7481 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7481 = true := by
  rw [show D2M8K2.u7481 = KTree.node D2M8K2.u7465 (nat_lit 15673301) (nat_lit 2373890930) (nat_lit 0) D2M8K2.u7480 from rfl, allE_node, arows7465, irow7481, arows7480]
  all_goals rfl

theorem atot7481 : totK PD2M8K2 D2M8K2.u7481 = [0, 1605538724154, 7671721824004, 11974291546152, 6586079067353, 954511214656, 25648839374, 0] := by
  rw [show D2M8K2.u7481 = KTree.node D2M8K2.u7465 (nat_lit 15673301) (nat_lit 2373890930) (nat_lit 0) D2M8K2.u7480 from rfl, totK_node, atot7465, atot7480]
  decide +kernel

theorem arows7513 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7513 = true := by
  rw [show D2M8K2.u7513 = KTree.node D2M8K2.u7497 (nat_lit 15960712) (nat_lit 2482525396) (nat_lit 0) D2M8K2.u7512 from rfl, allE_node, arows7497, irow7513, arows7512]
  all_goals rfl

theorem atot7513 : totK PD2M8K2 D2M8K2.u7513 = [0, 1936782422109, 9058502179031, 12705899695672, 4715528056686, 299237364682, 1369150432, 0] := by
  rw [show D2M8K2.u7513 = KTree.node D2M8K2.u7497 (nat_lit 15960712) (nat_lit 2482525396) (nat_lit 0) D2M8K2.u7512 from rfl, totK_node, atot7497, atot7512]
  decide +kernel

theorem arows7544 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7544 = true := by
  rw [show D2M8K2.u7544 = KTree.node D2M8K2.u7528 (nat_lit 15998254) (nat_lit 4014667683) (nat_lit 0) D2M8K2.u7543 from rfl, allE_node, arows7528, irow7544, arows7543]
  all_goals rfl

theorem atot7544 : totK PD2M8K2 D2M8K2.u7544 = [0, 1515594330374, 7344193996254, 11847976547356, 7053392186794, 1201159419423, 36367404465, 0] := by
  rw [show D2M8K2.u7544 = KTree.node D2M8K2.u7528 (nat_lit 15998254) (nat_lit 4014667683) (nat_lit 0) D2M8K2.u7543 from rfl, totK_node, atot7528, atot7543]
  decide +kernel

theorem arows7577 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7577 = true := by
  rw [show D2M8K2.u7577 = KTree.node D2M8K2.u7561 (nat_lit 16030570) (nat_lit 3958804250) (nat_lit 0) D2M8K2.u7576 from rfl, allE_node, arows7561, irow7577, arows7576]
  all_goals rfl

theorem atot7577 : totK PD2M8K2 D2M8K2.u7577 = [0, 1695988616655, 7928982015269, 12188615841977, 6095174999534, 737420890877, 18797058808, 0] := by
  rw [show D2M8K2.u7577 = KTree.node D2M8K2.u7561 (nat_lit 16030570) (nat_lit 3958804250) (nat_lit 0) D2M8K2.u7576 from rfl, totK_node, atot7561, atot7576]
  decide +kernel

theorem arows7608 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7608 = true := by
  rw [show D2M8K2.u7608 = KTree.node D2M8K2.u7592 (nat_lit 16106839) (nat_lit 2056241384) (nat_lit 0) D2M8K2.u7607 from rfl, allE_node, arows7592, irow7608, arows7607]
  all_goals rfl

theorem atot7608 : totK PD2M8K2 D2M8K2.u7608 = [0, 1857984025863, 8758560231933, 12503676990059, 5097211652535, 429881319428, 6115358396, 0] := by
  rw [show D2M8K2.u7608 = KTree.node D2M8K2.u7592 (nat_lit 16106839) (nat_lit 2056241384) (nat_lit 0) D2M8K2.u7607 from rfl, totK_node, atot7592, atot7607]
  decide +kernel

theorem arows7640 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7640 = true := by
  rw [show D2M8K2.u7640 = KTree.node D2M8K2.u7624 (nat_lit 16150889) (nat_lit 1477639229) (nat_lit 0) D2M8K2.u7639 from rfl, allE_node, arows7624, irow7640, arows7639]
  all_goals rfl

theorem atot7640 : totK PD2M8K2 D2M8K2.u7640 = [0, 1769564901391, 8514050145946, 12523813497294, 5588478634322, 512412068121, 6190125969, 0] := by
  rw [show D2M8K2.u7640 = KTree.node D2M8K2.u7624 (nat_lit 16150889) (nat_lit 1477639229) (nat_lit 0) D2M8K2.u7639 from rfl, totK_node, atot7624, atot7639]
  decide +kernel

theorem arows7671 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7671 = true := by
  rw [show D2M8K2.u7671 = KTree.node D2M8K2.u7655 (nat_lit 16190266) (nat_lit 3680527205) (nat_lit 0) D2M8K2.u7670 from rfl, allE_node, arows7655, irow7671, arows7670]
  all_goals rfl

theorem atot7671 : totK PD2M8K2 D2M8K2.u7671 = [0, 0, 2184681532092, 9973722471250, 12314979935725, 3599091434120, 223104336344, 1275377855] := by
  rw [show D2M8K2.u7671 = KTree.node D2M8K2.u7655 (nat_lit 16190266) (nat_lit 3680527205) (nat_lit 0) D2M8K2.u7670 from rfl, totK_node, atot7655, atot7670]
  decide +kernel

end QECKChecks.D2M8K2
