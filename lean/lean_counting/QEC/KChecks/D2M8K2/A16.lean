import QEC.Count.ChunksK3
import QEC.KChecks.D2M8K2.A15

namespace QECKChecks.D2M8K2

open QEC QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem arows5631 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5631 = true := by
  rw [show D2M8K2.u5631 = KTree.node D2M8K2.u5629 (nat_lit 12145543) (nat_lit 2349187145) (nat_lit 0) D2M8K2.u5630 from rfl, allE_node, arows5629, irow5631, arows5630]
  all_goals rfl

theorem atot5631 : totK PD2M8K2 D2M8K2.u5631 = [0, 432892715274, 1555313540674, 1314080517404, 208152960746, 2162517376, 0, 0] := by
  rw [show D2M8K2.u5631 = KTree.node D2M8K2.u5629 (nat_lit 12145543) (nat_lit 2349187145) (nat_lit 0) D2M8K2.u5630 from rfl, totK_node, atot5629, atot5630]
  decide +kernel

theorem arows5634 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5634 = true := by
  rw [show D2M8K2.u5634 = KTree.node D2M8K2.u5632 (nat_lit 12152816) (nat_lit 2834341603) (nat_lit 0) D2M8K2.u5633 from rfl, allE_node, arows5632, irow5634, arows5633]
  all_goals rfl

theorem atot5634 : totK PD2M8K2 D2M8K2.u5634 = [500825967538, 1605511779018, 1287423167626, 181000393908, 20618967235, 2814597007, 0, 0] := by
  rw [show D2M8K2.u5634 = KTree.node D2M8K2.u5632 (nat_lit 12152816) (nat_lit 2834341603) (nat_lit 0) D2M8K2.u5633 from rfl, totK_node, atot5632, atot5633]
  decide +kernel

theorem arows5638 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5638 = true := by
  rw [show D2M8K2.u5638 = KTree.node D2M8K2.u5636 (nat_lit 12156963) (nat_lit 3687294742) (nat_lit 0) D2M8K2.u5637 from rfl, allE_node, arows5636, irow5638, arows5637]
  all_goals rfl

theorem atot5638 : totK PD2M8K2 D2M8K2.u5638 = [370572661339, 1342176326273, 1423944559405, 492479789464, 34833699740, 0, 0, 0] := by
  rw [show D2M8K2.u5638 = KTree.node D2M8K2.u5636 (nat_lit 12156963) (nat_lit 3687294742) (nat_lit 0) D2M8K2.u5637 from rfl, totK_node, atot5636, atot5637]
  decide +kernel

theorem arows5641 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5641 = true := by
  rw [show D2M8K2.u5641 = KTree.node D2M8K2.u5639 (nat_lit 12160070) (nat_lit 3184491031) (nat_lit 0) D2M8K2.u5640 from rfl, allE_node, arows5639, irow5641, arows5640]
  all_goals rfl

theorem atot5641 : totK PD2M8K2 D2M8K2.u5641 = [395436999813, 1430119321059, 1437724371248, 332345522683, 13043783340, 0, 0, 0] := by
  rw [show D2M8K2.u5641 = KTree.node D2M8K2.u5639 (nat_lit 12160070) (nat_lit 3184491031) (nat_lit 0) D2M8K2.u5640 from rfl, totK_node, atot5639, atot5640]
  decide +kernel

theorem arows5646 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5646 = true := by
  rw [show D2M8K2.u5646 = KTree.node D2M8K2.u5644 (nat_lit 12163592) (nat_lit 2563632270) (nat_lit 0) D2M8K2.u5645 from rfl, allE_node, arows5644, irow5646, arows5645]
  all_goals rfl

theorem atot5646 : totK PD2M8K2 D2M8K2.u5646 = [431654433787, 1460848131172, 1362879106603, 326502877214, 13243784863, 0, 0, 0] := by
  rw [show D2M8K2.u5646 = KTree.node D2M8K2.u5644 (nat_lit 12163592) (nat_lit 2563632270) (nat_lit 0) D2M8K2.u5645 from rfl, totK_node, atot5644, atot5645]
  decide +kernel

theorem arows5649 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5649 = true := by
  rw [show D2M8K2.u5649 = KTree.node D2M8K2.u5647 (nat_lit 12170424) (nat_lit 3631534234) (nat_lit 0) D2M8K2.u5648 from rfl, allE_node, arows5647, irow5649, arows5648]
  all_goals rfl

theorem atot5649 : totK PD2M8K2 D2M8K2.u5649 = [283591591116, 1275320242596, 1572029389804, 455297478844, 22048779143, 0, 0, 0] := by
  rw [show D2M8K2.u5649 = KTree.node D2M8K2.u5647 (nat_lit 12170424) (nat_lit 3631534234) (nat_lit 0) D2M8K2.u5648 from rfl, totK_node, atot5647, atot5648]
  decide +kernel

theorem arows5653 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5653 = true := by
  rw [show D2M8K2.u5653 = KTree.node D2M8K2.u5651 (nat_lit 12173672) (nat_lit 2569045794) (nat_lit 0) D2M8K2.u5652 from rfl, allE_node, arows5651, irow5653, arows5652]
  all_goals rfl

theorem atot5653 : totK PD2M8K2 D2M8K2.u5653 = [0, 470343830988, 1641923582432, 1301466945514, 148551117009, 1310285577, 0, 0] := by
  rw [show D2M8K2.u5653 = KTree.node D2M8K2.u5651 (nat_lit 12173672) (nat_lit 2569045794) (nat_lit 0) D2M8K2.u5652 from rfl, totK_node, atot5651, atot5652]
  decide +kernel

theorem arows5656 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5656 = true := by
  rw [show D2M8K2.u5656 = KTree.node D2M8K2.u5654 (nat_lit 12179330) (nat_lit 3994939773) (nat_lit 0) D2M8K2.u5655 from rfl, allE_node, arows5654, irow5656, arows5655]
  all_goals rfl

theorem atot5656 : totK PD2M8K2 D2M8K2.u5656 = [0, 655914022313, 1784491239070, 1082067394979, 102498550421, 1075657031, 0, 0] := by
  rw [show D2M8K2.u5656 = KTree.node D2M8K2.u5654 (nat_lit 12179330) (nat_lit 3994939773) (nat_lit 0) D2M8K2.u5655 from rfl, totK_node, atot5654, atot5655]
  decide +kernel

theorem arows5662 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5662 = true := by
  rw [show D2M8K2.u5662 = KTree.node D2M8K2.u5660 (nat_lit 12182959) (nat_lit 2225277628) (nat_lit 0) D2M8K2.u5661 from rfl, allE_node, arows5660, irow5662, arows5661]
  all_goals rfl

theorem atot5662 : totK PD2M8K2 D2M8K2.u5662 = [0, 380639856186, 1475957088329, 1442068048280, 251070192774, 4911340522, 0, 0] := by
  rw [show D2M8K2.u5662 = KTree.node D2M8K2.u5660 (nat_lit 12182959) (nat_lit 2225277628) (nat_lit 0) D2M8K2.u5661 from rfl, totK_node, atot5660, atot5661]
  decide +kernel

theorem arows5665 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5665 = true := by
  rw [show D2M8K2.u5665 = KTree.node D2M8K2.u5663 (nat_lit 12190043) (nat_lit 2361985304) (nat_lit 0) D2M8K2.u5664 from rfl, allE_node, arows5663, irow5665, arows5664]
  all_goals rfl

theorem atot5665 : totK PD2M8K2 D2M8K2.u5665 = [0, 438094525316, 1533747907374, 1363041969764, 243553273994, 5066386085, 0, 0] := by
  rw [show D2M8K2.u5665 = KTree.node D2M8K2.u5663 (nat_lit 12190043) (nat_lit 2361985304) (nat_lit 0) D2M8K2.u5664 from rfl, totK_node, atot5663, atot5664]
  decide +kernel

theorem arows5669 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5669 = true := by
  rw [show D2M8K2.u5669 = KTree.node D2M8K2.u5667 (nat_lit 12193515) (nat_lit 2553553077) (nat_lit 0) D2M8K2.u5668 from rfl, allE_node, arows5667, irow5669, arows5668]
  all_goals rfl

theorem atot5669 : totK PD2M8K2 D2M8K2.u5669 = [0, 441412314152, 1423112761021, 1299838690152, 372267097400, 21878179898, 0, 0] := by
  rw [show D2M8K2.u5669 = KTree.node D2M8K2.u5667 (nat_lit 12193515) (nat_lit 2553553077) (nat_lit 0) D2M8K2.u5668 from rfl, totK_node, atot5667, atot5668]
  decide +kernel

theorem arows5672 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5672 = true := by
  rw [show D2M8K2.u5672 = KTree.node D2M8K2.u5670 (nat_lit 12200294) (nat_lit 3901195954) (nat_lit 0) D2M8K2.u5671 from rfl, allE_node, arows5670, irow5672, arows5671]
  all_goals rfl

theorem atot5672 : totK PD2M8K2 D2M8K2.u5672 = [0, 418417329849, 1572350028706, 1428300236528, 190699804021, 1164319620, 0, 0] := by
  rw [show D2M8K2.u5672 = KTree.node D2M8K2.u5670 (nat_lit 12200294) (nat_lit 3901195954) (nat_lit 0) D2M8K2.u5671 from rfl, totK_node, atot5670, atot5671]
  decide +kernel

theorem arows5677 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5677 = true := by
  rw [show D2M8K2.u5677 = KTree.node D2M8K2.u5675 (nat_lit 12204038) (nat_lit 3420113547) (nat_lit 0) D2M8K2.u5676 from rfl, allE_node, arows5675, irow5677, arows5676]
  all_goals rfl

theorem atot5677 : totK PD2M8K2 D2M8K2.u5677 = [0, 398026915003, 1427376194868, 1391267778414, 290200814932, 12925411781, 0, 0] := by
  rw [show D2M8K2.u5677 = KTree.node D2M8K2.u5675 (nat_lit 12204038) (nat_lit 3420113547) (nat_lit 0) D2M8K2.u5676 from rfl, totK_node, atot5675, atot5676]
  decide +kernel

theorem arows5680 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5680 = true := by
  rw [show D2M8K2.u5680 = KTree.node D2M8K2.u5678 (nat_lit 12207180) (nat_lit 3550057930) (nat_lit 0) D2M8K2.u5679 from rfl, allE_node, arows5678, irow5680, arows5679]
  all_goals rfl

theorem atot5680 : totK PD2M8K2 D2M8K2.u5680 = [0, 412010308217, 1438418927777, 1361967487879, 282214645273, 12990811517, 0, 0] := by
  rw [show D2M8K2.u5680 = KTree.node D2M8K2.u5678 (nat_lit 12207180) (nat_lit 3550057930) (nat_lit 0) D2M8K2.u5679 from rfl, totK_node, atot5678, atot5679]
  decide +kernel

theorem arows5684 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5684 = true := by
  rw [show D2M8K2.u5684 = KTree.node D2M8K2.u5682 (nat_lit 12210725) (nat_lit 2329682462) (nat_lit 0) D2M8K2.u5683 from rfl, allE_node, arows5682, irow5684, arows5683]
  all_goals rfl

theorem atot5684 : totK PD2M8K2 D2M8K2.u5684 = [0, 417509408390, 1505652918640, 1406798626713, 239589769614, 5106765734, 0, 0] := by
  rw [show D2M8K2.u5684 = KTree.node D2M8K2.u5682 (nat_lit 12210725) (nat_lit 2329682462) (nat_lit 0) D2M8K2.u5683 from rfl, totK_node, atot5682, atot5683]
  decide +kernel

theorem arows5687 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5687 = true := by
  rw [show D2M8K2.u5687 = KTree.node D2M8K2.u5685 (nat_lit 12214207) (nat_lit 1696719277) (nat_lit 0) D2M8K2.u5686 from rfl, allE_node, arows5685, irow5687, arows5686]
  all_goals rfl

theorem atot5687 : totK PD2M8K2 D2M8K2.u5687 = [0, 0, 665204462132, 1786603468095, 926634491517, 102489850969, 1369150432, 0] := by
  rw [show D2M8K2.u5687 = KTree.node D2M8K2.u5685 (nat_lit 12214207) (nat_lit 1696719277) (nat_lit 0) D2M8K2.u5686 from rfl, totK_node, atot5685, atot5686]
  decide +kernel

theorem arows5694 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5694 = true := by
  rw [show D2M8K2.u5694 = KTree.node D2M8K2.u5692 (nat_lit 12221148) (nat_lit 3149023000) (nat_lit 0) D2M8K2.u5693 from rfl, allE_node, arows5692, irow5694, arows5693]
  all_goals rfl

theorem atot5694 : totK PD2M8K2 D2M8K2.u5694 = [0, 0, 640347839223, 1764918138081, 986232330828, 107171504114, 0, 0] := by
  rw [show D2M8K2.u5694 = KTree.node D2M8K2.u5692 (nat_lit 12221148) (nat_lit 3149023000) (nat_lit 0) D2M8K2.u5693 from rfl, totK_node, atot5692, atot5693]
  decide +kernel

theorem arows5697 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5697 = true := by
  rw [show D2M8K2.u5697 = KTree.node D2M8K2.u5695 (nat_lit 12228060) (nat_lit 3141604827) (nat_lit 0) D2M8K2.u5696 from rfl, allE_node, arows5695, irow5697, arows5696]
  all_goals rfl

theorem atot5697 : totK PD2M8K2 D2M8K2.u5697 = [0, 0, 811932235776, 1903000958925, 730670405030, 42909584918, 0, 0] := by
  rw [show D2M8K2.u5697 = KTree.node D2M8K2.u5695 (nat_lit 12228060) (nat_lit 3141604827) (nat_lit 0) D2M8K2.u5696 from rfl, totK_node, atot5695, atot5696]
  decide +kernel

theorem arows5701 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5701 = true := by
  rw [show D2M8K2.u5701 = KTree.node D2M8K2.u5699 (nat_lit 12276533) (nat_lit 2308593483) (nat_lit 0) D2M8K2.u5700 from rfl, allE_node, arows5699, irow5701, arows5700]
  all_goals rfl

theorem atot5701 : totK PD2M8K2 D2M8K2.u5701 = [0, 419705733002, 1384098155587, 1330159833014, 386472765393, 22424464014, 0, 0] := by
  rw [show D2M8K2.u5701 = KTree.node D2M8K2.u5699 (nat_lit 12276533) (nat_lit 2308593483) (nat_lit 0) D2M8K2.u5700 from rfl, totK_node, atot5699, atot5700]
  decide +kernel

theorem arows5704 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5704 = true := by
  rw [show D2M8K2.u5704 = KTree.node D2M8K2.u5702 (nat_lit 12280372) (nat_lit 3986255077) (nat_lit 0) D2M8K2.u5703 from rfl, allE_node, arows5702, irow5704, arows5703]
  all_goals rfl

theorem atot5704 : totK PD2M8K2 D2M8K2.u5704 = [0, 346403488510, 1456382895550, 1557922459938, 287237351792, 5284349065, 0, 0] := by
  rw [show D2M8K2.u5704 = KTree.node D2M8K2.u5702 (nat_lit 12280372) (nat_lit 3986255077) (nat_lit 0) D2M8K2.u5703 from rfl, totK_node, atot5702, atot5703]
  decide +kernel

theorem arows5709 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5709 = true := by
  rw [show D2M8K2.u5709 = KTree.node D2M8K2.u5707 (nat_lit 12283992) (nat_lit 3216797280) (nat_lit 0) D2M8K2.u5708 from rfl, allE_node, arows5707, irow5709, arows5708]
  all_goals rfl

theorem atot5709 : totK PD2M8K2 D2M8K2.u5709 = [0, 440127250691, 1525430767710, 1397226084482, 268812022545, 9587713104, 0, 0] := by
  rw [show D2M8K2.u5709 = KTree.node D2M8K2.u5707 (nat_lit 12283992) (nat_lit 3216797280) (nat_lit 0) D2M8K2.u5708 from rfl, totK_node, atot5707, atot5708]
  decide +kernel

theorem arows5712 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5712 = true := by
  rw [show D2M8K2.u5712 = KTree.node D2M8K2.u5710 (nat_lit 12290502) (nat_lit 3848372517) (nat_lit 0) D2M8K2.u5711 from rfl, allE_node, arows5710, irow5712, arows5711]
  all_goals rfl

theorem atot5712 : totK PD2M8K2 D2M8K2.u5712 = [0, 408904915938, 1514550829781, 1418201509138, 228752876790, 4558519234, 0, 0] := by
  rw [show D2M8K2.u5712 = KTree.node D2M8K2.u5710 (nat_lit 12290502) (nat_lit 3848372517) (nat_lit 0) D2M8K2.u5711 from rfl, totK_node, atot5710, atot5711]
  decide +kernel

theorem arows5716 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5716 = true := by
  rw [show D2M8K2.u5716 = KTree.node D2M8K2.u5714 (nat_lit 12294127) (nat_lit 2273201905) (nat_lit 0) D2M8K2.u5715 from rfl, allE_node, arows5714, irow5716, arows5715]
  all_goals rfl

theorem atot5716 : totK PD2M8K2 D2M8K2.u5716 = [0, 414418486330, 1456996975894, 1420908006063, 309781666675, 8752419278, 0, 0] := by
  rw [show D2M8K2.u5716 = KTree.node D2M8K2.u5714 (nat_lit 12294127) (nat_lit 2273201905) (nat_lit 0) D2M8K2.u5715 from rfl, totK_node, atot5714, atot5715]
  decide +kernel

theorem arows5719 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5719 = true := by
  rw [show D2M8K2.u5719 = KTree.node D2M8K2.u5717 (nat_lit 12318507) (nat_lit 2876933863) (nat_lit 0) D2M8K2.u5718 from rfl, allE_node, arows5717, irow5719, arows5718]
  all_goals rfl

theorem atot5719 : totK PD2M8K2 D2M8K2.u5719 = [0, 418938605982, 1497641769077, 1369975719391, 262229840700, 10121797714, 0, 0] := by
  rw [show D2M8K2.u5719 = KTree.node D2M8K2.u5717 (nat_lit 12318507) (nat_lit 2876933863) (nat_lit 0) D2M8K2.u5718 from rfl, totK_node, atot5717, atot5718]
  decide +kernel

theorem arows5725 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5725 = true := by
  rw [show D2M8K2.u5725 = KTree.node D2M8K2.u5723 (nat_lit 12329032) (nat_lit 2910678018) (nat_lit 0) D2M8K2.u5724 from rfl, allE_node, arows5723, irow5725, arows5724]
  all_goals rfl

theorem atot5725 : totK PD2M8K2 D2M8K2.u5725 = [0, 425083345834, 1449588072073, 1378717511976, 322368126268, 13170675918, 0, 0] := by
  rw [show D2M8K2.u5725 = KTree.node D2M8K2.u5723 (nat_lit 12329032) (nat_lit 2910678018) (nat_lit 0) D2M8K2.u5724 from rfl, totK_node, atot5723, atot5724]
  decide +kernel

theorem arows5728 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5728 = true := by
  rw [show D2M8K2.u5728 = KTree.node D2M8K2.u5726 (nat_lit 12332170) (nat_lit 2802701296) (nat_lit 0) D2M8K2.u5727 from rfl, allE_node, arows5726, irow5728, arows5727]
  all_goals rfl

theorem atot5728 : totK PD2M8K2 D2M8K2.u5728 = [0, 415454967738, 1496010186740, 1412964374523, 238739901152, 4917684815, 0, 0] := by
  rw [show D2M8K2.u5728 = KTree.node D2M8K2.u5726 (nat_lit 12332170) (nat_lit 2802701296) (nat_lit 0) D2M8K2.u5727 from rfl, totK_node, atot5726, atot5727]
  decide +kernel

theorem arows5732 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5732 = true := by
  rw [show D2M8K2.u5732 = KTree.node D2M8K2.u5730 (nat_lit 12336068) (nat_lit 1986162019) (nat_lit 0) D2M8K2.u5731 from rfl, allE_node, arows5730, irow5732, arows5731]
  all_goals rfl

theorem atot5732 : totK PD2M8K2 D2M8K2.u5732 = [0, 395565363948, 1421588191403, 1431716723684, 340743394701, 13714665880, 0, 0] := by
  rw [show D2M8K2.u5732 = KTree.node D2M8K2.u5730 (nat_lit 12336068) (nat_lit 1986162019) (nat_lit 0) D2M8K2.u5731 from rfl, totK_node, atot5730, atot5731]
  decide +kernel

theorem arows5735 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5735 = true := by
  rw [show D2M8K2.u5735 = KTree.node D2M8K2.u5733 (nat_lit 12360188) (nat_lit 2595692338) (nat_lit 0) D2M8K2.u5734 from rfl, allE_node, arows5733, irow5735, arows5734]
  all_goals rfl

theorem atot5735 : totK PD2M8K2 D2M8K2.u5735 = [0, 491015990429, 1620671204895, 1280622282702, 173798299299, 1369150432, 0, 0] := by
  rw [show D2M8K2.u5735 = KTree.node D2M8K2.u5733 (nat_lit 12360188) (nat_lit 2595692338) (nat_lit 0) D2M8K2.u5734 from rfl, totK_node, atot5733, atot5734]
  decide +kernel

theorem arows5740 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5740 = true := by
  rw [show D2M8K2.u5740 = KTree.node D2M8K2.u5738 (nat_lit 12364521) (nat_lit 1893558233) (nat_lit 0) D2M8K2.u5739 from rfl, allE_node, arows5738, irow5740, arows5739]
  all_goals rfl

theorem atot5740 : totK PD2M8K2 D2M8K2.u5740 = [0, 496529238396, 1621576405284, 1331215606243, 197451023363, 1409560813, 0, 0] := by
  rw [show D2M8K2.u5740 = KTree.node D2M8K2.u5738 (nat_lit 12364521) (nat_lit 1893558233) (nat_lit 0) D2M8K2.u5739 from rfl, totK_node, atot5738, atot5739]
  decide +kernel

theorem arows5743 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5743 = true := by
  rw [show D2M8K2.u5743 = KTree.node D2M8K2.u5741 (nat_lit 12368078) (nat_lit 2464700975) (nat_lit 0) D2M8K2.u5742 from rfl, allE_node, arows5741, irow5743, arows5742]
  all_goals rfl

theorem atot5743 : totK PD2M8K2 D2M8K2.u5743 = [0, 396245434285, 1434600447747, 1418630632520, 305255989208, 12983449796, 0, 0] := by
  rw [show D2M8K2.u5743 = KTree.node D2M8K2.u5741 (nat_lit 12368078) (nat_lit 2464700975) (nat_lit 0) D2M8K2.u5742 from rfl, totK_node, atot5741, atot5742]
  decide +kernel

theorem arows5747 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5747 = true := by
  rw [show D2M8K2.u5747 = KTree.node D2M8K2.u5745 (nat_lit 12371935) (nat_lit 2341993973) (nat_lit 0) D2M8K2.u5746 from rfl, allE_node, arows5745, irow5747, arows5746]
  all_goals rfl

theorem atot5747 : totK PD2M8K2 D2M8K2.u5747 = [0, 414816586805, 1430385676854, 1385932020027, 305938400223, 13184317400, 0, 0] := by
  rw [show D2M8K2.u5747 = KTree.node D2M8K2.u5745 (nat_lit 12371935) (nat_lit 2341993973) (nat_lit 0) D2M8K2.u5746 from rfl, totK_node, atot5745, atot5746]
  decide +kernel

theorem arows5750 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5750 = true := by
  rw [show D2M8K2.u5750 = KTree.node D2M8K2.u5748 (nat_lit 12375173) (nat_lit 2023104873) (nat_lit 0) D2M8K2.u5749 from rfl, allE_node, arows5748, irow5750, arows5749]
  all_goals rfl

theorem atot5750 : totK PD2M8K2 D2M8K2.u5750 = [0, 437945110068, 1549488572784, 1356868745374, 228295903863, 4980514959, 0, 0] := by
  rw [show D2M8K2.u5750 = KTree.node D2M8K2.u5748 (nat_lit 12375173) (nat_lit 2023104873) (nat_lit 0) D2M8K2.u5749 from rfl, totK_node, atot5748, atot5749]
  decide +kernel

theorem arows5758 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5758 = true := by
  rw [show D2M8K2.u5758 = KTree.node D2M8K2.u5756 (nat_lit 12403124) (nat_lit 3545601958) (nat_lit 0) D2M8K2.u5757 from rfl, allE_node, arows5756, irow5758, arows5757]
  all_goals rfl

theorem atot5758 : totK PD2M8K2 D2M8K2.u5758 = [0, 473002628091, 1600915568515, 1375439730251, 190857449020, 1369150432, 0, 0] := by
  rw [show D2M8K2.u5758 = KTree.node D2M8K2.u5756 (nat_lit 12403124) (nat_lit 3545601958) (nat_lit 0) D2M8K2.u5757 from rfl, totK_node, atot5756, atot5757]
  decide +kernel

theorem arows5761 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5761 = true := by
  rw [show D2M8K2.u5761 = KTree.node D2M8K2.u5759 (nat_lit 12407262) (nat_lit 3778626699) (nat_lit 0) D2M8K2.u5760 from rfl, allE_node, arows5759, irow5761, arows5760]
  all_goals rfl

theorem atot5761 : totK PD2M8K2 D2M8K2.u5761 = [0, 413968481898, 1457828960360, 1418778370053, 332125873974, 9575627623, 0, 0] := by
  rw [show D2M8K2.u5761 = KTree.node D2M8K2.u5759 (nat_lit 12407262) (nat_lit 3778626699) (nat_lit 0) D2M8K2.u5760 from rfl, totK_node, atot5759, atot5760]
  decide +kernel

theorem arows5765 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5765 = true := by
  rw [show D2M8K2.u5765 = KTree.node D2M8K2.u5763 (nat_lit 12410829) (nat_lit 1307640355) (nat_lit 0) D2M8K2.u5764 from rfl, allE_node, arows5763, irow5765, arows5764]
  all_goals rfl

theorem atot5765 : totK PD2M8K2 D2M8K2.u5765 = [0, 381555484994, 1449007582360, 1475958235334, 285298375911, 6300972902, 0, 0] := by
  rw [show D2M8K2.u5765 = KTree.node D2M8K2.u5763 (nat_lit 12410829) (nat_lit 1307640355) (nat_lit 0) D2M8K2.u5764 from rfl, totK_node, atot5763, atot5764]
  decide +kernel

theorem arows5768 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5768 = true := by
  rw [show D2M8K2.u5768 = KTree.node D2M8K2.u5766 (nat_lit 12417923) (nat_lit 2746135022) (nat_lit 0) D2M8K2.u5767 from rfl, allE_node, arows5766, irow5768, arows5767]
  all_goals rfl

theorem atot5768 : totK PD2M8K2 D2M8K2.u5768 = [0, 439285579497, 1509309374321, 1405808009488, 266442166744, 5280507705, 0, 0] := by
  rw [show D2M8K2.u5768 = KTree.node D2M8K2.u5766 (nat_lit 12417923) (nat_lit 2746135022) (nat_lit 0) D2M8K2.u5767 from rfl, totK_node, atot5766, atot5767]
  decide +kernel

theorem arows5773 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5773 = true := by
  rw [show D2M8K2.u5773 = KTree.node D2M8K2.u5771 (nat_lit 12486993) (nat_lit 1760239441) (nat_lit 0) D2M8K2.u5772 from rfl, allE_node, arows5771, irow5773, arows5772]
  all_goals rfl

theorem atot5773 : totK PD2M8K2 D2M8K2.u5773 = [449429933209, 1088355372757, 910667143687, 844538765230, 327913004993, 20647649770, 0, 0] := by
  rw [show D2M8K2.u5773 = KTree.node D2M8K2.u5771 (nat_lit 12486993) (nat_lit 1760239441) (nat_lit 0) D2M8K2.u5772 from rfl, totK_node, atot5771, atot5772]
  decide +kernel

theorem arows5776 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5776 = true := by
  rw [show D2M8K2.u5776 = KTree.node D2M8K2.u5774 (nat_lit 12489609) (nat_lit 1837758669) (nat_lit 0) D2M8K2.u5775 from rfl, allE_node, arows5774, irow5776, arows5775]
  all_goals rfl

theorem atot5776 : totK PD2M8K2 D2M8K2.u5776 = [265623211152, 1175521261376, 1571138967793, 604980446268, 37609398105, 0, 0, 0] := by
  rw [show D2M8K2.u5776 = KTree.node D2M8K2.u5774 (nat_lit 12489609) (nat_lit 1837758669) (nat_lit 0) D2M8K2.u5775 from rfl, totK_node, atot5774, atot5775]
  decide +kernel

theorem arows5780 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5780 = true := by
  rw [show D2M8K2.u5780 = KTree.node D2M8K2.u5778 (nat_lit 12492563) (nat_lit 2330070553) (nat_lit 0) D2M8K2.u5779 from rfl, allE_node, arows5778, irow5780, arows5779]
  all_goals rfl

theorem atot5780 : totK PD2M8K2 D2M8K2.u5780 = [386772004951, 1439017125933, 1447394549522, 331561643554, 12995965463, 0, 0, 0] := by
  rw [show D2M8K2.u5780 = KTree.node D2M8K2.u5778 (nat_lit 12492563) (nat_lit 2330070553) (nat_lit 0) D2M8K2.u5779 from rfl, totK_node, atot5778, atot5779]
  decide +kernel

theorem arows5783 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5783 = true := by
  rw [show D2M8K2.u5783 = KTree.node D2M8K2.u5781 (nat_lit 12496325) (nat_lit 1845492369) (nat_lit 0) D2M8K2.u5782 from rfl, allE_node, arows5781, irow5783, arows5782]
  all_goals rfl

theorem atot5783 : totK PD2M8K2 D2M8K2.u5783 = [412760154532, 1445433877897, 1395828269786, 317120379244, 11831777775, 0, 0, 0] := by
  rw [show D2M8K2.u5783 = KTree.node D2M8K2.u5781 (nat_lit 12496325) (nat_lit 1845492369) (nat_lit 0) D2M8K2.u5782 from rfl, totK_node, atot5781, atot5782]
  decide +kernel

theorem arows5789 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5789 = true := by
  rw [show D2M8K2.u5789 = KTree.node D2M8K2.u5787 (nat_lit 12499571) (nat_lit 2613779081) (nat_lit 0) D2M8K2.u5788 from rfl, allE_node, arows5787, irow5789, arows5788]
  all_goals rfl

theorem atot5789 : totK PD2M8K2 D2M8K2.u5789 = [435479071296, 1534229731061, 1384935704917, 243513191911, 4959151969, 0, 0, 0] := by
  rw [show D2M8K2.u5789 = KTree.node D2M8K2.u5787 (nat_lit 12499571) (nat_lit 2613779081) (nat_lit 0) D2M8K2.u5788 from rfl, totK_node, atot5787, atot5788]
  decide +kernel

theorem arows5792 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5792 = true := by
  rw [show D2M8K2.u5792 = KTree.node D2M8K2.u5790 (nat_lit 12502921) (nat_lit 1386424734) (nat_lit 0) D2M8K2.u5791 from rfl, allE_node, arows5790, irow5792, arows5791]
  all_goals rfl

theorem atot5792 : totK PD2M8K2 D2M8K2.u5792 = [163433783747, 1038814802178, 1681511501162, 681905098026, 48944830458, 0, 0, 0] := by
  rw [show D2M8K2.u5792 = KTree.node D2M8K2.u5790 (nat_lit 12502921) (nat_lit 1386424734) (nat_lit 0) D2M8K2.u5791 from rfl, totK_node, atot5790, atot5791]
  decide +kernel

theorem arows5796 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5796 = true := by
  rw [show D2M8K2.u5796 = KTree.node D2M8K2.u5794 (nat_lit 12509555) (nat_lit 2803776139) (nat_lit 0) D2M8K2.u5795 from rfl, allE_node, arows5794, irow5796, arows5795]
  all_goals rfl

theorem atot5796 : totK PD2M8K2 D2M8K2.u5796 = [0, 332076935301, 1228610054314, 1475343713959, 551219961367, 36921873854, 0, 0] := by
  rw [show D2M8K2.u5796 = KTree.node D2M8K2.u5794 (nat_lit 12509555) (nat_lit 2803776139) (nat_lit 0) D2M8K2.u5795 from rfl, totK_node, atot5794, atot5795]
  decide +kernel

theorem arows5799 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5799 = true := by
  rw [show D2M8K2.u5799 = KTree.node D2M8K2.u5797 (nat_lit 12512352) (nat_lit 3269329108) (nat_lit 0) D2M8K2.u5798 from rfl, allE_node, arows5797, irow5799, arows5798]
  all_goals rfl

theorem atot5799 : totK PD2M8K2 D2M8K2.u5799 = [0, 425208287850, 1548760759890, 1387475818787, 244636105682, 5159868635, 0, 0] := by
  rw [show D2M8K2.u5799 = KTree.node D2M8K2.u5797 (nat_lit 12512352) (nat_lit 3269329108) (nat_lit 0) D2M8K2.u5798 from rfl, totK_node, atot5797, atot5798]
  decide +kernel

theorem arows5804 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5804 = true := by
  rw [show D2M8K2.u5804 = KTree.node D2M8K2.u5802 (nat_lit 12516002) (nat_lit 2762252210) (nat_lit 0) D2M8K2.u5803 from rfl, allE_node, arows5802, irow5804, arows5803]
  all_goals rfl

theorem atot5804 : totK PD2M8K2 D2M8K2.u5804 = [0, 462859052054, 1534820303563, 1327843373427, 248193420208, 5218872685, 0, 0] := by
  rw [show D2M8K2.u5804 = KTree.node D2M8K2.u5802 (nat_lit 12516002) (nat_lit 2762252210) (nat_lit 0) D2M8K2.u5803 from rfl, totK_node, atot5802, atot5803]
  decide +kernel

theorem arows5807 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5807 = true := by
  rw [show D2M8K2.u5807 = KTree.node D2M8K2.u5805 (nat_lit 12519682) (nat_lit 3884263210) (nat_lit 0) D2M8K2.u5806 from rfl, allE_node, arows5805, irow5807, arows5806]
  all_goals rfl

theorem atot5807 : totK PD2M8K2 D2M8K2.u5807 = [0, 441447864697, 1597796445956, 1388343787141, 196227295124, 1415142070, 0, 0] := by
  rw [show D2M8K2.u5807 = KTree.node D2M8K2.u5805 (nat_lit 12519682) (nat_lit 3884263210) (nat_lit 0) D2M8K2.u5806 from rfl, totK_node, atot5805, atot5806]
  decide +kernel

theorem arows5811 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5811 = true := by
  rw [show D2M8K2.u5811 = KTree.node D2M8K2.u5809 (nat_lit 12523421) (nat_lit 2292050166) (nat_lit 0) D2M8K2.u5810 from rfl, allE_node, arows5809, irow5811, arows5810]
  all_goals rfl

theorem atot5811 : totK PD2M8K2 D2M8K2.u5811 = [175368045151, 640696448479, 1232963684922, 1225587565610, 304369163247, 9302370699, 0, 0] := by
  rw [show D2M8K2.u5811 = KTree.node D2M8K2.u5809 (nat_lit 12523421) (nat_lit 2292050166) (nat_lit 0) D2M8K2.u5810 from rfl, totK_node, atot5809, atot5810]
  decide +kernel

theorem arows5814 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5814 = true := by
  rw [show D2M8K2.u5814 = KTree.node D2M8K2.u5812 (nat_lit 12527529) (nat_lit 1916366651) (nat_lit 0) D2M8K2.u5813 from rfl, allE_node, arows5812, irow5814, arows5813]
  all_goals rfl

theorem atot5814 : totK PD2M8K2 D2M8K2.u5814 = [508505511793, 1635256809299, 1316233455565, 186857290589, 1369150432, 0, 0, 0] := by
  rw [show D2M8K2.u5814 = KTree.node D2M8K2.u5812 (nat_lit 12527529) (nat_lit 1916366651) (nat_lit 0) D2M8K2.u5813 from rfl, totK_node, atot5812, atot5813]
  decide +kernel

theorem arows5821 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5821 = true := by
  rw [show D2M8K2.u5821 = KTree.node D2M8K2.u5819 (nat_lit 12530822) (nat_lit 3089259579) (nat_lit 0) D2M8K2.u5820 from rfl, allE_node, arows5819, irow5821, arows5820]
  all_goals rfl

theorem atot5821 : totK PD2M8K2 D2M8K2.u5821 = [278685436907, 1192533650161, 1541420125597, 594983085539, 37597116817, 0, 0, 0] := by
  rw [show D2M8K2.u5821 = KTree.node D2M8K2.u5819 (nat_lit 12530822) (nat_lit 3089259579) (nat_lit 0) D2M8K2.u5820 from rfl, totK_node, atot5819, atot5820]
  decide +kernel

theorem arows5824 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5824 = true := by
  rw [show D2M8K2.u5824 = KTree.node D2M8K2.u5822 (nat_lit 12533572) (nat_lit 3798767105) (nat_lit 0) D2M8K2.u5823 from rfl, allE_node, arows5822, irow5824, arows5823]
  all_goals rfl

theorem atot5824 : totK PD2M8K2 D2M8K2.u5824 = [416781722592, 1467110099986, 1401653545146, 323410101203, 13049727234, 0, 0, 0] := by
  rw [show D2M8K2.u5824 = KTree.node D2M8K2.u5822 (nat_lit 12533572) (nat_lit 3798767105) (nat_lit 0) D2M8K2.u5823 from rfl, totK_node, atot5822, atot5823]
  decide +kernel

theorem arows5828 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5828 = true := by
  rw [show D2M8K2.u5828 = KTree.node D2M8K2.u5826 (nat_lit 12540428) (nat_lit 3710297274) (nat_lit 0) D2M8K2.u5827 from rfl, allE_node, arows5826, irow5828, arows5827]
  all_goals rfl

theorem atot5828 : totK PD2M8K2 D2M8K2.u5828 = [413758767153, 1511413549874, 1419691899019, 257560835395, 4980514959, 0, 0, 0] := by
  rw [show D2M8K2.u5828 = KTree.node D2M8K2.u5826 (nat_lit 12540428) (nat_lit 3710297274) (nat_lit 0) D2M8K2.u5827 from rfl, totK_node, atot5826, atot5827]
  decide +kernel

theorem arows5831 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5831 = true := by
  rw [show D2M8K2.u5831 = KTree.node D2M8K2.u5829 (nat_lit 12543922) (nat_lit 3937058269) (nat_lit 0) D2M8K2.u5830 from rfl, allE_node, arows5829, irow5831, arows5830]
  all_goals rfl

theorem atot5831 : totK PD2M8K2 D2M8K2.u5831 = [249247453021, 1194182108407, 1621385521470, 511949238649, 23248205325, 0, 0, 0] := by
  rw [show D2M8K2.u5831 = KTree.node D2M8K2.u5829 (nat_lit 12543922) (nat_lit 3937058269) (nat_lit 0) D2M8K2.u5830 from rfl, totK_node, atot5829, atot5830]
  decide +kernel

theorem arows5836 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5836 = true := by
  rw [show D2M8K2.u5836 = KTree.node D2M8K2.u5834 (nat_lit 12548178) (nat_lit 2718875827) (nat_lit 0) D2M8K2.u5835 from rfl, allE_node, arows5834, irow5836, arows5835]
  all_goals rfl

theorem atot5836 : totK PD2M8K2 D2M8K2.u5836 = [0, 532185643757, 1668795329431, 1238922135699, 148545533982, 1206465782, 0, 0] := by
  rw [show D2M8K2.u5836 = KTree.node D2M8K2.u5834 (nat_lit 12548178) (nat_lit 2718875827) (nat_lit 0) D2M8K2.u5835 from rfl, totK_node, atot5834, atot5835]
  decide +kernel

theorem arows5839 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5839 = true := by
  rw [show D2M8K2.u5839 = KTree.node D2M8K2.u5837 (nat_lit 12552921) (nat_lit 1722548377) (nat_lit 0) D2M8K2.u5838 from rfl, allE_node, arows5837, irow5839, arows5838]
  all_goals rfl

theorem atot5839 : totK PD2M8K2 D2M8K2.u5839 = [0, 553427165490, 1727031421778, 1180646587636, 143973025887, 1162935789, 0, 0] := by
  rw [show D2M8K2.u5839 = KTree.node D2M8K2.u5837 (nat_lit 12552921) (nat_lit 1722548377) (nat_lit 0) D2M8K2.u5838 from rfl, totK_node, atot5837, atot5838]
  decide +kernel

theorem arows5843 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5843 = true := by
  rw [show D2M8K2.u5843 = KTree.node D2M8K2.u5841 (nat_lit 12559780) (nat_lit 3867998432) (nat_lit 0) D2M8K2.u5842 from rfl, allE_node, arows5841, irow5843, arows5842]
  all_goals rfl

theorem atot5843 : totK PD2M8K2 D2M8K2.u5843 = [0, 410637294450, 1482876307952, 1326076663828, 278978047288, 12874862223, 0, 0] := by
  rw [show D2M8K2.u5843 = KTree.node D2M8K2.u5841 (nat_lit 12559780) (nat_lit 3867998432) (nat_lit 0) D2M8K2.u5842 from rfl, totK_node, atot5841, atot5842]
  decide +kernel

theorem arows5846 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5846 = true := by
  rw [show D2M8K2.u5846 = KTree.node D2M8K2.u5844 (nat_lit 12563450) (nat_lit 4184849567) (nat_lit 0) D2M8K2.u5845 from rfl, allE_node, arows5844, irow5846, arows5845]
  all_goals rfl

theorem atot5846 : totK PD2M8K2 D2M8K2.u5846 = [229587690250, 935930742373, 1485236481478, 847294899815, 118954741146, 3552795014, 0, 0] := by
  rw [show D2M8K2.u5846 = KTree.node D2M8K2.u5844 (nat_lit 12563450) (nat_lit 4184849567) (nat_lit 0) D2M8K2.u5845 from rfl, totK_node, atot5844, atot5845]
  decide +kernel

theorem arows5852 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5852 = true := by
  rw [show D2M8K2.u5852 = KTree.node D2M8K2.u5850 (nat_lit 12571893) (nat_lit 1724547134) (nat_lit 0) D2M8K2.u5851 from rfl, allE_node, arows5850, irow5852, arows5851]
  all_goals rfl

theorem atot5852 : totK PD2M8K2 D2M8K2.u5852 = [291214882346, 1215637940915, 1500362972219, 580389945251, 37595089999, 0, 0, 0] := by
  rw [show D2M8K2.u5852 = KTree.node D2M8K2.u5850 (nat_lit 12571893) (nat_lit 1724547134) (nat_lit 0) D2M8K2.u5851 from rfl, totK_node, atot5850, atot5851]
  decide +kernel

theorem arows5855 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5855 = true := by
  rw [show D2M8K2.u5855 = KTree.node D2M8K2.u5853 (nat_lit 12578130) (nat_lit 3411121563) (nat_lit 0) D2M8K2.u5854 from rfl, allE_node, arows5853, irow5855, arows5854]
  all_goals rfl

theorem atot5855 : totK PD2M8K2 D2M8K2.u5855 = [402153184742, 1418824385558, 1433278241489, 345732987457, 13250685261, 0, 0, 0] := by
  rw [show D2M8K2.u5855 = KTree.node D2M8K2.u5853 (nat_lit 12578130) (nat_lit 3411121563) (nat_lit 0) D2M8K2.u5854 from rfl, totK_node, atot5853, atot5854]
  decide +kernel

theorem arows5859 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5859 = true := by
  rw [show D2M8K2.u5859 = KTree.node D2M8K2.u5857 (nat_lit 12581246) (nat_lit 2978853002) (nat_lit 0) D2M8K2.u5858 from rfl, allE_node, arows5857, irow5859, arows5858]
  all_goals rfl

theorem atot5859 : totK PD2M8K2 D2M8K2.u5859 = [438457347196, 1541261897953, 1380080177215, 244206699644, 4980514959, 0, 0, 0] := by
  rw [show D2M8K2.u5859 = KTree.node D2M8K2.u5857 (nat_lit 12581246) (nat_lit 2978853002) (nat_lit 0) D2M8K2.u5858 from rfl, totK_node, atot5857, atot5858]
  decide +kernel

theorem arows5862 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5862 = true := by
  rw [show D2M8K2.u5862 = KTree.node D2M8K2.u5860 (nat_lit 12585161) (nat_lit 1541341933) (nat_lit 0) D2M8K2.u5861 from rfl, allE_node, arows5860, irow5862, arows5861]
  all_goals rfl

theorem atot5862 : totK PD2M8K2 D2M8K2.u5862 = [300928237669, 1292587363785, 1555461197682, 457432517299, 22006723946, 0, 0, 0] := by
  rw [show D2M8K2.u5862 = KTree.node D2M8K2.u5860 (nat_lit 12585161) (nat_lit 1541341933) (nat_lit 0) D2M8K2.u5861 from rfl, totK_node, atot5860, atot5861]
  decide +kernel

theorem arows5867 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5867 = true := by
  rw [show D2M8K2.u5867 = KTree.node D2M8K2.u5865 (nat_lit 12591848) (nat_lit 2154407346) (nat_lit 0) D2M8K2.u5866 from rfl, allE_node, arows5865, irow5867, arows5866]
  all_goals rfl

theorem atot5867 : totK PD2M8K2 D2M8K2.u5867 = [0, 692962128840, 1844422708160, 1024542323077, 81003488760, 0, 0, 0] := by
  rw [show D2M8K2.u5867 = KTree.node D2M8K2.u5865 (nat_lit 12591848) (nat_lit 2154407346) (nat_lit 0) D2M8K2.u5866 from rfl, totK_node, atot5865, atot5866]
  decide +kernel

theorem arows5870 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5870 = true := by
  rw [show D2M8K2.u5870 = KTree.node D2M8K2.u5868 (nat_lit 12600256) (nat_lit 1425656091) (nat_lit 0) D2M8K2.u5869 from rfl, allE_node, arows5868, irow5870, arows5869]
  all_goals rfl

theorem atot5870 : totK PD2M8K2 D2M8K2.u5870 = [0, 427781523493, 1461889874986, 1339799270405, 303429317873, 13105450397, 0, 0] := by
  rw [show D2M8K2.u5870 = KTree.node D2M8K2.u5868 (nat_lit 12600256) (nat_lit 1425656091) (nat_lit 0) D2M8K2.u5869 from rfl, totK_node, atot5868, atot5869]
  decide +kernel

theorem arows5874 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5874 = true := by
  rw [show D2M8K2.u5874 = KTree.node D2M8K2.u5872 (nat_lit 12604170) (nat_lit 3785293213) (nat_lit 0) D2M8K2.u5873 from rfl, allE_node, arows5872, irow5874, arows5873]
  all_goals rfl

theorem atot5874 : totK PD2M8K2 D2M8K2.u5874 = [0, 459444248749, 1594753005990, 1298906616464, 194618906443, 4720618446, 0, 0] := by
  rw [show D2M8K2.u5874 = KTree.node D2M8K2.u5872 (nat_lit 12604170) (nat_lit 3785293213) (nat_lit 0) D2M8K2.u5873 from rfl, totK_node, atot5872, atot5873]
  decide +kernel

theorem arows5877 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5877 = true := by
  rw [show D2M8K2.u5877 = KTree.node D2M8K2.u5875 (nat_lit 12609320) (nat_lit 3841917883) (nat_lit 0) D2M8K2.u5876 from rfl, allE_node, arows5875, irow5877, arows5876]
  all_goals rfl

theorem atot5877 : totK PD2M8K2 D2M8K2.u5877 = [510813857819, 1611573321721, 1271226269215, 205787931828, 8462762220, 0, 0, 0] := by
  rw [show D2M8K2.u5877 = KTree.node D2M8K2.u5875 (nat_lit 12609320) (nat_lit 3841917883) (nat_lit 0) D2M8K2.u5876 from rfl, totK_node, atot5875, atot5876]
  decide +kernel

theorem arows5886 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5886 = true := by
  rw [show D2M8K2.u5886 = KTree.node D2M8K2.u5884 (nat_lit 12613291) (nat_lit 1640564298) (nat_lit 0) D2M8K2.u5885 from rfl, allE_node, arows5884, irow5886, arows5885]
  all_goals rfl

theorem atot5886 : totK PD2M8K2 D2M8K2.u5886 = [315582023195, 1212378847046, 1468852664546, 580490138380, 37601708222, 0, 0, 0] := by
  rw [show D2M8K2.u5886 = KTree.node D2M8K2.u5884 (nat_lit 12613291) (nat_lit 1640564298) (nat_lit 0) D2M8K2.u5885 from rfl, totK_node, atot5884, atot5885]
  decide +kernel

theorem arows5889 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5889 = true := by
  rw [show D2M8K2.u5889 = KTree.node D2M8K2.u5887 (nat_lit 12616137) (nat_lit 1809676038) (nat_lit 0) D2M8K2.u5888 from rfl, allE_node, arows5887, irow5889, arows5888]
  all_goals rfl

theorem atot5889 : totK PD2M8K2 D2M8K2.u5889 = [401221832216, 1433060882747, 1422612126265, 334534028968, 13049727234, 0, 0, 0] := by
  rw [show D2M8K2.u5889 = KTree.node D2M8K2.u5887 (nat_lit 12616137) (nat_lit 1809676038) (nat_lit 0) D2M8K2.u5888 from rfl, totK_node, atot5887, atot5888]
  decide +kernel

theorem arows5893 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5893 = true := by
  rw [show D2M8K2.u5893 = KTree.node D2M8K2.u5891 (nat_lit 12619657) (nat_lit 1516325822) (nat_lit 0) D2M8K2.u5892 from rfl, allE_node, arows5891, irow5893, arows5892]
  all_goals rfl

theorem atot5893 : totK PD2M8K2 D2M8K2.u5893 = [401005754361, 1436730929525, 1389538431645, 333416271063, 13250685261, 0, 0, 0] := by
  rw [show D2M8K2.u5893 = KTree.node D2M8K2.u5891 (nat_lit 12619657) (nat_lit 1516325822) (nat_lit 0) D2M8K2.u5892 from rfl, totK_node, atot5891, atot5892]
  decide +kernel

theorem arows5896 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5896 = true := by
  rw [show D2M8K2.u5896 = KTree.node D2M8K2.u5894 (nat_lit 12622722) (nat_lit 2904283101) (nat_lit 0) D2M8K2.u5895 from rfl, allE_node, arows5894, irow5896, arows5895]
  all_goals rfl

theorem atot5896 : totK PD2M8K2 D2M8K2.u5896 = [355265117471, 1443427470473, 1511871511713, 305941326569, 6350335412, 0, 0, 0] := by
  rw [show D2M8K2.u5896 = KTree.node D2M8K2.u5894 (nat_lit 12622722) (nat_lit 2904283101) (nat_lit 0) D2M8K2.u5895 from rfl, totK_node, atot5894, atot5895]
  decide +kernel

theorem arows5901 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5901 = true := by
  rw [show D2M8K2.u5901 = KTree.node D2M8K2.u5899 (nat_lit 12630821) (nat_lit 1925132436) (nat_lit 0) D2M8K2.u5900 from rfl, allE_node, arows5899, irow5901, arows5900]
  all_goals rfl

theorem atot5901 : totK PD2M8K2 D2M8K2.u5901 = [0, 537324774809, 1670399427482, 1189629721643, 143708098234, 1138244013, 0, 0] := by
  rw [show D2M8K2.u5901 = KTree.node D2M8K2.u5899 (nat_lit 12630821) (nat_lit 1925132436) (nat_lit 0) D2M8K2.u5900 from rfl, totK_node, atot5899, atot5900]
  decide +kernel

theorem arows5904 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5904 = true := by
  rw [show D2M8K2.u5904 = KTree.node D2M8K2.u5902 (nat_lit 12635882) (nat_lit 4191348247) (nat_lit 0) D2M8K2.u5903 from rfl, allE_node, arows5902, irow5904, arows5903]
  all_goals rfl

theorem atot5904 : totK PD2M8K2 D2M8K2.u5904 = [0, 756722628680, 1914241843453, 910082136172, 48012607713, 0, 0, 0] := by
  rw [show D2M8K2.u5904 = KTree.node D2M8K2.u5902 (nat_lit 12635882) (nat_lit 4191348247) (nat_lit 0) D2M8K2.u5903 from rfl, totK_node, atot5902, atot5903]
  decide +kernel

theorem arows5908 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5908 = true := by
  rw [show D2M8K2.u5908 = KTree.node D2M8K2.u5906 (nat_lit 12642625) (nat_lit 1551245451) (nat_lit 0) D2M8K2.u5907 from rfl, allE_node, arows5906, irow5908, arows5907]
  all_goals rfl

theorem atot5908 : totK PD2M8K2 D2M8K2.u5908 = [0, 601657890338, 1745600779094, 1070709553861, 119676414471, 1095107716, 0, 0] := by
  rw [show D2M8K2.u5908 = KTree.node D2M8K2.u5906 (nat_lit 12642625) (nat_lit 1551245451) (nat_lit 0) D2M8K2.u5907 from rfl, totK_node, atot5906, atot5907]
  decide +kernel

theorem arows5911 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5911 = true := by
  rw [show D2M8K2.u5911 = KTree.node D2M8K2.u5909 (nat_lit 12649897) (nat_lit 1508216469) (nat_lit 0) D2M8K2.u5910 from rfl, allE_node, arows5909, irow5911, arows5910]
  all_goals rfl

theorem atot5911 : totK PD2M8K2 D2M8K2.u5911 = [353677020485, 1199877707174, 1307192220819, 623622768441, 121352030014, 3882006667, 0, 0] := by
  rw [show D2M8K2.u5911 = KTree.node D2M8K2.u5909 (nat_lit 12649897) (nat_lit 1508216469) (nat_lit 0) D2M8K2.u5910 from rfl, totK_node, atot5909, atot5910]
  decide +kernel

theorem arows5917 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5917 = true := by
  rw [show D2M8K2.u5917 = KTree.node D2M8K2.u5915 (nat_lit 12653936) (nat_lit 2939935682) (nat_lit 0) D2M8K2.u5916 from rfl, allE_node, arows5915, irow5917, arows5916]
  all_goals rfl

theorem atot5917 : totK PD2M8K2 D2M8K2.u5917 = [398482584663, 1398541936849, 1377108686551, 431765665247, 29375735501, 0, 0, 0] := by
  rw [show D2M8K2.u5917 = KTree.node D2M8K2.u5915 (nat_lit 12653936) (nat_lit 2939935682) (nat_lit 0) D2M8K2.u5916 from rfl, totK_node, atot5915, atot5916]
  decide +kernel

theorem arows5920 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5920 = true := by
  rw [show D2M8K2.u5920 = KTree.node D2M8K2.u5918 (nat_lit 12656661) (nat_lit 1458309550) (nat_lit 0) D2M8K2.u5919 from rfl, allE_node, arows5918, irow5920, arows5919]
  all_goals rfl

theorem atot5920 : totK PD2M8K2 D2M8K2.u5920 = [416742846530, 1419673793155, 1427875800407, 369411676048, 10523317450, 0, 0, 0] := by
  rw [show D2M8K2.u5920 = KTree.node D2M8K2.u5918 (nat_lit 12656661) (nat_lit 1458309550) (nat_lit 0) D2M8K2.u5919 from rfl, totK_node, atot5918, atot5919]
  decide +kernel

theorem arows5924 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5924 = true := by
  rw [show D2M8K2.u5924 = KTree.node D2M8K2.u5922 (nat_lit 12660428) (nat_lit 3174329735) (nat_lit 0) D2M8K2.u5923 from rfl, allE_node, arows5922, irow5924, arows5923]
  all_goals rfl

theorem atot5924 : totK PD2M8K2 D2M8K2.u5924 = [385573486721, 1409588862813, 1433736600109, 366504544696, 19077010550, 0, 0, 0] := by
  rw [show D2M8K2.u5924 = KTree.node D2M8K2.u5922 (nat_lit 12660428) (nat_lit 3174329735) (nat_lit 0) D2M8K2.u5923 from rfl, totK_node, atot5922, atot5923]
  decide +kernel

theorem arows5927 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5927 = true := by
  rw [show D2M8K2.u5927 = KTree.node D2M8K2.u5925 (nat_lit 12667131) (nat_lit 3745994988) (nat_lit 0) D2M8K2.u5926 from rfl, allE_node, arows5925, irow5927, arows5926]
  all_goals rfl

theorem atot5927 : totK PD2M8K2 D2M8K2.u5927 = [440762120087, 1513355634864, 1404515517752, 277642127796, 4794543529, 0, 0, 0] := by
  rw [show D2M8K2.u5927 = KTree.node D2M8K2.u5925 (nat_lit 12667131) (nat_lit 3745994988) (nat_lit 0) D2M8K2.u5926 from rfl, totK_node, atot5925, atot5926]
  decide +kernel

theorem arows5932 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5932 = true := by
  rw [show D2M8K2.u5932 = KTree.node D2M8K2.u5930 (nat_lit 12670591) (nat_lit 2355767884) (nat_lit 0) D2M8K2.u5931 from rfl, allE_node, arows5930, irow5932, arows5931]
  all_goals rfl

theorem atot5932 : totK PD2M8K2 D2M8K2.u5932 = [0, 524521984008, 1671602773185, 1236306450028, 145292053120, 1310285577, 0, 0] := by
  rw [show D2M8K2.u5932 = KTree.node D2M8K2.u5930 (nat_lit 12670591) (nat_lit 2355767884) (nat_lit 0) D2M8K2.u5931 from rfl, totK_node, atot5930, atot5931]
  decide +kernel

theorem arows5935 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5935 = true := by
  rw [show D2M8K2.u5935 = KTree.node D2M8K2.u5933 (nat_lit 12674675) (nat_lit 2895302561) (nat_lit 0) D2M8K2.u5934 from rfl, allE_node, arows5933, irow5935, arows5934]
  all_goals rfl

theorem atot5935 : totK PD2M8K2 D2M8K2.u5935 = [0, 733902731140, 1845301958733, 987141404972, 80223789868, 0, 0, 0] := by
  rw [show D2M8K2.u5935 = KTree.node D2M8K2.u5933 (nat_lit 12674675) (nat_lit 2895302561) (nat_lit 0) D2M8K2.u5934 from rfl, totK_node, atot5933, atot5934]
  decide +kernel

theorem arows5939 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5939 = true := by
  rw [show D2M8K2.u5939 = KTree.node D2M8K2.u5937 (nat_lit 12679858) (nat_lit 3998051431) (nat_lit 0) D2M8K2.u5938 from rfl, allE_node, arows5937, irow5939, arows5938]
  all_goals rfl

theorem atot5939 : totK PD2M8K2 D2M8K2.u5939 = [0, 473687205070, 1584420459996, 1318883914204, 214344439624, 4879840392, 0, 0] := by
  rw [show D2M8K2.u5939 = KTree.node D2M8K2.u5937 (nat_lit 12679858) (nat_lit 3998051431) (nat_lit 0) D2M8K2.u5938 from rfl, totK_node, atot5937, atot5938]
  decide +kernel

theorem arows5942 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5942 = true := by
  rw [show D2M8K2.u5942 = KTree.node D2M8K2.u5940 (nat_lit 12687293) (nat_lit 2282052395) (nat_lit 0) D2M8K2.u5941 from rfl, allE_node, arows5940, irow5942, arows5941]
  all_goals rfl

theorem atot5942 : totK PD2M8K2 D2M8K2.u5942 = [0, 439224370106, 1579127448066, 1357296928990, 216446650164, 4931404646, 0, 0] := by
  rw [show D2M8K2.u5942 = KTree.node D2M8K2.u5940 (nat_lit 12687293) (nat_lit 2282052395) (nat_lit 0) D2M8K2.u5941 from rfl, totK_node, atot5940, atot5941]
  decide +kernel

theorem arows5949 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5949 = true := by
  rw [show D2M8K2.u5949 = KTree.node D2M8K2.u5947 (nat_lit 12690413) (nat_lit 2098322605) (nat_lit 0) D2M8K2.u5948 from rfl, allE_node, arows5947, irow5949, arows5948]
  all_goals rfl

theorem atot5949 : totK PD2M8K2 D2M8K2.u5949 = [0, 359781790945, 1352306700176, 1442364738318, 408878873830, 21751168066, 0, 0] := by
  rw [show D2M8K2.u5949 = KTree.node D2M8K2.u5947 (nat_lit 12690413) (nat_lit 2098322605) (nat_lit 0) D2M8K2.u5948 from rfl, totK_node, atot5947, atot5948]
  decide +kernel

theorem arows5952 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5952 = true := by
  rw [show D2M8K2.u5952 = KTree.node D2M8K2.u5950 (nat_lit 12738226) (nat_lit 4038837434) (nat_lit 0) D2M8K2.u5951 from rfl, allE_node, arows5950, irow5952, arows5951]
  all_goals rfl

theorem atot5952 : totK PD2M8K2 D2M8K2.u5952 = [0, 321172386253, 1195582340874, 1520650810001, 594958393743, 37609398105, 0, 0] := by
  rw [show D2M8K2.u5952 = KTree.node D2M8K2.u5950 (nat_lit 12738226) (nat_lit 4038837434) (nat_lit 0) D2M8K2.u5951 from rfl, totK_node, atot5950, atot5951]
  decide +kernel

theorem arows5956 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5956 = true := by
  rw [show D2M8K2.u5956 = KTree.node D2M8K2.u5954 (nat_lit 12741216) (nat_lit 3392819896) (nat_lit 0) D2M8K2.u5955 from rfl, allE_node, arows5954, irow5956, arows5955]
  all_goals rfl

theorem atot5956 : totK PD2M8K2 D2M8K2.u5956 = [0, 395740351873, 1439724219099, 1443428745180, 315714126453, 8706415949, 0, 0] := by
  rw [show D2M8K2.u5956 = KTree.node D2M8K2.u5954 (nat_lit 12741216) (nat_lit 3392819896) (nat_lit 0) D2M8K2.u5955 from rfl, totK_node, atot5954, atot5955]
  decide +kernel

theorem arows5959 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5959 = true := by
  rw [show D2M8K2.u5959 = KTree.node D2M8K2.u5957 (nat_lit 12744967) (nat_lit 2394825812) (nat_lit 0) D2M8K2.u5958 from rfl, allE_node, arows5957, irow5959, arows5958]
  all_goals rfl

theorem atot5959 : totK PD2M8K2 D2M8K2.u5959 = [0, 401844521523, 1441718641924, 1405764325009, 315283916066, 8824320960, 0, 0] := by
  rw [show D2M8K2.u5959 = KTree.node D2M8K2.u5957 (nat_lit 12744967) (nat_lit 2394825812) (nat_lit 0) D2M8K2.u5958 from rfl, totK_node, atot5957, atot5958]
  decide +kernel

theorem arows5964 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5964 = true := by
  rw [show D2M8K2.u5964 = KTree.node D2M8K2.u5962 (nat_lit 12748083) (nat_lit 3632946869) (nat_lit 0) D2M8K2.u5963 from rfl, allE_node, arows5962, irow5964, arows5963]
  all_goals rfl

theorem atot5964 : totK PD2M8K2 D2M8K2.u5964 = [0, 460886329650, 1565860246817, 1353963992327, 228082136044, 2498823382, 0, 0] := by
  rw [show D2M8K2.u5964 = KTree.node D2M8K2.u5962 (nat_lit 12748083) (nat_lit 3632946869) (nat_lit 0) D2M8K2.u5963 from rfl, totK_node, atot5962, atot5963]
  decide +kernel

theorem arows5967 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5967 = true := by
  rw [show D2M8K2.u5967 = KTree.node D2M8K2.u5965 (nat_lit 12751588) (nat_lit 3836185354) (nat_lit 0) D2M8K2.u5966 from rfl, allE_node, arows5965, irow5967, arows5966]
  all_goals rfl

theorem atot5967 : totK PD2M8K2 D2M8K2.u5967 = [0, 178282915971, 1124724723654, 1664650750185, 588879247312, 37675614470, 0, 0] := by
  rw [show D2M8K2.u5967 = KTree.node D2M8K2.u5965 (nat_lit 12751588) (nat_lit 3836185354) (nat_lit 0) D2M8K2.u5966 from rfl, totK_node, atot5965, atot5966]
  decide +kernel

theorem arows5971 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5971 = true := by
  rw [show D2M8K2.u5971 = KTree.node D2M8K2.u5969 (nat_lit 12758286) (nat_lit 3835350830) (nat_lit 0) D2M8K2.u5970 from rfl, allE_node, arows5969, irow5971, arows5970]
  all_goals rfl

theorem atot5971 : totK PD2M8K2 D2M8K2.u5971 = [0, 0, 282075261720, 1227533307913, 1522804358337, 530132654566, 32664942840, 0] := by
  rw [show D2M8K2.u5971 = KTree.node D2M8K2.u5969 (nat_lit 12758286) (nat_lit 3835350830) (nat_lit 0) D2M8K2.u5970 from rfl, totK_node, atot5969, atot5970]
  decide +kernel

theorem arows5974 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5974 = true := by
  rw [show D2M8K2.u5974 = KTree.node D2M8K2.u5972 (nat_lit 12761064) (nat_lit 2257300797) (nat_lit 0) D2M8K2.u5973 from rfl, allE_node, arows5972, irow5974, arows5973]
  all_goals rfl

theorem atot5974 : totK PD2M8K2 D2M8K2.u5974 = [0, 0, 467883246865, 1524434731285, 1318026627105, 244077454148, 9324794432, 0] := by
  rw [show D2M8K2.u5974 = KTree.node D2M8K2.u5972 (nat_lit 12761064) (nat_lit 2257300797) (nat_lit 0) D2M8K2.u5973 from rfl, totK_node, atot5972, atot5973]
  decide +kernel

theorem arows5980 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5980 = true := by
  rw [show D2M8K2.u5980 = KTree.node D2M8K2.u5978 (nat_lit 12764675) (nat_lit 2878848963) (nat_lit 0) D2M8K2.u5979 from rfl, allE_node, arows5978, irow5980, arows5979]
  all_goals rfl

theorem atot5980 : totK PD2M8K2 D2M8K2.u5980 = [0, 0, 451195952624, 1540722746497, 1323027747472, 226090717867, 5126512042, 0] := by
  rw [show D2M8K2.u5980 = KTree.node D2M8K2.u5978 (nat_lit 12764675) (nat_lit 2878848963) (nat_lit 0) D2M8K2.u5979 from rfl, totK_node, atot5978, atot5979]
  decide +kernel

theorem arows5983 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5983 = true := by
  rw [show D2M8K2.u5983 = KTree.node D2M8K2.u5981 (nat_lit 12768306) (nat_lit 2969994777) (nat_lit 0) D2M8K2.u5982 from rfl, allE_node, arows5981, irow5983, arows5982]
  all_goals rfl

theorem atot5983 : totK PD2M8K2 D2M8K2.u5983 = [0, 0, 464975714069, 1612998189356, 1350475103626, 175841151747, 1392055030, 0] := by
  rw [show D2M8K2.u5983 = KTree.node D2M8K2.u5981 (nat_lit 12768306) (nat_lit 2969994777) (nat_lit 0) D2M8K2.u5982 from rfl, totK_node, atot5981, atot5982]
  decide +kernel

theorem arows5987 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5987 = true := by
  rw [show D2M8K2.u5987 = KTree.node D2M8K2.u5985 (nat_lit 12772280) (nat_lit 3335923554) (nat_lit 0) D2M8K2.u5986 from rfl, allE_node, arows5985, irow5987, arows5986]
  all_goals rfl

theorem atot5987 : totK PD2M8K2 D2M8K2.u5987 = [0, 175368045151, 675826355637, 1233703897631, 1179494589240, 276786117824, 9139067247, 0] := by
  rw [show D2M8K2.u5987 = KTree.node D2M8K2.u5985 (nat_lit 12772280) (nat_lit 3335923554) (nat_lit 0) D2M8K2.u5986 from rfl, totK_node, atot5985, atot5986]
  decide +kernel

theorem arows5990 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5990 = true := by
  rw [show D2M8K2.u5990 = KTree.node D2M8K2.u5988 (nat_lit 12776596) (nat_lit 3998811703) (nat_lit 0) D2M8K2.u5989 from rfl, allE_node, arows5988, irow5990, arows5989]
  all_goals rfl

theorem atot5990 : totK PD2M8K2 D2M8K2.u5990 = [0, 508505511793, 1659853718425, 1289144096981, 159531414601, 1275377855, 0, 0] := by
  rw [show D2M8K2.u5990 = KTree.node D2M8K2.u5988 (nat_lit 12776596) (nat_lit 3998811703) (nat_lit 0) D2M8K2.u5989 from rfl, totK_node, atot5988, atot5989]
  decide +kernel

theorem arows5995 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5995 = true := by
  rw [show D2M8K2.u5995 = KTree.node D2M8K2.u5993 (nat_lit 12779730) (nat_lit 2446859310) (nat_lit 0) D2M8K2.u5994 from rfl, allE_node, arows5993, irow5995, arows5994]
  all_goals rfl

theorem atot5995 : totK PD2M8K2 D2M8K2.u5995 = [0, 317307697575, 1198618128928, 1503964588930, 588990905985, 37487326182, 0, 0] := by
  rw [show D2M8K2.u5995 = KTree.node D2M8K2.u5993 (nat_lit 12779730) (nat_lit 2446859310) (nat_lit 0) D2M8K2.u5994 from rfl, totK_node, atot5993, atot5994]
  decide +kernel

theorem arows5998 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5998 = true := by
  rw [show D2M8K2.u5998 = KTree.node D2M8K2.u5996 (nat_lit 12782608) (nat_lit 3414903850) (nat_lit 0) D2M8K2.u5997 from rfl, allE_node, arows5996, irow5998, arows5997]
  all_goals rfl

theorem atot5998 : totK PD2M8K2 D2M8K2.u5998 = [0, 374652833641, 1428439224803, 1443977189151, 334883206544, 13049727234, 0, 0] := by
  rw [show D2M8K2.u5998 = KTree.node D2M8K2.u5996 (nat_lit 12782608) (nat_lit 3414903850) (nat_lit 0) D2M8K2.u5997 from rfl, totK_node, atot5996, atot5997]
  decide +kernel

theorem arows6002 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6002 = true := by
  rw [show D2M8K2.u6002 = KTree.node D2M8K2.u6000 (nat_lit 12789326) (nat_lit 3871238098) (nat_lit 0) D2M8K2.u6001 from rfl, allE_node, arows6000, irow6002, arows6001]
  all_goals rfl

theorem atot6002 : totK PD2M8K2 D2M8K2.u6002 = [0, 445691715500, 1529684544949, 1380008263529, 246260556101, 4980514959, 0, 0] := by
  rw [show D2M8K2.u6002 = KTree.node D2M8K2.u6000 (nat_lit 12789326) (nat_lit 3871238098) (nat_lit 0) D2M8K2.u6001 from rfl, totK_node, atot6000, atot6001]
  decide +kernel

theorem arows6005 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6005 = true := by
  rw [show D2M8K2.u6005 = KTree.node D2M8K2.u6003 (nat_lit 12792968) (nat_lit 3028481235) (nat_lit 0) D2M8K2.u6004 from rfl, allE_node, arows6003, irow6005, arows6004]
  all_goals rfl

theorem atot6005 : totK PD2M8K2 D2M8K2.u6005 = [0, 213309932166, 1193033464195, 1655982701441, 494212484772, 19170701339, 0, 0] := by
  rw [show D2M8K2.u6005 = KTree.node D2M8K2.u6003 (nat_lit 12792968) (nat_lit 3028481235) (nat_lit 0) D2M8K2.u6004 from rfl, totK_node, atot6003, atot6004]
  decide +kernel

theorem arows6013 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6013 = true := by
  rw [show D2M8K2.u6013 = KTree.node D2M8K2.u6011 (nat_lit 12798554) (nat_lit 4057403736) (nat_lit 0) D2M8K2.u6012 from rfl, allE_node, arows6011, irow6013, arows6012]
  all_goals rfl

theorem atot6013 : totK PD2M8K2 D2M8K2.u6013 = [0, 0, 762551014200, 1892393520260, 886234230065, 58597296997, 0, 0] := by
  rw [show D2M8K2.u6013 = KTree.node D2M8K2.u6011 (nat_lit 12798554) (nat_lit 4057403736) (nat_lit 0) D2M8K2.u6012 from rfl, totK_node, atot6011, atot6012]
  decide +kernel

theorem arows6016 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6016 = true := by
  rw [show D2M8K2.u6016 = KTree.node D2M8K2.u6014 (nat_lit 12803337) (nat_lit 1786811280) (nat_lit 0) D2M8K2.u6015 from rfl, allE_node, arows6014, irow6016, arows6015]
  all_goals rfl

theorem atot6016 : totK PD2M8K2 D2M8K2.u6016 = [0, 0, 447062980319, 1546737909519, 1318497121248, 223442181375, 5320761635, 0] := by
  rw [show D2M8K2.u6016 = KTree.node D2M8K2.u6014 (nat_lit 12803337) (nat_lit 1786811280) (nat_lit 0) D2M8K2.u6015 from rfl, totK_node, atot6014, atot6015]
  decide +kernel

theorem arows6020 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6020 = true := by
  rw [show D2M8K2.u6020 = KTree.node D2M8K2.u6018 (nat_lit 12810629) (nat_lit 1883842654) (nat_lit 0) D2M8K2.u6019 from rfl, allE_node, arows6018, irow6020, arows6019]
  all_goals rfl

theorem atot6020 : totK PD2M8K2 D2M8K2.u6020 = [0, 0, 550211373840, 1694069859000, 1173601995849, 130261564325, 1225787871, 0] := by
  rw [show D2M8K2.u6020 = KTree.node D2M8K2.u6018 (nat_lit 12810629) (nat_lit 1883842654) (nat_lit 0) D2M8K2.u6019 from rfl, totK_node, atot6018, atot6019]
  decide +kernel

theorem arows6023 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6023 = true := by
  rw [show D2M8K2.u6023 = KTree.node D2M8K2.u6021 (nat_lit 12819402) (nat_lit 3720273817) (nat_lit 0) D2M8K2.u6022 from rfl, allE_node, arows6021, irow6023, arows6022]
  all_goals rfl

theorem atot6023 : totK PD2M8K2 D2M8K2.u6023 = [0, 429562897600, 1362232986680, 1328587614848, 484459486639, 38364741381, 0, 0] := by
  rw [show D2M8K2.u6023 = KTree.node D2M8K2.u6021 (nat_lit 12819402) (nat_lit 3720273817) (nat_lit 0) D2M8K2.u6022 from rfl, totK_node, atot6021, atot6022]
  decide +kernel

theorem arows6028 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6028 = true := by
  rw [show D2M8K2.u6028 = KTree.node D2M8K2.u6026 (nat_lit 12825638) (nat_lit 4041823053) (nat_lit 0) D2M8K2.u6027 from rfl, allE_node, arows6026, irow6028, arows6027]
  all_goals rfl

theorem atot6028 : totK PD2M8K2 D2M8K2.u6028 = [0, 426867752077, 1428377279085, 1384830490011, 371944072351, 12186868223, 0, 0] := by
  rw [show D2M8K2.u6028 = KTree.node D2M8K2.u6026 (nat_lit 12825638) (nat_lit 4041823053) (nat_lit 0) D2M8K2.u6027 from rfl, totK_node, atot6026, atot6027]
  decide +kernel

theorem arows6031 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6031 = true := by
  rw [show D2M8K2.u6031 = KTree.node D2M8K2.u6029 (nat_lit 12829013) (nat_lit 2347954106) (nat_lit 0) D2M8K2.u6030 from rfl, allE_node, arows6029, irow6031, arows6030]
  all_goals rfl

theorem atot6031 : totK PD2M8K2 D2M8K2.u6031 = [0, 400075243880, 1440235134904, 1403728182752, 325662521821, 13196099988, 0, 0] := by
  rw [show D2M8K2.u6031 = KTree.node D2M8K2.u6029 (nat_lit 12829013) (nat_lit 2347954106) (nat_lit 0) D2M8K2.u6030 from rfl, totK_node, atot6029, atot6030]
  decide +kernel

theorem arows6035 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6035 = true := by
  rw [show D2M8K2.u6035 = KTree.node D2M8K2.u6033 (nat_lit 12832610) (nat_lit 4065193331) (nat_lit 0) D2M8K2.u6034 from rfl, allE_node, arows6033, irow6035, arows6034]
  all_goals rfl

theorem atot6035 : totK PD2M8K2 D2M8K2.u6035 = [0, 405835448646, 1467319897685, 1440955738309, 302963252856, 6213124392, 0, 0] := by
  rw [show D2M8K2.u6035 = KTree.node D2M8K2.u6033 (nat_lit 12832610) (nat_lit 4065193331) (nat_lit 0) D2M8K2.u6034 from rfl, totK_node, atot6033, atot6034]
  decide +kernel

theorem arows6038 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6038 = true := by
  rw [show D2M8K2.u6038 = KTree.node D2M8K2.u6036 (nat_lit 12839577) (nat_lit 1887745875) (nat_lit 0) D2M8K2.u6037 from rfl, allE_node, arows6036, irow6038, arows6037]
  all_goals rfl

theorem atot6038 : totK PD2M8K2 D2M8K2.u6038 = [0, 0, 780222665869, 1867839372969, 898329563419, 61175805054, 0, 0] := by
  rw [show D2M8K2.u6038 = KTree.node D2M8K2.u6036 (nat_lit 12839577) (nat_lit 1887745875) (nat_lit 0) D2M8K2.u6037 from rfl, totK_node, atot6036, atot6037]
  decide +kernel

theorem arows6044 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6044 = true := by
  rw [show D2M8K2.u6044 = KTree.node D2M8K2.u6042 (nat_lit 12847534) (nat_lit 4051426970) (nat_lit 0) D2M8K2.u6043 from rfl, allE_node, arows6042, irow6044, arows6043]
  all_goals rfl

theorem atot6044 : totK PD2M8K2 D2M8K2.u6044 = [0, 0, 446742349660, 1535376369217, 1327370728798, 229546248959, 5352782441, 0] := by
  rw [show D2M8K2.u6044 = KTree.node D2M8K2.u6042 (nat_lit 12847534) (nat_lit 4051426970) (nat_lit 0) D2M8K2.u6043 from rfl, totK_node, atot6042, atot6043]
  decide +kernel

theorem arows6047 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6047 = true := by
  rw [show D2M8K2.u6047 = KTree.node D2M8K2.u6045 (nat_lit 12851218) (nat_lit 2912266822) (nat_lit 0) D2M8K2.u6046 from rfl, allE_node, arows6045, irow6047, arows6046]
  all_goals rfl

theorem atot6047 : totK PD2M8K2 D2M8K2.u6047 = [0, 0, 513779741579, 1674862918450, 1236636373734, 138903248276, 1271866555, 0] := by
  rw [show D2M8K2.u6047 = KTree.node D2M8K2.u6045 (nat_lit 12851218) (nat_lit 2912266822) (nat_lit 0) D2M8K2.u6046 from rfl, totK_node, atot6045, atot6046]
  decide +kernel

theorem arows6051 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6051 = true := by
  rw [show D2M8K2.u6051 = KTree.node D2M8K2.u6049 (nat_lit 12857049) (nat_lit 1731128826) (nat_lit 0) D2M8K2.u6050 from rfl, allE_node, arows6049, irow6051, arows6050]
  all_goals rfl

theorem atot6051 : totK PD2M8K2 D2M8K2.u6051 = [0, 323576573617, 1326101664717, 1467752901644, 430356142333, 21098116541, 0, 0] := by
  rw [show D2M8K2.u6051 = KTree.node D2M8K2.u6049 (nat_lit 12857049) (nat_lit 1731128826) (nat_lit 0) D2M8K2.u6050 from rfl, totK_node, atot6049, atot6050]
  decide +kernel

theorem arows6054 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6054 = true := by
  rw [show D2M8K2.u6054 = KTree.node D2M8K2.u6052 (nat_lit 12861120) (nat_lit 3195670785) (nat_lit 0) D2M8K2.u6053 from rfl, allE_node, arows6052, irow6054, arows6053]
  all_goals rfl

theorem atot6054 : totK PD2M8K2 D2M8K2.u6054 = [0, 428564893714, 1402935127047, 1347996066933, 418993436644, 29391110695, 0, 0] := by
  rw [show D2M8K2.u6054 = KTree.node D2M8K2.u6052 (nat_lit 12861120) (nat_lit 3195670785) (nat_lit 0) D2M8K2.u6053 from rfl, totK_node, atot6052, atot6053]
  decide +kernel

theorem arows6059 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6059 = true := by
  rw [show D2M8K2.u6059 = KTree.node D2M8K2.u6057 (nat_lit 12863911) (nat_lit 1992885035) (nat_lit 0) D2M8K2.u6058 from rfl, allE_node, arows6057, irow6059, arows6058]
  all_goals rfl

theorem atot6059 : totK PD2M8K2 D2M8K2.u6059 = [0, 415434151704, 1449458448072, 1400183106215, 339917798334, 9264497486, 0, 0] := by
  rw [show D2M8K2.u6059 = KTree.node D2M8K2.u6057 (nat_lit 12863911) (nat_lit 1992885035) (nat_lit 0) D2M8K2.u6058 from rfl, totK_node, atot6057, atot6058]
  decide +kernel

theorem arows6062 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6062 = true := by
  rw [show D2M8K2.u6062 = KTree.node D2M8K2.u6060 (nat_lit 12867650) (nat_lit 4015663094) (nat_lit 0) D2M8K2.u6061 from rfl, allE_node, arows6060, irow6062, arows6061]
  all_goals rfl

theorem atot6062 : totK PD2M8K2 D2M8K2.u6062 = [0, 383541694899, 1402492189278, 1431527528012, 338969769752, 13083481006, 0, 0] := by
  rw [show D2M8K2.u6062 = KTree.node D2M8K2.u6060 (nat_lit 12867650) (nat_lit 4015663094) (nat_lit 0) D2M8K2.u6061 from rfl, totK_node, atot6060, atot6061]
  decide +kernel

theorem arows6066 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6066 = true := by
  rw [show D2M8K2.u6066 = KTree.node D2M8K2.u6064 (nat_lit 12870850) (nat_lit 3239212053) (nat_lit 0) D2M8K2.u6065 from rfl, allE_node, arows6064, irow6066, arows6065]
  all_goals rfl

theorem atot6066 : totK PD2M8K2 D2M8K2.u6066 = [0, 436307283398, 1478395414748, 1352652434821, 309606972718, 13149116973, 0, 0] := by
  rw [show D2M8K2.u6066 = KTree.node D2M8K2.u6064 (nat_lit 12870850) (nat_lit 3239212053) (nat_lit 0) D2M8K2.u6065 from rfl, totK_node, atot6064, atot6065]
  decide +kernel

theorem arows6069 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6069 = true := by
  rw [show D2M8K2.u6069 = KTree.node D2M8K2.u6067 (nat_lit 12878163) (nat_lit 1357512957) (nat_lit 0) D2M8K2.u6068 from rfl, allE_node, arows6067, irow6069, arows6068]
  all_goals rfl

theorem atot6069 : totK PD2M8K2 D2M8K2.u6069 = [0, 0, 819197379011, 1923833303578, 762862227884, 43693204040, 0, 0] := by
  rw [show D2M8K2.u6069 = KTree.node D2M8K2.u6067 (nat_lit 12878163) (nat_lit 1357512957) (nat_lit 0) D2M8K2.u6068 from rfl, totK_node, atot6067, atot6068]
  decide +kernel

theorem arows6076 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6076 = true := by
  rw [show D2M8K2.u6076 = KTree.node D2M8K2.u6074 (nat_lit 12884699) (nat_lit 2230731936) (nat_lit 0) D2M8K2.u6075 from rfl, allE_node, arows6074, irow6076, arows6075]
  all_goals rfl

theorem atot6076 : totK PD2M8K2 D2M8K2.u6076 = [0, 0, 764024053109, 1909358524496, 884888466194, 45143100478, 0, 0] := by
  rw [show D2M8K2.u6076 = KTree.node D2M8K2.u6074 (nat_lit 12884699) (nat_lit 2230731936) (nat_lit 0) D2M8K2.u6075 from rfl, totK_node, atot6074, atot6075]
  decide +kernel

theorem arows6079 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6079 = true := by
  rw [show D2M8K2.u6079 = KTree.node D2M8K2.u6077 (nat_lit 12891460) (nat_lit 3836880707) (nat_lit 0) D2M8K2.u6078 from rfl, allE_node, arows6077, irow6079, arows6078]
  all_goals rfl

theorem atot6079 : totK PD2M8K2 D2M8K2.u6079 = [0, 0, 601657890338, 1796656634830, 1061402108017, 81534660334, 0, 0] := by
  rw [show D2M8K2.u6079 = KTree.node D2M8K2.u6077 (nat_lit 12891460) (nat_lit 3836880707) (nat_lit 0) D2M8K2.u6078 from rfl, totK_node, atot6077, atot6078]
  decide +kernel

theorem arows6083 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6083 = true := by
  rw [show D2M8K2.u6083 = KTree.node D2M8K2.u6081 (nat_lit 12898880) (nat_lit 3063607282) (nat_lit 0) D2M8K2.u6082 from rfl, allE_node, arows6081, irow6083, arows6082]
  all_goals rfl

theorem atot6083 : totK PD2M8K2 D2M8K2.u6083 = [0, 420434840162, 1312478489124, 1244384913920, 528258819864, 101970545355, 1429815836, 0] := by
  rw [show D2M8K2.u6083 = KTree.node D2M8K2.u6081 (nat_lit 12898880) (nat_lit 3063607282) (nat_lit 0) D2M8K2.u6082 from rfl, totK_node, atot6081, atot6082]
  decide +kernel

theorem arows6086 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6086 = true := by
  rw [show D2M8K2.u6086 = KTree.node D2M8K2.u6084 (nat_lit 12902902) (nat_lit 3523201531) (nat_lit 0) D2M8K2.u6085 from rfl, allE_node, arows6084, irow6086, arows6085]
  all_goals rfl

theorem atot6086 : totK PD2M8K2 D2M8K2.u6086 = [0, 335755555786, 1300019085343, 1464851188259, 485052771660, 30675760985, 0, 0] := by
  rw [show D2M8K2.u6086 = KTree.node D2M8K2.u6084 (nat_lit 12902902) (nat_lit 3523201531) (nat_lit 0) D2M8K2.u6085 from rfl, totK_node, atot6084, atot6085]
  decide +kernel

theorem arows6091 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6091 = true := by
  rw [show D2M8K2.u6091 = KTree.node D2M8K2.u6089 (nat_lit 12905914) (nat_lit 3317367956) (nat_lit 0) D2M8K2.u6090 from rfl, allE_node, arows6089, irow6091, arows6090]
  all_goals rfl

theorem atot6091 : totK PD2M8K2 D2M8K2.u6091 = [0, 416742846530, 1444582029266, 1394573624094, 358167808739, 14683973409, 0, 0] := by
  rw [show D2M8K2.u6091 = KTree.node D2M8K2.u6089 (nat_lit 12905914) (nat_lit 3317367956) (nat_lit 0) D2M8K2.u6090 from rfl, totK_node, atot6089, atot6090]
  decide +kernel

theorem arows6094 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6094 = true := by
  rw [show D2M8K2.u6094 = KTree.node D2M8K2.u6092 (nat_lit 12909426) (nat_lit 3451040612) (nat_lit 0) D2M8K2.u6093 from rfl, allE_node, arows6092, irow6094, arows6093]
  all_goals rfl

theorem atot6094 : totK PD2M8K2 D2M8K2.u6094 = [0, 385573486721, 1405195485223, 1457043529097, 353517510684, 10369302704, 0, 0] := by
  rw [show D2M8K2.u6094 = KTree.node D2M8K2.u6092 (nat_lit 12909426) (nat_lit 3451040612) (nat_lit 0) D2M8K2.u6093 from rfl, totK_node, atot6092, atot6093]
  decide +kernel

theorem arows6098 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6098 = true := by
  rw [show D2M8K2.u6098 = KTree.node D2M8K2.u6096 (nat_lit 12916100) (nat_lit 1941034839) (nat_lit 0) D2M8K2.u6097 from rfl, allE_node, arows6096, irow6098, arows6097]
  all_goals rfl

theorem atot6098 : totK PD2M8K2 D2M8K2.u6098 = [0, 440762120087, 1519104511841, 1398189092244, 276462232659, 4909780899, 0, 0] := by
  rw [show D2M8K2.u6098 = KTree.node D2M8K2.u6096 (nat_lit 12916100) (nat_lit 1941034839) (nat_lit 0) D2M8K2.u6097 from rfl, totK_node, atot6096, atot6097]
  decide +kernel

theorem arows6101 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6101 = true := by
  rw [show D2M8K2.u6101 = KTree.node D2M8K2.u6099 (nat_lit 12922322) (nat_lit 4138950161) (nat_lit 0) D2M8K2.u6100 from rfl, allE_node, arows6099, irow6101, arows6100]
  all_goals rfl

theorem atot6101 : totK PD2M8K2 D2M8K2.u6101 = [0, 0, 850247498969, 1891821377430, 812299342252, 51992392475, 0, 0] := by
  rw [show D2M8K2.u6101 = KTree.node D2M8K2.u6099 (nat_lit 12922322) (nat_lit 4138950161) (nat_lit 0) D2M8K2.u6100 from rfl, totK_node, atot6099, atot6100]
  decide +kernel

theorem arows6107 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6107 = true := by
  rw [show D2M8K2.u6107 = KTree.node D2M8K2.u6105 (nat_lit 12926884) (nat_lit 3791399467) (nat_lit 0) D2M8K2.u6106 from rfl, allE_node, arows6105, irow6107, arows6106]
  all_goals rfl

theorem atot6107 : totK PD2M8K2 D2M8K2.u6107 = [0, 0, 493984003417, 1656283198445, 1287077103410, 149985516680, 1323630408, 0] := by
  rw [show D2M8K2.u6107 = KTree.node D2M8K2.u6105 (nat_lit 12926884) (nat_lit 3791399467) (nat_lit 0) D2M8K2.u6106 from rfl, totK_node, atot6105, atot6106]
  decide +kernel

theorem arows6110 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6110 = true := by
  rw [show D2M8K2.u6110 = KTree.node D2M8K2.u6108 (nat_lit 12930944) (nat_lit 3502266183) (nat_lit 0) D2M8K2.u6109 from rfl, allE_node, arows6108, irow6110, arows6109]
  all_goals rfl

theorem atot6110 : totK PD2M8K2 D2M8K2.u6110 = [0, 0, 522420686761, 1657069256303, 1273261607591, 157249741769, 1332468113, 0] := by
  rw [show D2M8K2.u6110 = KTree.node D2M8K2.u6108 (nat_lit 12930944) (nat_lit 3502266183) (nat_lit 0) D2M8K2.u6109 from rfl, totK_node, atot6108, atot6109]
  decide +kernel

theorem arows6114 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6114 = true := by
  rw [show D2M8K2.u6114 = KTree.node D2M8K2.u6112 (nat_lit 12938222) (nat_lit 2496373606) (nat_lit 0) D2M8K2.u6113 from rfl, allE_node, arows6112, irow6114, arows6113]
  all_goals rfl

theorem atot6114 : totK PD2M8K2 D2M8K2.u6114 = [179984371288, 439406052484, 416470648221, 1045469610245, 1195149510118, 275600791882, 9533751846, 0] := by
  rw [show D2M8K2.u6114 = KTree.node D2M8K2.u6112 (nat_lit 12938222) (nat_lit 2496373606) (nat_lit 0) D2M8K2.u6113 from rfl, totK_node, atot6112, atot6113]
  decide +kernel

theorem arows6117 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6117 = true := by
  rw [show D2M8K2.u6117 = KTree.node D2M8K2.u6115 (nat_lit 12941618) (nat_lit 3790225163) (nat_lit 0) D2M8K2.u6116 from rfl, allE_node, arows6115, irow6117, arows6116]
  all_goals rfl

theorem atot6117 : totK PD2M8K2 D2M8K2.u6117 = [486053360805, 1606730605140, 1343366592915, 190686473959, 1369150432, 0, 0, 0] := by
  rw [show D2M8K2.u6117 = KTree.node D2M8K2.u6115 (nat_lit 12941618) (nat_lit 3790225163) (nat_lit 0) D2M8K2.u6116 from rfl, totK_node, atot6115, atot6116]
  decide +kernel

theorem arows6122 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6122 = true := by
  rw [show D2M8K2.u6122 = KTree.node D2M8K2.u6120 (nat_lit 12948521) (nat_lit 1802491271) (nat_lit 0) D2M8K2.u6121 from rfl, allE_node, arows6120, irow6122, arows6121]
  all_goals rfl

theorem atot6122 : totK PD2M8K2 D2M8K2.u6122 = [375573856497, 1434469387415, 1427337491850, 326070276413, 13049727234, 0, 0, 0] := by
  rw [show D2M8K2.u6122 = KTree.node D2M8K2.u6120 (nat_lit 12948521) (nat_lit 1802491271) (nat_lit 0) D2M8K2.u6121 from rfl, totK_node, atot6120, atot6121]
  decide +kernel

theorem arows6125 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6125 = true := by
  rw [show D2M8K2.u6125 = KTree.node D2M8K2.u6123 (nat_lit 12952687) (nat_lit 1665736598) (nat_lit 0) D2M8K2.u6124 from rfl, allE_node, arows6123, irow6125, arows6124]
  all_goals rfl

theorem atot6125 : totK PD2M8K2 D2M8K2.u6125 = [456685425026, 1462087597478, 1303167273094, 302611587850, 13250685261, 0, 0, 0] := by
  rw [show D2M8K2.u6125 = KTree.node D2M8K2.u6123 (nat_lit 12952687) (nat_lit 1665736598) (nat_lit 0) D2M8K2.u6124 from rfl, totK_node, atot6123, atot6124]
  decide +kernel

theorem arows6129 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6129 = true := by
  rw [show D2M8K2.u6129 = KTree.node D2M8K2.u6127 (nat_lit 12956077) (nat_lit 1122376177) (nat_lit 0) D2M8K2.u6128 from rfl, allE_node, arows6127, irow6129, arows6128]
  all_goals rfl

theorem atot6129 : totK PD2M8K2 D2M8K2.u6129 = [412234219416, 1516532037076, 1398314148114, 248048479561, 4980514959, 0, 0, 0] := by
  rw [show D2M8K2.u6129 = KTree.node D2M8K2.u6127 (nat_lit 12956077) (nat_lit 1122376177) (nat_lit 0) D2M8K2.u6128 from rfl, totK_node, atot6127, atot6128]
  decide +kernel

theorem arows6132 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6132 = true := by
  rw [show D2M8K2.u6132 = KTree.node D2M8K2.u6130 (nat_lit 12959376) (nat_lit 2889591294) (nat_lit 0) D2M8K2.u6131 from rfl, allE_node, arows6130, irow6132, arows6131]
  all_goals rfl

theorem atot6132 : totK PD2M8K2 D2M8K2.u6132 = [88521112267, 926291576521, 1783251625327, 711313238374, 40051593738, 0, 0, 0] := by
  rw [show D2M8K2.u6132 = KTree.node D2M8K2.u6130 (nat_lit 12959376) (nat_lit 2889591294) (nat_lit 0) D2M8K2.u6131 from rfl, totK_node, atot6130, atot6131]
  decide +kernel

theorem arows6144 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6144 = true := by
  rw [show D2M8K2.u6144 = KTree.node D2M8K2.u6142 (nat_lit 12962963) (nat_lit 1984829494) (nat_lit 0) D2M8K2.u6143 from rfl, allE_node, arows6142, irow6144, arows6143]
  all_goals rfl

theorem atot6144 : totK PD2M8K2 D2M8K2.u6144 = [0, 493483498227, 1654473977558, 1210120957913, 161482089986, 1369150432, 0, 0] := by
  rw [show D2M8K2.u6144 = KTree.node D2M8K2.u6142 (nat_lit 12962963) (nat_lit 1984829494) (nat_lit 0) D2M8K2.u6143 from rfl, totK_node, atot6142, atot6143]
  decide +kernel

theorem arows6147 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6147 = true := by
  rw [show D2M8K2.u6147 = KTree.node D2M8K2.u6145 (nat_lit 12971869) (nat_lit 1175249342) (nat_lit 0) D2M8K2.u6146 from rfl, allE_node, arows6145, irow6147, arows6146]
  all_goals rfl

theorem atot6147 : totK PD2M8K2 D2M8K2.u6147 = [0, 725073131599, 1869668785120, 891018725791, 51107289371, 0, 0, 0] := by
  rw [show D2M8K2.u6147 = KTree.node D2M8K2.u6145 (nat_lit 12971869) (nat_lit 1175249342) (nat_lit 0) D2M8K2.u6146 from rfl, totK_node, atot6145, atot6146]
  decide +kernel

theorem arows6151 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6151 = true := by
  rw [show D2M8K2.u6151 = KTree.node D2M8K2.u6149 (nat_lit 12978253) (nat_lit 1105918388) (nat_lit 0) D2M8K2.u6150 from rfl, allE_node, arows6149, irow6151, arows6150]
  all_goals rfl

theorem atot6151 : totK PD2M8K2 D2M8K2.u6151 = [249139256659, 1062923852295, 1610262331036, 680051872604, 36001643463, 0, 0, 0] := by
  rw [show D2M8K2.u6151 = KTree.node D2M8K2.u6149 (nat_lit 12978253) (nat_lit 1105918388) (nat_lit 0) D2M8K2.u6150 from rfl, totK_node, atot6149, atot6150]
  decide +kernel

theorem arows6154 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6154 = true := by
  rw [show D2M8K2.u6154 = KTree.node D2M8K2.u6152 (nat_lit 12986606) (nat_lit 3811364628) (nat_lit 0) D2M8K2.u6153 from rfl, allE_node, arows6152, irow6154, arows6153]
  all_goals rfl

theorem atot6154 : totK PD2M8K2 D2M8K2.u6154 = [285935247419, 1212575375304, 1520469945852, 582077109846, 37609398105, 0, 0, 0] := by
  rw [show D2M8K2.u6154 = KTree.node D2M8K2.u6152 (nat_lit 12986606) (nat_lit 3811364628) (nat_lit 0) D2M8K2.u6153 from rfl, totK_node, atot6152, atot6153]
  decide +kernel

theorem arows6159 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6159 = true := by
  rw [show D2M8K2.u6159 = KTree.node D2M8K2.u6157 (nat_lit 12989386) (nat_lit 3859003536) (nat_lit 0) D2M8K2.u6158 from rfl, allE_node, arows6157, irow6159, arows6158]
  all_goals rfl

theorem atot6159 : totK PD2M8K2 D2M8K2.u6159 = [407778892743, 1441055691390, 1441185889063, 335366378178, 13036865798, 0, 0, 0] := by
  rw [show D2M8K2.u6159 = KTree.node D2M8K2.u6157 (nat_lit 12989386) (nat_lit 3859003536) (nat_lit 0) D2M8K2.u6158 from rfl, totK_node, atot6157, atot6158]
  decide +kernel

theorem arows6162 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6162 = true := by
  rw [show D2M8K2.u6162 = KTree.node D2M8K2.u6160 (nat_lit 12993774) (nat_lit 4086215485) (nat_lit 0) D2M8K2.u6161 from rfl, allE_node, arows6160, irow6162, arows6161]
  all_goals rfl

theorem atot6162 : totK PD2M8K2 D2M8K2.u6162 = [451889987231, 1519219075391, 1376033336166, 281941097956, 10698315783, 0, 0, 0] := by
  rw [show D2M8K2.u6162 = KTree.node D2M8K2.u6160 (nat_lit 12993774) (nat_lit 4086215485) (nat_lit 0) D2M8K2.u6161 from rfl, totK_node, atot6160, atot6161]
  decide +kernel

theorem arows6166 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6166 = true := by
  rw [show D2M8K2.u6166 = KTree.node D2M8K2.u6164 (nat_lit 12996916) (nat_lit 4062894510) (nat_lit 0) D2M8K2.u6165 from rfl, allE_node, arows6164, irow6166, arows6165]
  all_goals rfl

theorem atot6166 : totK PD2M8K2 D2M8K2.u6166 = [462728054687, 1556021535986, 1362971778249, 243372723786, 4976872846, 0, 0, 0] := by
  rw [show D2M8K2.u6166 = KTree.node D2M8K2.u6164 (nat_lit 12996916) (nat_lit 4062894510) (nat_lit 0) D2M8K2.u6165 from rfl, totK_node, atot6164, atot6165]
  decide +kernel

theorem arows6169 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6169 = true := by
  rw [show D2M8K2.u6169 = KTree.node D2M8K2.u6167 (nat_lit 13000440) (nat_lit 3448333778) (nat_lit 0) D2M8K2.u6168 from rfl, allE_node, arows6167, irow6169, arows6168]
  all_goals rfl

theorem atot6169 : totK PD2M8K2 D2M8K2.u6169 = [171412815235, 1118311809474, 1676792841801, 610708405491, 43941008531, 0, 0, 0] := by
  rw [show D2M8K2.u6169 = KTree.node D2M8K2.u6167 (nat_lit 13000440) (nat_lit 3448333778) (nat_lit 0) D2M8K2.u6168 from rfl, totK_node, atot6167, atot6168]
  decide +kernel

theorem arows6175 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6175 = true := by
  rw [show D2M8K2.u6175 = KTree.node D2M8K2.u6173 (nat_lit 13007147) (nat_lit 2560184903) (nat_lit 0) D2M8K2.u6174 from rfl, allE_node, arows6173, irow6175, arows6174]
  all_goals rfl

theorem atot6175 : totK PD2M8K2 D2M8K2.u6175 = [0, 278010137228, 1205413338897, 1532669083259, 555000994741, 36921873854, 0, 0] := by
  rw [show D2M8K2.u6175 = KTree.node D2M8K2.u6173 (nat_lit 13007147) (nat_lit 2560184903) (nat_lit 0) D2M8K2.u6174 from rfl, totK_node, atot6173, atot6174]
  decide +kernel

theorem arows6178 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6178 = true := by
  rw [show D2M8K2.u6178 = KTree.node D2M8K2.u6176 (nat_lit 13009906) (nat_lit 3989869592) (nat_lit 0) D2M8K2.u6177 from rfl, allE_node, arows6176, irow6178, arows6177]
  all_goals rfl

theorem atot6178 : totK PD2M8K2 D2M8K2.u6178 = [0, 449633903829, 1548289409577, 1380326459165, 244802375745, 5159868635, 0, 0] := by
  rw [show D2M8K2.u6178 = KTree.node D2M8K2.u6176 (nat_lit 13009906) (nat_lit 3989869592) (nat_lit 0) D2M8K2.u6177 from rfl, totK_node, atot6176, atot6177]
  decide +kernel

theorem arows6182 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6182 = true := by
  rw [show D2M8K2.u6182 = KTree.node D2M8K2.u6180 (nat_lit 13013994) (nat_lit 3785927919) (nat_lit 0) D2M8K2.u6181 from rfl, allE_node, arows6180, irow6182, arows6181]
  all_goals rfl

theorem atot6182 : totK PD2M8K2 D2M8K2.u6182 = [0, 468443831398, 1536200521697, 1350137937912, 259290932758, 5218872685, 0, 0] := by
  rw [show D2M8K2.u6182 = KTree.node D2M8K2.u6180 (nat_lit 13013994) (nat_lit 3785927919) (nat_lit 0) D2M8K2.u6181 from rfl, totK_node, atot6180, atot6181]
  decide +kernel

theorem arows6185 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6185 = true := by
  rw [show D2M8K2.u6185 = KTree.node D2M8K2.u6183 (nat_lit 13017721) (nat_lit 1188192122) (nat_lit 0) D2M8K2.u6184 from rfl, allE_node, arows6183, irow6185, arows6184]
  all_goals rfl

theorem atot6185 : totK PD2M8K2 D2M8K2.u6185 = [0, 468969209221, 1621347127991, 1347102372022, 185598661743, 1415142070, 0, 0] := by
  rw [show D2M8K2.u6185 = KTree.node D2M8K2.u6183 (nat_lit 13017721) (nat_lit 1188192122) (nat_lit 0) D2M8K2.u6184 from rfl, totK_node, atot6183, atot6184]
  decide +kernel

theorem arows6190 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6190 = true := by
  rw [show D2M8K2.u6190 = KTree.node D2M8K2.u6188 (nat_lit 13021437) (nat_lit 965997342) (nat_lit 0) D2M8K2.u6189 from rfl, allE_node, arows6188, irow6190, arows6189]
  all_goals rfl

theorem atot6190 : totK PD2M8K2 D2M8K2.u6190 = [245216813082, 777112438896, 1149940213853, 1108600909792, 291763706461, 9302370699, 0, 0] := by
  rw [show D2M8K2.u6190 = KTree.node D2M8K2.u6188 (nat_lit 13021437) (nat_lit 965997342) (nat_lit 0) D2M8K2.u6189 from rfl, totK_node, atot6188, atot6189]
  decide +kernel

theorem arows6193 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6193 = true := by
  rw [show D2M8K2.u6193 = KTree.node D2M8K2.u6191 (nat_lit 13025133) (nat_lit 1389665779) (nat_lit 0) D2M8K2.u6192 from rfl, allE_node, arows6191, irow6193, arows6192]
  all_goals rfl

theorem atot6193 : totK PD2M8K2 D2M8K2.u6193 = [474726035039, 1593641742839, 1374350771366, 194566168670, 1369150432, 0, 0, 0] := by
  rw [show D2M8K2.u6193 = KTree.node D2M8K2.u6191 (nat_lit 13025133) (nat_lit 1389665779) (nat_lit 0) D2M8K2.u6192 from rfl, totK_node, atot6191, atot6192]
  decide +kernel

theorem arows6197 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6197 = true := by
  rw [show D2M8K2.u6197 = KTree.node D2M8K2.u6195 (nat_lit 13028379) (nat_lit 3638395622) (nat_lit 0) D2M8K2.u6196 from rfl, allE_node, arows6195, irow6197, arows6196]
  all_goals rfl

theorem atot6197 : totK PD2M8K2 D2M8K2.u6197 = [299810186183, 1222703096009, 1497525095005, 582929354595, 37348207948, 0, 0, 0] := by
  rw [show D2M8K2.u6197 = KTree.node D2M8K2.u6195 (nat_lit 13028379) (nat_lit 3638395622) (nat_lit 0) D2M8K2.u6196 from rfl, totK_node, atot6195, atot6196]
  decide +kernel

theorem arows6200 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6200 = true := by
  rw [show D2M8K2.u6200 = KTree.node D2M8K2.u6198 (nat_lit 13031175) (nat_lit 3638030424) (nat_lit 0) D2M8K2.u6199 from rfl, allE_node, arows6198, irow6200, arows6199]
  all_goals rfl

theorem atot6200 : totK PD2M8K2 D2M8K2.u6200 = [405771661075, 1439670387064, 1438972362307, 326042517198, 13049727234, 0, 0, 0] := by
  rw [show D2M8K2.u6200 = KTree.node D2M8K2.u6198 (nat_lit 13031175) (nat_lit 3638030424) (nat_lit 0) D2M8K2.u6199 from rfl, totK_node, atot6198, atot6199]
  decide +kernel

theorem arows6207 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6207 = true := by
  rw [show D2M8K2.u6207 = KTree.node D2M8K2.u6205 (nat_lit 13037904) (nat_lit 3700418224) (nat_lit 0) D2M8K2.u6206 from rfl, allE_node, arows6205, irow6207, arows6206]
  all_goals rfl

theorem atot6207 : totK PD2M8K2 D2M8K2.u6207 = [449308295025, 1535707378829, 1373707955707, 245398049097, 4980514959, 0, 0, 0] := by
  rw [show D2M8K2.u6207 = KTree.node D2M8K2.u6205 (nat_lit 13037904) (nat_lit 3700418224) (nat_lit 0) D2M8K2.u6206 from rfl, totK_node, atot6205, atot6206]
  decide +kernel

theorem arows6210 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6210 = true := by
  rw [show D2M8K2.u6210 = KTree.node D2M8K2.u6208 (nat_lit 13041410) (nat_lit 3237548698) (nat_lit 0) D2M8K2.u6209 from rfl, allE_node, arows6208, irow6210, arows6209]
  all_goals rfl

theorem atot6210 : totK PD2M8K2 D2M8K2.u6210 = [258174440891, 1266071815393, 1607478506570, 458900677627, 21861635611, 0, 0, 0] := by
  rw [show D2M8K2.u6210 = KTree.node D2M8K2.u6208 (nat_lit 13041410) (nat_lit 3237548698) (nat_lit 0) D2M8K2.u6209 from rfl, totK_node, atot6208, atot6209]
  decide +kernel

theorem arows6214 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6214 = true := by
  rw [show D2M8K2.u6214 = KTree.node D2M8K2.u6212 (nat_lit 13044724) (nat_lit 3977858031) (nat_lit 0) D2M8K2.u6213 from rfl, allE_node, arows6212, irow6214, arows6213]
  all_goals rfl

theorem atot6214 : totK PD2M8K2 D2M8K2.u6214 = [0, 488191895881, 1663014374148, 1245741013189, 142107551378, 1206465782, 0, 0] := by
  rw [show D2M8K2.u6214 = KTree.node D2M8K2.u6212 (nat_lit 13044724) (nat_lit 3977858031) (nat_lit 0) D2M8K2.u6213 from rfl, totK_node, atot6212, atot6213]
  decide +kernel

theorem arows6217 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6217 = true := by
  rw [show D2M8K2.u6217 = KTree.node D2M8K2.u6215 (nat_lit 13050171) (nat_lit 3787259967) (nat_lit 0) D2M8K2.u6216 from rfl, allE_node, arows6215, irow6217, arows6216]
  all_goals rfl

theorem atot6217 : totK PD2M8K2 D2M8K2.u6217 = [0, 701991200152, 1891552555692, 978455490839, 64011997164, 0, 0, 0] := by
  rw [show D2M8K2.u6217 = KTree.node D2M8K2.u6215 (nat_lit 13050171) (nat_lit 3787259967) (nat_lit 0) D2M8K2.u6216 from rfl, totK_node, atot6215, atot6216]
  decide +kernel

theorem arows6222 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6222 = true := by
  rw [show D2M8K2.u6222 = KTree.node D2M8K2.u6220 (nat_lit 13056900) (nat_lit 3267676036) (nat_lit 0) D2M8K2.u6221 from rfl, allE_node, arows6220, irow6222, arows6221]
  all_goals rfl

theorem atot6222 : totK PD2M8K2 D2M8K2.u6222 = [0, 417134332862, 1478767061474, 1319014462028, 296883087181, 13016197374, 0, 0] := by
  rw [show D2M8K2.u6222 = KTree.node D2M8K2.u6220 (nat_lit 13056900) (nat_lit 3267676036) (nat_lit 0) D2M8K2.u6221 from rfl, totK_node, atot6220, atot6221]
  decide +kernel

theorem arows6225 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6225 = true := by
  rw [show D2M8K2.u6225 = KTree.node D2M8K2.u6223 (nat_lit 13060585) (nat_lit 984788577) (nat_lit 0) D2M8K2.u6224 from rfl, allE_node, arows6223, irow6225, arows6224]
  all_goals rfl

theorem atot6225 : totK PD2M8K2 D2M8K2.u6225 = [76372199855, 534814010449, 1488601792120, 1244276761912, 192767450308, 4574395652, 0, 0] := by
  rw [show D2M8K2.u6225 = KTree.node D2M8K2.u6223 (nat_lit 13060585) (nat_lit 984788577) (nat_lit 0) D2M8K2.u6224 from rfl, totK_node, atot6223, atot6224]
  decide +kernel

theorem arows6229 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6229 = true := by
  rw [show D2M8K2.u6229 = KTree.node D2M8K2.u6227 (nat_lit 13106868) (nat_lit 3156357768) (nat_lit 0) D2M8K2.u6228 from rfl, allE_node, arows6227, irow6229, arows6228]
  all_goals rfl

theorem atot6229 : totK PD2M8K2 D2M8K2.u6229 = [431361773986, 1567049133642, 1379695978042, 195698870958, 1369150432, 0, 0, 0] := by
  rw [show D2M8K2.u6229 = KTree.node D2M8K2.u6227 (nat_lit 13106868) (nat_lit 3156357768) (nat_lit 0) D2M8K2.u6228 from rfl, totK_node, atot6227, atot6228]
  decide +kernel

theorem arows6232 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6232 = true := by
  rw [show D2M8K2.u6232 = KTree.node D2M8K2.u6230 (nat_lit 13110745) (nat_lit 685443821) (nat_lit 0) D2M8K2.u6231 from rfl, allE_node, arows6230, irow6232, arows6231]
  all_goals rfl

theorem atot6232 : totK PD2M8K2 D2M8K2.u6232 = [313650562615, 1245689012592, 1484160624296, 551904203381, 33004026400, 0, 0, 0] := by
  rw [show D2M8K2.u6232 = KTree.node D2M8K2.u6230 (nat_lit 13110745) (nat_lit 685443821) (nat_lit 0) D2M8K2.u6231 from rfl, totK_node, atot6230, atot6231]
  decide +kernel

theorem arows6238 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6238 = true := by
  rw [show D2M8K2.u6238 = KTree.node D2M8K2.u6236 (nat_lit 13113514) (nat_lit 3933585078) (nat_lit 0) D2M8K2.u6237 from rfl, allE_node, arows6236, irow6238, arows6237]
  all_goals rfl

theorem atot6238 : totK PD2M8K2 D2M8K2.u6238 = [426363809857, 1441096156782, 1378381537931, 337269784073, 17462716779, 0, 0, 0] := by
  rw [show D2M8K2.u6238 = KTree.node D2M8K2.u6236 (nat_lit 13113514) (nat_lit 3933585078) (nat_lit 0) D2M8K2.u6237 from rfl, totK_node, atot6236, atot6237]
  decide +kernel

theorem arows6241 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6241 = true := by
  rw [show D2M8K2.u6241 = KTree.node D2M8K2.u6239 (nat_lit 13116921) (nat_lit 1902210205) (nat_lit 0) D2M8K2.u6240 from rfl, allE_node, arows6239, irow6241, arows6240]
  all_goals rfl

theorem atot6241 : totK PD2M8K2 D2M8K2.u6241 = [429103290613, 1450043339752, 1355662196672, 319262082482, 13250685261, 0, 0, 0] := by
  rw [show D2M8K2.u6241 = KTree.node D2M8K2.u6239 (nat_lit 13116921) (nat_lit 1902210205) (nat_lit 0) D2M8K2.u6240 from rfl, totK_node, atot6239, atot6240]
  decide +kernel

theorem arows6245 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6245 = true := by
  rw [show D2M8K2.u6245 = KTree.node D2M8K2.u6243 (nat_lit 13120763) (nat_lit 2248247038) (nat_lit 0) D2M8K2.u6244 from rfl, allE_node, arows6243, irow6245, arows6244]
  all_goals rfl

theorem atot6245 : totK PD2M8K2 D2M8K2.u6245 = [332401058255, 1406661124931, 1549996449991, 327242805594, 6350335412, 0, 0, 0] := by
  rw [show D2M8K2.u6245 = KTree.node D2M8K2.u6243 (nat_lit 13120763) (nat_lit 2248247038) (nat_lit 0) D2M8K2.u6244 from rfl, totK_node, atot6243, atot6244]
  decide +kernel

theorem arows6248 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6248 = true := by
  rw [show D2M8K2.u6248 = KTree.node D2M8K2.u6246 (nat_lit 13127765) (nat_lit 2043598029) (nat_lit 0) D2M8K2.u6247 from rfl, allE_node, arows6246, irow6248, arows6247]
  all_goals rfl

theorem atot6248 : totK PD2M8K2 D2M8K2.u6248 = [0, 509505333224, 1664962111748, 1195376189428, 138908615155, 1138244013, 0, 0] := by
  rw [show D2M8K2.u6248 = KTree.node D2M8K2.u6246 (nat_lit 13127765) (nat_lit 2043598029) (nat_lit 0) D2M8K2.u6247 from rfl, totK_node, atot6246, atot6247]
  decide +kernel

theorem arows6253 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6253 = true := by
  rw [show D2M8K2.u6253 = KTree.node D2M8K2.u6251 (nat_lit 13133283) (nat_lit 3679096561) (nat_lit 0) D2M8K2.u6252 from rfl, allE_node, arows6251, irow6253, arows6252]
  all_goals rfl

theorem atot6253 : totK PD2M8K2 D2M8K2.u6253 = [0, 756660917265, 1909032204279, 889903392235, 45249087562, 0, 0, 0] := by
  rw [show D2M8K2.u6253 = KTree.node D2M8K2.u6251 (nat_lit 13133283) (nat_lit 3679096561) (nat_lit 0) D2M8K2.u6252 from rfl, totK_node, atot6251, atot6252]
  decide +kernel

theorem arows6256 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6256 = true := by
  rw [show D2M8K2.u6256 = KTree.node D2M8K2.u6254 (nat_lit 13140186) (nat_lit 3432425138) (nat_lit 0) D2M8K2.u6255 from rfl, allE_node, arows6254, irow6256, arows6255]
  all_goals rfl

theorem atot6256 : totK PD2M8K2 D2M8K2.u6256 = [0, 644674386649, 1770386574317, 1033689052056, 110039464627, 1095107716, 0, 0] := by
  rw [show D2M8K2.u6256 = KTree.node D2M8K2.u6254 (nat_lit 13140186) (nat_lit 3432425138) (nat_lit 0) D2M8K2.u6255 from rfl, totK_node, atot6254, atot6255]
  decide +kernel

theorem arows6260 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6260 = true := by
  rw [show D2M8K2.u6260 = KTree.node D2M8K2.u6258 (nat_lit 13147401) (nat_lit 1729010575) (nat_lit 0) D2M8K2.u6259 from rfl, allE_node, arows6258, irow6260, arows6259]
  all_goals rfl

theorem atot6260 : totK PD2M8K2 D2M8K2.u6260 = [407615386080, 1181738483301, 1147826373382, 677558716374, 136458380445, 3882006667, 0, 0] := by
  rw [show D2M8K2.u6260 = KTree.node D2M8K2.u6258 (nat_lit 13147401) (nat_lit 1729010575) (nat_lit 0) D2M8K2.u6259 from rfl, totK_node, atot6258, atot6259]
  decide +kernel

theorem arows6263 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6263 = true := by
  rw [show D2M8K2.u6263 = KTree.node D2M8K2.u6261 (nat_lit 13151026) (nat_lit 3942439521) (nat_lit 0) D2M8K2.u6262 from rfl, allE_node, arows6261, irow6263, arows6262]
  all_goals rfl

theorem atot6263 : totK PD2M8K2 D2M8K2.u6263 = [419077794545, 1524229437492, 1396590209368, 297390706623, 21380039407, 0, 0, 0] := by
  rw [show D2M8K2.u6263 = KTree.node D2M8K2.u6261 (nat_lit 13151026) (nat_lit 3942439521) (nat_lit 0) D2M8K2.u6262 from rfl, totK_node, atot6261, atot6262]
  decide +kernel

theorem arows6271 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6271 = true := by
  rw [show D2M8K2.u6271 = KTree.node D2M8K2.u6269 (nat_lit 13153898) (nat_lit 4091287736) (nat_lit 0) D2M8K2.u6270 from rfl, allE_node, arows6269, irow6271, arows6270]
  all_goals rfl

theorem atot6271 : totK PD2M8K2 D2M8K2.u6271 = [426989175620, 1398183530423, 1375971409495, 414255213542, 16023640966, 0, 0, 0] := by
  rw [show D2M8K2.u6271 = KTree.node D2M8K2.u6269 (nat_lit 13153898) (nat_lit 4091287736) (nat_lit 0) D2M8K2.u6270 from rfl, totK_node, atot6269, atot6270]
  decide +kernel

theorem arows6274 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6274 = true := by
  rw [show D2M8K2.u6274 = KTree.node D2M8K2.u6272 (nat_lit 13157239) (nat_lit 1998019274) (nat_lit 0) D2M8K2.u6273 from rfl, allE_node, arows6272, irow6274, arows6273]
  all_goals rfl

theorem atot6274 : totK PD2M8K2 D2M8K2.u6274 = [326690195400, 1330989616399, 1542283591189, 394189783456, 14241856732, 0, 0, 0] := by
  rw [show D2M8K2.u6274 = KTree.node D2M8K2.u6272 (nat_lit 13157239) (nat_lit 1998019274) (nat_lit 0) D2M8K2.u6273 from rfl, totK_node, atot6272, atot6273]
  decide +kernel

theorem arows6278 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6278 = true := by
  rw [show D2M8K2.u6278 = KTree.node D2M8K2.u6276 (nat_lit 13164614) (nat_lit 3977188800) (nat_lit 0) D2M8K2.u6277 from rfl, allE_node, arows6276, irow6278, arows6277]
  all_goals rfl

theorem atot6278 : totK PD2M8K2 D2M8K2.u6278 = [441844054865, 1538430183821, 1402345526872, 270999317671, 7214193561, 0, 0, 0] := by
  rw [show D2M8K2.u6278 = KTree.node D2M8K2.u6276 (nat_lit 13164614) (nat_lit 3977188800) (nat_lit 0) D2M8K2.u6277 from rfl, totK_node, atot6276, atot6277]
  decide +kernel

theorem arows6281 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6281 = true := by
  rw [show D2M8K2.u6281 = KTree.node D2M8K2.u6279 (nat_lit 13168062) (nat_lit 3153595654) (nat_lit 0) D2M8K2.u6280 from rfl, allE_node, arows6279, irow6281, arows6280]
  all_goals rfl

theorem atot6281 : totK PD2M8K2 D2M8K2.u6281 = [0, 634232354799, 1767131387710, 1023290670047, 108294528766, 1310285577, 0, 0] := by
  rw [show D2M8K2.u6281 = KTree.node D2M8K2.u6279 (nat_lit 13168062) (nat_lit 3153595654) (nat_lit 0) D2M8K2.u6280 from rfl, totK_node, atot6279, atot6280]
  decide +kernel

theorem arows6286 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6286 = true := by
  rw [show D2M8K2.u6286 = KTree.node D2M8K2.u6284 (nat_lit 13171754) (nat_lit 4094523830) (nat_lit 0) D2M8K2.u6285 from rfl, allE_node, arows6284, irow6286, arows6285]
  all_goals rfl

theorem atot6286 : totK PD2M8K2 D2M8K2.u6286 = [0, 590401355753, 1750638490642, 1195059110444, 105719212178, 0, 0, 0] := by
  rw [show D2M8K2.u6286 = KTree.node D2M8K2.u6284 (nat_lit 13171754) (nat_lit 4094523830) (nat_lit 0) D2M8K2.u6285 from rfl, totK_node, atot6284, atot6285]
  decide +kernel

theorem arows6289 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6289 = true := by
  rw [show D2M8K2.u6289 = KTree.node D2M8K2.u6287 (nat_lit 13176337) (nat_lit 1202915508) (nat_lit 0) D2M8K2.u6288 from rfl, allE_node, arows6287, irow6289, arows6288]
  all_goals rfl

theorem atot6289 : totK PD2M8K2 D2M8K2.u6289 = [0, 433266855368, 1533025568394, 1372814419041, 220894780170, 4879840392, 0, 0] := by
  rw [show D2M8K2.u6289 = KTree.node D2M8K2.u6287 (nat_lit 13176337) (nat_lit 1202915508) (nat_lit 0) D2M8K2.u6288 from rfl, totK_node, atot6287, atot6288]
  decide +kernel

theorem arows6293 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6293 = true := by
  rw [show D2M8K2.u6293 = KTree.node D2M8K2.u6291 (nat_lit 13180975) (nat_lit 2426719847) (nat_lit 0) D2M8K2.u6292 from rfl, allE_node, arows6291, irow6293, arows6292]
  all_goals rfl

theorem atot6293 : totK PD2M8K2 D2M8K2.u6293 = [0, 491498846639, 1606149557007, 1289249151397, 208301608742, 4931404646, 0, 0] := by
  rw [show D2M8K2.u6293 = KTree.node D2M8K2.u6291 (nat_lit 13180975) (nat_lit 2426719847) (nat_lit 0) D2M8K2.u6292 from rfl, totK_node, atot6291, atot6292]
  decide +kernel

theorem arows6296 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6296 = true := by
  rw [show D2M8K2.u6296 = KTree.node D2M8K2.u6294 (nat_lit 13187472) (nat_lit 2561297960) (nat_lit 0) D2M8K2.u6295 from rfl, allE_node, arows6294, irow6296, arows6295]
  all_goals rfl

theorem atot6296 : totK PD2M8K2 D2M8K2.u6296 = [0, 369126198275, 1349025415381, 1411125514465, 400221212030, 21751168066, 0, 0] := by
  rw [show D2M8K2.u6296 = KTree.node D2M8K2.u6294 (nat_lit 13187472) (nat_lit 2561297960) (nat_lit 0) D2M8K2.u6295 from rfl, totK_node, atot6294, atot6295]
  decide +kernel

theorem arows6302 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6302 = true := by
  rw [show D2M8K2.u6302 = KTree.node D2M8K2.u6300 (nat_lit 13191044) (nat_lit 3352333383) (nat_lit 0) D2M8K2.u6301 from rfl, allE_node, arows6300, irow6302, arows6301]
  all_goals rfl

theorem atot6302 : totK PD2M8K2 D2M8K2.u6302 = [0, 493411852499, 1617844466101, 1327984713708, 180424936986, 1369150432, 0, 0] := by
  rw [show D2M8K2.u6302 = KTree.node D2M8K2.u6300 (nat_lit 13191044) (nat_lit 3352333383) (nat_lit 0) D2M8K2.u6301 from rfl, totK_node, atot6300, atot6301]
  decide +kernel

theorem arows6305 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6305 = true := by
  rw [show D2M8K2.u6305 = KTree.node D2M8K2.u6303 (nat_lit 13197963) (nat_lit 1790587840) (nat_lit 0) D2M8K2.u6304 from rfl, allE_node, arows6303, irow6305, arows6304]
  all_goals rfl

theorem atot6305 : totK PD2M8K2 D2M8K2.u6305 = [0, 389037799312, 1441682241916, 1390758298417, 310459218567, 13049727234, 0, 0] := by
  rw [show D2M8K2.u6305 = KTree.node D2M8K2.u6303 (nat_lit 13197963) (nat_lit 1790587840) (nat_lit 0) D2M8K2.u6304 from rfl, totK_node, atot6303, atot6304]
  decide +kernel

theorem arows6309 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6309 = true := by
  rw [show D2M8K2.u6309 = KTree.node D2M8K2.u6307 (nat_lit 13202311) (nat_lit 2294401710) (nat_lit 0) D2M8K2.u6308 from rfl, allE_node, arows6307, irow6309, arows6308]
  all_goals rfl

theorem atot6309 : totK PD2M8K2 D2M8K2.u6309 = [0, 426493347107, 1553740210263, 1364933709941, 194888010544, 2294578496, 0, 0] := by
  rw [show D2M8K2.u6309 = KTree.node D2M8K2.u6307 (nat_lit 13202311) (nat_lit 2294401710) (nat_lit 0) D2M8K2.u6308 from rfl, totK_node, atot6307, atot6308]
  decide +kernel

theorem arows6312 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6312 = true := by
  rw [show D2M8K2.u6312 = KTree.node D2M8K2.u6310 (nat_lit 13205935) (nat_lit 2069643196) (nat_lit 0) D2M8K2.u6311 from rfl, allE_node, arows6310, irow6312, arows6311]
  all_goals rfl

theorem atot6312 : totK PD2M8K2 D2M8K2.u6312 = [0, 413133451104, 1499058142142, 1427571050810, 254041644073, 5089503546, 0, 0] := by
  rw [show D2M8K2.u6312 = KTree.node D2M8K2.u6310 (nat_lit 13205935) (nat_lit 2069643196) (nat_lit 0) D2M8K2.u6311 from rfl, totK_node, atot6310, atot6311]
  decide +kernel

theorem arows6317 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6317 = true := by
  rw [show D2M8K2.u6317 = KTree.node D2M8K2.u6315 (nat_lit 13209553) (nat_lit 1533549872) (nat_lit 0) D2M8K2.u6316 from rfl, allE_node, arows6315, irow6317, arows6316]
  all_goals rfl

theorem atot6317 : totK PD2M8K2 D2M8K2.u6317 = [0, 0, 714443166694, 1797342772404, 885418990987, 95029887653, 1275377855, 0] := by
  rw [show D2M8K2.u6317 = KTree.node D2M8K2.u6315 (nat_lit 13209553) (nat_lit 1533549872) (nat_lit 0) D2M8K2.u6316 from rfl, totK_node, atot6315, atot6316]
  decide +kernel

theorem arows6320 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6320 = true := by
  rw [show D2M8K2.u6320 = KTree.node D2M8K2.u6318 (nat_lit 13216525) (nat_lit 1191408568) (nat_lit 0) D2M8K2.u6319 from rfl, allE_node, arows6318, irow6320, arows6319]
  all_goals rfl

theorem atot6320 : totK PD2M8K2 D2M8K2.u6320 = [0, 0, 657252251453, 1834712662312, 922654992465, 62399766365, 0, 0] := by
  rw [show D2M8K2.u6320 = KTree.node D2M8K2.u6318 (nat_lit 13216525) (nat_lit 1191408568) (nat_lit 0) D2M8K2.u6319 from rfl, totK_node, atot6318, atot6319]
  decide +kernel

theorem arows6324 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6324 = true := by
  rw [show D2M8K2.u6324 = KTree.node D2M8K2.u6322 (nat_lit 13223841) (nat_lit 1858652781) (nat_lit 0) D2M8K2.u6323 from rfl, allE_node, arows6322, irow6324, arows6323]
  all_goals rfl

theorem atot6324 : totK PD2M8K2 D2M8K2.u6324 = [0, 0, 896282958503, 1952322544484, 659214221555, 21225507460, 0, 0] := by
  rw [show D2M8K2.u6324 = KTree.node D2M8K2.u6322 (nat_lit 13223841) (nat_lit 1858652781) (nat_lit 0) D2M8K2.u6323 from rfl, totK_node, atot6322, atot6323]
  decide +kernel

theorem arows6327 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6327 = true := by
  rw [show D2M8K2.u6327 = KTree.node D2M8K2.u6325 (nat_lit 13234324) (nat_lit 3426026828) (nat_lit 0) D2M8K2.u6326 from rfl, allE_node, arows6325, irow6327, arows6326]
  all_goals rfl

theorem atot6327 : totK PD2M8K2 D2M8K2.u6327 = [0, 443708700729, 1405637061468, 1352274009583, 439051123820, 34233509477, 0, 0] := by
  rw [show D2M8K2.u6327 = KTree.node D2M8K2.u6325 (nat_lit 13234324) (nat_lit 3426026828) (nat_lit 0) D2M8K2.u6326 from rfl, totK_node, atot6325, atot6326]
  decide +kernel

theorem arows6334 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6334 = true := by
  rw [show D2M8K2.u6334 = KTree.node D2M8K2.u6332 (nat_lit 13237084) (nat_lit 3969568137) (nat_lit 0) D2M8K2.u6333 from rfl, allE_node, arows6332, irow6334, arows6333]
  all_goals rfl

theorem atot6334 : totK PD2M8K2 D2M8K2.u6334 = [0, 426470632228, 1463687373954, 1386081533390, 349471293571, 12125819103, 0, 0] := by
  rw [show D2M8K2.u6334 = KTree.node D2M8K2.u6332 (nat_lit 13237084) (nat_lit 3969568137) (nat_lit 0) D2M8K2.u6333 from rfl, totK_node, atot6332, atot6333]
  decide +kernel

theorem arows6337 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6337 = true := by
  rw [show D2M8K2.u6337 = KTree.node D2M8K2.u6335 (nat_lit 13241071) (nat_lit 2353934900) (nat_lit 0) D2M8K2.u6336 from rfl, allE_node, arows6335, irow6337, arows6336]
  all_goals rfl

theorem atot6337 : totK PD2M8K2 D2M8K2.u6337 = [0, 328169559918, 1329523053917, 1529749968377, 407664720726, 17312036757, 0, 0] := by
  rw [show D2M8K2.u6337 = KTree.node D2M8K2.u6335 (nat_lit 13241071) (nat_lit 2353934900) (nat_lit 0) D2M8K2.u6336 from rfl, totK_node, atot6335, atot6336]
  decide +kernel

theorem arows6341 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6341 = true := by
  rw [show D2M8K2.u6341 = KTree.node D2M8K2.u6339 (nat_lit 13244516) (nat_lit 3309796675) (nat_lit 0) D2M8K2.u6340 from rfl, allE_node, arows6339, irow6341, arows6340]
  all_goals rfl

theorem atot6341 : totK PD2M8K2 D2M8K2.u6341 = [0, 445655816177, 1568617172477, 1384084664444, 224232082835, 3880716147, 0, 0] := by
  rw [show D2M8K2.u6341 = KTree.node D2M8K2.u6339 (nat_lit 13244516) (nat_lit 3309796675) (nat_lit 0) D2M8K2.u6340 from rfl, totK_node, atot6339, atot6340]
  decide +kernel

theorem arows6344 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6344 = true := by
  rw [show D2M8K2.u6344 = KTree.node D2M8K2.u6342 (nat_lit 13248433) (nat_lit 1522759666) (nat_lit 0) D2M8K2.u6343 from rfl, allE_node, arows6342, irow6344, arows6343]
  all_goals rfl

theorem atot6344 : totK PD2M8K2 D2M8K2.u6344 = [0, 381516222605, 1446515849585, 1472174805317, 320413176693, 6216931096, 0, 0] := by
  rw [show D2M8K2.u6344 = KTree.node D2M8K2.u6342 (nat_lit 13248433) (nat_lit 1522759666) (nat_lit 0) D2M8K2.u6343 from rfl, totK_node, atot6342, atot6343]
  decide +kernel

theorem arows6349 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6349 = true := by
  rw [show D2M8K2.u6349 = KTree.node D2M8K2.u6347 (nat_lit 13272498) (nat_lit 3293872654) (nat_lit 0) D2M8K2.u6348 from rfl, allE_node, arows6347, irow6349, arows6348]
  all_goals rfl

theorem atot6349 : totK PD2M8K2 D2M8K2.u6349 = [0, 467640622430, 1534376186756, 1307179523429, 246725860516, 12908700479, 0, 0] := by
  rw [show D2M8K2.u6349 = KTree.node D2M8K2.u6347 (nat_lit 13272498) (nat_lit 3293872654) (nat_lit 0) D2M8K2.u6348 from rfl, totK_node, atot6347, atot6348]
  decide +kernel

theorem arows6352 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6352 = true := by
  rw [show D2M8K2.u6352 = KTree.node D2M8K2.u6350 (nat_lit 13276080) (nat_lit 3550114128) (nat_lit 0) D2M8K2.u6351 from rfl, allE_node, arows6350, irow6352, arows6351]
  all_goals rfl

theorem atot6352 : totK PD2M8K2 D2M8K2.u6352 = [0, 373434484842, 1413256229908, 1448287199942, 399805182923, 19941272494, 0, 0] := by
  rw [show D2M8K2.u6352 = KTree.node D2M8K2.u6350 (nat_lit 13276080) (nat_lit 3550114128) (nat_lit 0) D2M8K2.u6351 from rfl, totK_node, atot6350, atot6351]
  decide +kernel

theorem arows6356 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6356 = true := by
  rw [show D2M8K2.u6356 = KTree.node D2M8K2.u6354 (nat_lit 13279201) (nat_lit 1487679972) (nat_lit 0) D2M8K2.u6355 from rfl, allE_node, arows6354, irow6356, arows6355]
  all_goals rfl

theorem atot6356 : totK PD2M8K2 D2M8K2.u6356 = [0, 446008351477, 1479040746227, 1377844895389, 327191685932, 13735364887, 0, 0] := by
  rw [show D2M8K2.u6356 = KTree.node D2M8K2.u6354 (nat_lit 13279201) (nat_lit 1487679972) (nat_lit 0) D2M8K2.u6355 from rfl, totK_node, atot6354, atot6355]
  decide +kernel

theorem arows6359 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6359 = true := by
  rw [show D2M8K2.u6359 = KTree.node D2M8K2.u6357 (nat_lit 13285684) (nat_lit 3822117226) (nat_lit 0) D2M8K2.u6358 from rfl, allE_node, arows6357, irow6359, arows6358]
  all_goals rfl

theorem atot6359 : totK PD2M8K2 D2M8K2.u6359 = [0, 417900361372, 1526786401704, 1406247602995, 228118537925, 4524940636, 0, 0] := by
  rw [show D2M8K2.u6359 = KTree.node D2M8K2.u6357 (nat_lit 13285684) (nat_lit 3822117226) (nat_lit 0) D2M8K2.u6358 from rfl, totK_node, atot6357, atot6358]
  decide +kernel

theorem arows6365 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6365 = true := by
  rw [show D2M8K2.u6365 = KTree.node D2M8K2.u6363 (nat_lit 13289222) (nat_lit 4109227046) (nat_lit 0) D2M8K2.u6364 from rfl, allE_node, arows6363, irow6365, arows6364]
  all_goals rfl

theorem atot6365 : totK PD2M8K2 D2M8K2.u6365 = [0, 422956155823, 1452696131106, 1403100189945, 308993030049, 8723260559, 0, 0] := by
  rw [show D2M8K2.u6365 = KTree.node D2M8K2.u6363 (nat_lit 13289222) (nat_lit 4109227046) (nat_lit 0) D2M8K2.u6364 from rfl, totK_node, atot6363, atot6364]
  decide +kernel

theorem arows6368 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6368 = true := by
  rw [show D2M8K2.u6368 = KTree.node D2M8K2.u6366 (nat_lit 13292968) (nat_lit 3667198012) (nat_lit 0) D2M8K2.u6367 from rfl, allE_node, arows6366, irow6368, arows6367]
  all_goals rfl

theorem atot6368 : totK PD2M8K2 D2M8K2.u6368 = [0, 0, 552985103264, 1702518547132, 1084029331013, 120734081605, 1206465782, 0] := by
  rw [show D2M8K2.u6368 = KTree.node D2M8K2.u6366 (nat_lit 13292968) (nat_lit 3667198012) (nat_lit 0) D2M8K2.u6367 from rfl, totK_node, atot6366, atot6367]
  decide +kernel

theorem arows6372 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6372 = true := by
  rw [show D2M8K2.u6372 = KTree.node D2M8K2.u6370 (nat_lit 13296826) (nat_lit 3777208117) (nat_lit 0) D2M8K2.u6371 from rfl, allE_node, arows6370, irow6372, arows6371]
  all_goals rfl

theorem atot6372 : totK PD2M8K2 D2M8K2.u6372 = [0, 0, 772117929603, 1889698076474, 879525413941, 62649513560, 0, 0] := by
  rw [show D2M8K2.u6372 = KTree.node D2M8K2.u6370 (nat_lit 13296826) (nat_lit 3777208117) (nat_lit 0) D2M8K2.u6371 from rfl, totK_node, atot6370, atot6371]
  decide +kernel

theorem arows6375 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6375 = true := by
  rw [show D2M8K2.u6375 = KTree.node D2M8K2.u6373 (nat_lit 13301746) (nat_lit 2341676570) (nat_lit 0) D2M8K2.u6374 from rfl, allE_node, arows6373, irow6375, arows6374]
  all_goals rfl

theorem atot6375 : totK PD2M8K2 D2M8K2.u6375 = [0, 0, 408683038324, 1446501018525, 1313594533180, 302081845572, 13016197374, 0] := by
  rw [show D2M8K2.u6375 = KTree.node D2M8K2.u6373 (nat_lit 13301746) (nat_lit 2341676570) (nat_lit 0) D2M8K2.u6374 from rfl, totK_node, atot6373, atot6374]
  decide +kernel

theorem arows6380 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6380 = true := by
  rw [show D2M8K2.u6380 = KTree.node D2M8K2.u6378 (nat_lit 13309064) (nat_lit 3243950824) (nat_lit 0) D2M8K2.u6379 from rfl, allE_node, arows6378, irow6380, arows6379]
  all_goals rfl

theorem atot6380 : totK PD2M8K2 D2M8K2.u6380 = [0, 0, 507272229864, 1613731969349, 1163399981465, 173405728435, 4574395652, 0] := by
  rw [show D2M8K2.u6380 = KTree.node D2M8K2.u6378 (nat_lit 13309064) (nat_lit 3243950824) (nat_lit 0) D2M8K2.u6379 from rfl, totK_node, atot6378, atot6379]
  decide +kernel

theorem arows6383 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6383 = true := by
  rw [show D2M8K2.u6383 = KTree.node D2M8K2.u6381 (nat_lit 13355544) (nat_lit 3603225515) (nat_lit 0) D2M8K2.u6382 from rfl, allE_node, arows6381, irow6383, arows6382]
  all_goals rfl

theorem atot6383 : totK PD2M8K2 D2M8K2.u6383 = [0, 497816364279, 1612582619159, 1269513116214, 175557946929, 6377659709, 0, 0] := by
  rw [show D2M8K2.u6383 = KTree.node D2M8K2.u6381 (nat_lit 13355544) (nat_lit 3603225515) (nat_lit 0) D2M8K2.u6382 from rfl, totK_node, atot6381, atot6382]
  decide +kernel

theorem arows6387 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6387 = true := by
  rw [show D2M8K2.u6387 = KTree.node D2M8K2.u6385 (nat_lit 13359504) (nat_lit 2640877032) (nat_lit 0) D2M8K2.u6386 from rfl, allE_node, arows6385, irow6387, arows6386]
  all_goals rfl

theorem atot6387 : totK PD2M8K2 D2M8K2.u6387 = [0, 398072120101, 1410431465223, 1438161687533, 384576018730, 15013989272, 0, 0] := by
  rw [show D2M8K2.u6387 = KTree.node D2M8K2.u6385 (nat_lit 13359504) (nat_lit 2640877032) (nat_lit 0) D2M8K2.u6386 from rfl, totK_node, atot6385, atot6386]
  decide +kernel

theorem arows6390 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6390 = true := by
  rw [show D2M8K2.u6390 = KTree.node D2M8K2.u6388 (nat_lit 13362511) (nat_lit 1589070771) (nat_lit 0) D2M8K2.u6389 from rfl, allE_node, arows6388, irow6390, arows6389]
  all_goals rfl

theorem atot6390 : totK PD2M8K2 D2M8K2.u6390 = [0, 372993961718, 1428298185853, 1454287973723, 327053613274, 13049727234, 0, 0] := by
  rw [show D2M8K2.u6390 = KTree.node D2M8K2.u6388 (nat_lit 13362511) (nat_lit 1589070771) (nat_lit 0) D2M8K2.u6389 from rfl, totK_node, atot6388, atot6389]
  decide +kernel

theorem arows6399 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6399 = true := by
  rw [show D2M8K2.u6399 = KTree.node D2M8K2.u6397 (nat_lit 13366282) (nat_lit 2161705550) (nat_lit 0) D2M8K2.u6398 from rfl, allE_node, arows6397, irow6399, arows6398]
  all_goals rfl

theorem atot6399 : totK PD2M8K2 D2M8K2.u6399 = [0, 488876611939, 1580606177251, 1292224748502, 208497227863, 4686148432, 0, 0] := by
  rw [show D2M8K2.u6399 = KTree.node D2M8K2.u6397 (nat_lit 13366282) (nat_lit 2161705550) (nat_lit 0) D2M8K2.u6398 from rfl, totK_node, atot6397, atot6398]
  decide +kernel

theorem arows6402 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6402 = true := by
  rw [show D2M8K2.u6402 = KTree.node D2M8K2.u6400 (nat_lit 13369949) (nat_lit 2122359738) (nat_lit 0) D2M8K2.u6401 from rfl, allE_node, arows6400, irow6402, arows6401]
  all_goals rfl

theorem atot6402 : totK PD2M8K2 D2M8K2.u6402 = [0, 245678469189, 1275350966478, 1630806575084, 407064420746, 14720655943, 0, 0] := by
  rw [show D2M8K2.u6402 = KTree.node D2M8K2.u6400 (nat_lit 13369949) (nat_lit 2122359738) (nat_lit 0) D2M8K2.u6401 from rfl, totK_node, atot6400, atot6401]
  decide +kernel

theorem arows6406 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6406 = true := by
  rw [show D2M8K2.u6406 = KTree.node D2M8K2.u6404 (nat_lit 13377678) (nat_lit 3903017956) (nat_lit 0) D2M8K2.u6405 from rfl, allE_node, arows6404, irow6406, arows6405]
  all_goals rfl

theorem atot6406 : totK PD2M8K2 D2M8K2.u6406 = [0, 0, 606574881007, 1758179140900, 1021795885413, 91205659373, 1103454931, 0] := by
  rw [show D2M8K2.u6406 = KTree.node D2M8K2.u6404 (nat_lit 13377678) (nat_lit 3903017956) (nat_lit 0) D2M8K2.u6405 from rfl, totK_node, atot6404, atot6405]
  decide +kernel

theorem arows6409 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6409 = true := by
  rw [show D2M8K2.u6409 = KTree.node D2M8K2.u6407 (nat_lit 13383136) (nat_lit 3756584681) (nat_lit 0) D2M8K2.u6408 from rfl, allE_node, arows6407, irow6409, arows6408]
  all_goals rfl

theorem atot6409 : totK PD2M8K2 D2M8K2.u6409 = [0, 0, 845253735078, 1907988753574, 723598950081, 33285129003, 0, 0] := by
  rw [show D2M8K2.u6409 = KTree.node D2M8K2.u6407 (nat_lit 13383136) (nat_lit 3756584681) (nat_lit 0) D2M8K2.u6408 from rfl, totK_node, atot6407, atot6408]
  decide +kernel

theorem arows6414 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6414 = true := by
  rw [show D2M8K2.u6414 = KTree.node D2M8K2.u6412 (nat_lit 13390410) (nat_lit 1510299383) (nat_lit 0) D2M8K2.u6413 from rfl, allE_node, arows6412, irow6414, arows6413]
  all_goals rfl

theorem atot6414 : totK PD2M8K2 D2M8K2.u6414 = [0, 175895516967, 707947076091, 1363408843044, 1034420294811, 172287691161, 4779662215, 0] := by
  rw [show D2M8K2.u6414 = KTree.node D2M8K2.u6412 (nat_lit 13390410) (nat_lit 1510299383) (nat_lit 0) D2M8K2.u6413 from rfl, totK_node, atot6412, atot6413]
  decide +kernel

theorem arows6417 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6417 = true := by
  rw [show D2M8K2.u6417 = KTree.node D2M8K2.u6415 (nat_lit 13397828) (nat_lit 3261500151) (nat_lit 0) D2M8K2.u6416 from rfl, allE_node, arows6415, irow6417, arows6416]
  all_goals rfl

theorem atot6417 : totK PD2M8K2 D2M8K2.u6417 = [0, 458485678440, 1578909358273, 1372845062769, 184756422689, 1369150432, 0, 0] := by
  rw [show D2M8K2.u6417 = KTree.node D2M8K2.u6415 (nat_lit 13397828) (nat_lit 3261500151) (nat_lit 0) D2M8K2.u6416 from rfl, totK_node, atot6415, atot6416]
  decide +kernel

theorem arows6421 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6421 = true := by
  rw [show D2M8K2.u6421 = KTree.node D2M8K2.u6419 (nat_lit 13401388) (nat_lit 3920258384) (nat_lit 0) D2M8K2.u6420 from rfl, allE_node, arows6419, irow6421, arows6420]
  all_goals rfl

theorem atot6421 : totK PD2M8K2 D2M8K2.u6421 = [0, 340750342271, 1267841759910, 1451925527484, 532240183527, 32762398897, 0, 0] := by
  rw [show D2M8K2.u6421 = KTree.node D2M8K2.u6419 (nat_lit 13401388) (nat_lit 3920258384) (nat_lit 0) D2M8K2.u6420 from rfl, totK_node, atot6419, atot6420]
  decide +kernel

theorem arows6424 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6424 = true := by
  rw [show D2M8K2.u6424 = KTree.node D2M8K2.u6422 (nat_lit 13404246) (nat_lit 3005024420) (nat_lit 0) D2M8K2.u6423 from rfl, allE_node, arows6422, irow6424, arows6423]
  all_goals rfl

theorem atot6424 : totK PD2M8K2 D2M8K2.u6424 = [0, 424393685433, 1512505262652, 1403425610593, 275418896437, 9583672031, 0, 0] := by
  rw [show D2M8K2.u6424 = KTree.node D2M8K2.u6422 (nat_lit 13404246) (nat_lit 3005024420) (nat_lit 0) D2M8K2.u6423 from rfl, totK_node, atot6422, atot6423]
  decide +kernel

theorem arows6430 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6430 = true := by
  rw [show D2M8K2.u6430 = KTree.node D2M8K2.u6428 (nat_lit 13408501) (nat_lit 1255213702) (nat_lit 0) D2M8K2.u6429 from rfl, allE_node, arows6428, irow6430, arows6429]
  all_goals rfl

theorem atot6430 : totK PD2M8K2 D2M8K2.u6430 = [0, 451041003373, 1542416031152, 1383522589790, 252446781902, 5228939780, 0, 0] := by
  rw [show D2M8K2.u6430 = KTree.node D2M8K2.u6428 (nat_lit 13408501) (nat_lit 1255213702) (nat_lit 0) D2M8K2.u6429 from rfl, totK_node, atot6428, atot6429]
  decide +kernel

theorem arows6433 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6433 = true := by
  rw [show D2M8K2.u6433 = KTree.node D2M8K2.u6431 (nat_lit 13415237) (nat_lit 2366851252) (nat_lit 0) D2M8K2.u6432 from rfl, allE_node, arows6431, irow6433, arows6432]
  all_goals rfl

theorem atot6433 : totK PD2M8K2 D2M8K2.u6433 = [193081648232, 621008336196, 1074294749251, 1272140958401, 418426765032, 21982452388, 0, 0] := by
  rw [show D2M8K2.u6433 = KTree.node D2M8K2.u6431 (nat_lit 13415237) (nat_lit 2366851252) (nat_lit 0) D2M8K2.u6432 from rfl, totK_node, atot6431, atot6432]
  decide +kernel

theorem arows6437 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6437 = true := by
  rw [show D2M8K2.u6437 = KTree.node D2M8K2.u6435 (nat_lit 13936995) (nat_lit 3242104416) (nat_lit 0) D2M8K2.u6436 from rfl, allE_node, arows6435, irow6437, arows6436]
  all_goals rfl

theorem atot6437 : totK PD2M8K2 D2M8K2.u6437 = [488003464808, 1608491075995, 1325815719912, 188197790390, 1369150432, 0, 0, 0] := by
  rw [show D2M8K2.u6437 = KTree.node D2M8K2.u6435 (nat_lit 13936995) (nat_lit 3242104416) (nat_lit 0) D2M8K2.u6436 from rfl, totK_node, atot6435, atot6436]
  decide +kernel

theorem arows6440 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6440 = true := by
  rw [show D2M8K2.u6440 = KTree.node D2M8K2.u6438 (nat_lit 13943930) (nat_lit 3772051039) (nat_lit 0) D2M8K2.u6439 from rfl, allE_node, arows6438, irow6440, arows6439]
  all_goals rfl

theorem atot6440 : totK PD2M8K2 D2M8K2.u6440 = [394877528264, 1424055191965, 1414788335773, 329328272327, 13049727234, 0, 0, 0] := by
  rw [show D2M8K2.u6440 = KTree.node D2M8K2.u6438 (nat_lit 13943930) (nat_lit 3772051039) (nat_lit 0) D2M8K2.u6439 from rfl, totK_node, atot6438, atot6439]
  decide +kernel

theorem arows6445 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6445 = true := by
  rw [show D2M8K2.u6445 = KTree.node D2M8K2.u6443 (nat_lit 13947729) (nat_lit 1404783079) (nat_lit 0) D2M8K2.u6444 from rfl, allE_node, arows6443, irow6445, arows6444]
  all_goals rfl

theorem atot6445 : totK PD2M8K2 D2M8K2.u6445 = [395912297647, 1412663238699, 1396442153382, 331094494158, 13250685261, 0, 0, 0] := by
  rw [show D2M8K2.u6445 = KTree.node D2M8K2.u6443 (nat_lit 13947729) (nat_lit 1404783079) (nat_lit 0) D2M8K2.u6444 from rfl, totK_node, atot6443, atot6444]
  decide +kernel

theorem arows6448 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6448 = true := by
  rw [show D2M8K2.u6448 = KTree.node D2M8K2.u6446 (nat_lit 13951017) (nat_lit 1826954158) (nat_lit 0) D2M8K2.u6447 from rfl, allE_node, arows6446, irow6448, arows6447]
  all_goals rfl

theorem atot6448 : totK PD2M8K2 D2M8K2.u6448 = [425520072451, 1527472999180, 1379935556125, 238777679265, 4980514959, 0, 0, 0] := by
  rw [show D2M8K2.u6448 = KTree.node D2M8K2.u6446 (nat_lit 13951017) (nat_lit 1826954158) (nat_lit 0) D2M8K2.u6447 from rfl, totK_node, atot6446, atot6447]
  decide +kernel

theorem arows6452 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6452 = true := by
  rw [show D2M8K2.u6452 = KTree.node D2M8K2.u6450 (nat_lit 13955191) (nat_lit 1787442217) (nat_lit 0) D2M8K2.u6451 from rfl, allE_node, arows6450, irow6452, arows6451]
  all_goals rfl

theorem atot6452 : totK PD2M8K2 D2M8K2.u6452 = [76459986009, 893767239831, 1795550992157, 726737624451, 41132877050, 0, 0, 0] := by
  rw [show D2M8K2.u6452 = KTree.node D2M8K2.u6450 (nat_lit 13955191) (nat_lit 1787442217) (nat_lit 0) D2M8K2.u6451 from rfl, totK_node, atot6450, atot6451]
  decide +kernel

theorem arows6455 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6455 = true := by
  rw [show D2M8K2.u6455 = KTree.node D2M8K2.u6453 (nat_lit 13962251) (nat_lit 2911071882) (nat_lit 0) D2M8K2.u6454 from rfl, allE_node, arows6453, irow6455, arows6454]
  all_goals rfl

theorem atot6455 : totK PD2M8K2 D2M8K2.u6455 = [0, 494499530088, 1646008236939, 1212334967875, 163108868223, 1369150432, 0, 0] := by
  rw [show D2M8K2.u6455 = KTree.node D2M8K2.u6453 (nat_lit 13962251) (nat_lit 2911071882) (nat_lit 0) D2M8K2.u6454 from rfl, totK_node, atot6453, atot6454]
  decide +kernel

theorem arows6462 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6462 = true := by
  rw [show D2M8K2.u6462 = KTree.node D2M8K2.u6460 (nat_lit 13967219) (nat_lit 2899928239) (nat_lit 0) D2M8K2.u6461 from rfl, allE_node, arows6460, irow6462, arows6461]
  all_goals rfl

theorem atot6462 : totK PD2M8K2 D2M8K2.u6462 = [0, 707577949698, 1855372441939, 916407790223, 53562853746, 0, 0, 0] := by
  rw [show D2M8K2.u6462 = KTree.node D2M8K2.u6460 (nat_lit 13967219) (nat_lit 2899928239) (nat_lit 0) D2M8K2.u6461 from rfl, totK_node, atot6460, atot6461]
  decide +kernel

theorem arows6465 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6465 = true := by
  rw [show D2M8K2.u6465 = KTree.node D2M8K2.u6463 (nat_lit 13974184) (nat_lit 3809354571) (nat_lit 0) D2M8K2.u6464 from rfl, allE_node, arows6463, irow6465, arows6464]
  all_goals rfl

theorem atot6465 : totK PD2M8K2 D2M8K2.u6465 = [338449428671, 1217951265149, 1500892757390, 546316703173, 28128401517, 0, 0, 0] := by
  rw [show D2M8K2.u6465 = KTree.node D2M8K2.u6463 (nat_lit 13974184) (nat_lit 3809354571) (nat_lit 0) D2M8K2.u6464 from rfl, totK_node, atot6463, atot6464]
  decide +kernel

theorem arows6469 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6469 = true := by
  rw [show D2M8K2.u6469 = KTree.node D2M8K2.u6467 (nat_lit 13982250) (nat_lit 3850059356) (nat_lit 0) D2M8K2.u6468 from rfl, allE_node, arows6467, irow6469, arows6468]
  all_goals rfl

theorem atot6469 : totK PD2M8K2 D2M8K2.u6469 = [274929489656, 1189084943440, 1555949588362, 594806615965, 37609398105, 0, 0, 0] := by
  rw [show D2M8K2.u6469 = KTree.node D2M8K2.u6467 (nat_lit 13982250) (nat_lit 3850059356) (nat_lit 0) D2M8K2.u6468 from rfl, totK_node, atot6467, atot6468]
  decide +kernel

theorem arows6472 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6472 = true := by
  rw [show D2M8K2.u6472 = KTree.node D2M8K2.u6470 (nat_lit 13985280) (nat_lit 3656280539) (nat_lit 0) D2M8K2.u6471 from rfl, allE_node, arows6470, irow6472, arows6471]
  all_goals rfl

theorem atot6472 : totK PD2M8K2 D2M8K2.u6472 = [392257707870, 1436687541285, 1441874754130, 333550820556, 13036865798, 0, 0, 0] := by
  rw [show D2M8K2.u6472 = KTree.node D2M8K2.u6470 (nat_lit 13985280) (nat_lit 3656280539) (nat_lit 0) D2M8K2.u6471 from rfl, totK_node, atot6470, atot6471]
  decide +kernel

theorem arows6477 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6477 = true := by
  rw [show D2M8K2.u6477 = KTree.node D2M8K2.u6475 (nat_lit 13989106) (nat_lit 3959079341) (nat_lit 0) D2M8K2.u6476 from rfl, allE_node, arows6475, irow6477, arows6476]
  all_goals rfl

theorem atot6477 : totK PD2M8K2 D2M8K2.u6477 = [424911020254, 1459608816694, 1382298517148, 329190936575, 13237669976, 0, 0, 0] := by
  rw [show D2M8K2.u6477 = KTree.node D2M8K2.u6475 (nat_lit 13989106) (nat_lit 3959079341) (nat_lit 0) D2M8K2.u6476 from rfl, totK_node, atot6475, atot6476]
  decide +kernel

theorem arows6480 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6480 = true := by
  rw [show D2M8K2.u6480 = KTree.node D2M8K2.u6478 (nat_lit 13992218) (nat_lit 4203815236) (nat_lit 0) D2M8K2.u6479 from rfl, allE_node, arows6478, irow6480, arows6479]
  all_goals rfl

theorem atot6480 : totK PD2M8K2 D2M8K2.u6480 = [424394139179, 1526405296889, 1421191111354, 252556343556, 4976872846, 0, 0, 0] := by
  rw [show D2M8K2.u6480 = KTree.node D2M8K2.u6478 (nat_lit 13992218) (nat_lit 4203815236) (nat_lit 0) D2M8K2.u6479 from rfl, totK_node, atot6478, atot6479]
  decide +kernel

theorem arows6484 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6484 = true := by
  rw [show D2M8K2.u6484 = KTree.node D2M8K2.u6482 (nat_lit 13996568) (nat_lit 2790056810) (nat_lit 0) D2M8K2.u6483 from rfl, allE_node, arows6482, irow6484, arows6483]
  all_goals rfl

theorem atot6484 : totK PD2M8K2 D2M8K2.u6484 = [132249069452, 1010449405432, 1714666037170, 739431454316, 54497627329, 0, 0, 0] := by
  rw [show D2M8K2.u6484 = KTree.node D2M8K2.u6482 (nat_lit 13996568) (nat_lit 2790056810) (nat_lit 0) D2M8K2.u6483 from rfl, totK_node, atot6482, atot6483]
  decide +kernel

theorem arows6487 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6487 = true := by
  rw [show D2M8K2.u6487 = KTree.node D2M8K2.u6485 (nat_lit 14002946) (nat_lit 4027104210) (nat_lit 0) D2M8K2.u6486 from rfl, allE_node, arows6485, irow6487, arows6486]
  all_goals rfl

theorem atot6487 : totK PD2M8K2 D2M8K2.u6487 = [0, 293823875390, 1213942040326, 1510404579424, 560656765529, 36921873854, 0, 0] := by
  rw [show D2M8K2.u6487 = KTree.node D2M8K2.u6485 (nat_lit 14002946) (nat_lit 4027104210) (nat_lit 0) D2M8K2.u6486 from rfl, totK_node, atot6485, atot6486]
  decide +kernel

theorem arows6493 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6493 = true := by
  rw [show D2M8K2.u6493 = KTree.node D2M8K2.u6491 (nat_lit 14006056) (nat_lit 3888878535) (nat_lit 0) D2M8K2.u6492 from rfl, allE_node, arows6491, irow6493, arows6492]
  all_goals rfl

theorem atot6493 : totK PD2M8K2 D2M8K2.u6493 = [0, 456701254896, 1531884665361, 1379736711457, 248775998393, 5159868635, 0, 0] := by
  rw [show D2M8K2.u6493 = KTree.node D2M8K2.u6491 (nat_lit 14006056) (nat_lit 3888878535) (nat_lit 0) D2M8K2.u6492 from rfl, totK_node, atot6491, atot6492]
  decide +kernel

theorem arows6496 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6496 = true := by
  rw [show D2M8K2.u6496 = KTree.node D2M8K2.u6494 (nat_lit 14010021) (nat_lit 1105167837) (nat_lit 0) D2M8K2.u6495 from rfl, allE_node, arows6494, irow6496, arows6495]
  all_goals rfl

theorem atot6496 : totK PD2M8K2 D2M8K2.u6496 = [0, 429758140431, 1525623286012, 1373733061454, 255666366941, 5218872685, 0, 0] := by
  rw [show D2M8K2.u6496 = KTree.node D2M8K2.u6494 (nat_lit 14010021) (nat_lit 1105167837) (nat_lit 0) D2M8K2.u6495 from rfl, totK_node, atot6494, atot6495]
  decide +kernel

theorem arows6500 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6500 = true := by
  rw [show D2M8K2.u6500 = KTree.node D2M8K2.u6498 (nat_lit 14013526) (nat_lit 1625881735) (nat_lit 0) D2M8K2.u6499 from rfl, allE_node, arows6498, irow6500, arows6499]
  all_goals rfl

theorem atot6500 : totK PD2M8K2 D2M8K2.u6500 = [0, 503818102154, 1618496336000, 1341821569751, 183166209382, 1415142070, 0, 0] := by
  rw [show D2M8K2.u6500 = KTree.node D2M8K2.u6498 (nat_lit 14013526) (nat_lit 1625881735) (nat_lit 0) D2M8K2.u6499 from rfl, totK_node, atot6498, atot6499]
  decide +kernel

theorem arows6503 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6503 = true := by
  rw [show D2M8K2.u6503 = KTree.node D2M8K2.u6501 (nat_lit 14017663) (nat_lit 2211991322) (nat_lit 0) D2M8K2.u6502 from rfl, allE_node, arows6501, irow6503, arows6502]
  all_goals rfl

theorem atot6503 : totK PD2M8K2 D2M8K2.u6503 = [407232325195, 1042398509285, 954048478389, 883629174579, 277291679837, 9302370699, 0, 0] := by
  rw [show D2M8K2.u6503 = KTree.node D2M8K2.u6501 (nat_lit 14017663) (nat_lit 2211991322) (nat_lit 0) D2M8K2.u6502 from rfl, totK_node, atot6501, atot6502]
  decide +kernel

theorem arows6508 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6508 = true := by
  rw [show D2M8K2.u6508 = KTree.node D2M8K2.u6506 (nat_lit 14021584) (nat_lit 3422012555) (nat_lit 0) D2M8K2.u6507 from rfl, allE_node, arows6506, irow6508, arows6507]
  all_goals rfl

theorem atot6508 : totK PD2M8K2 D2M8K2.u6508 = [418498508285, 1566327971082, 1441826594762, 217485416947, 1369150432, 0, 0, 0] := by
  rw [show D2M8K2.u6508 = KTree.node D2M8K2.u6506 (nat_lit 14021584) (nat_lit 3422012555) (nat_lit 0) D2M8K2.u6507 from rfl, totK_node, atot6506, atot6507]
  decide +kernel

theorem arows6511 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6511 = true := by
  rw [show D2M8K2.u6511 = KTree.node D2M8K2.u6509 (nat_lit 14024435) (nat_lit 2961873652) (nat_lit 0) D2M8K2.u6510 from rfl, allE_node, arows6509, irow6511, arows6510]
  all_goals rfl

theorem atot6511 : totK PD2M8K2 D2M8K2.u6511 = [373504498661, 1260228598789, 1408323720346, 558853194855, 37413887388, 0, 0, 0] := by
  rw [show D2M8K2.u6511 = KTree.node D2M8K2.u6509 (nat_lit 14024435) (nat_lit 2961873652) (nat_lit 0) D2M8K2.u6510 from rfl, totK_node, atot6509, atot6510]
  decide +kernel

theorem arows6515 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6515 = true := by
  rw [show D2M8K2.u6515 = KTree.node D2M8K2.u6513 (nat_lit 14027571) (nat_lit 2313191336) (nat_lit 0) D2M8K2.u6514 from rfl, allE_node, arows6513, irow6515, arows6514]
  all_goals rfl

theorem atot6515 : totK PD2M8K2 D2M8K2.u6515 = [399889094924, 1429601672467, 1444818803515, 335002510418, 13049727234, 0, 0, 0] := by
  rw [show D2M8K2.u6515 = KTree.node D2M8K2.u6513 (nat_lit 14027571) (nat_lit 2313191336) (nat_lit 0) D2M8K2.u6514 from rfl, totK_node, atot6513, atot6514]
  decide +kernel

theorem arows6518 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6518 = true := by
  rw [show D2M8K2.u6518 = KTree.node D2M8K2.u6516 (nat_lit 14034336) (nat_lit 3528398759) (nat_lit 0) D2M8K2.u6517 from rfl, allE_node, arows6516, irow6518, arows6517]
  all_goals rfl

theorem atot6518 : totK PD2M8K2 D2M8K2.u6518 = [437333645756, 1537405203896, 1406247978669, 247176669912, 4980514959, 0, 0, 0] := by
  rw [show D2M8K2.u6518 = KTree.node D2M8K2.u6516 (nat_lit 14034336) (nat_lit 3528398759) (nat_lit 0) D2M8K2.u6517 from rfl, totK_node, atot6516, atot6517]
  decide +kernel

theorem arows6526 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6526 = true := by
  rw [show D2M8K2.u6526 = KTree.node D2M8K2.u6524 (nat_lit 14038389) (nat_lit 1723910427) (nat_lit 0) D2M8K2.u6525 from rfl, allE_node, arows6524, irow6526, arows6525]
  all_goals rfl

theorem atot6526 : totK PD2M8K2 D2M8K2.u6526 = [0, 804801763731, 1907661917127, 798002494801, 41879330265, 0, 0, 0] := by
  rw [show D2M8K2.u6526 = KTree.node D2M8K2.u6524 (nat_lit 14038389) (nat_lit 1723910427) (nat_lit 0) D2M8K2.u6525 from rfl, totK_node, atot6524, atot6525]
  decide +kernel

theorem arows6529 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6529 = true := by
  rw [show D2M8K2.u6529 = KTree.node D2M8K2.u6527 (nat_lit 14042416) (nat_lit 3448478989) (nat_lit 0) D2M8K2.u6528 from rfl, allE_node, arows6527, irow6529, arows6528]
  all_goals rfl

theorem atot6529 : totK PD2M8K2 D2M8K2.u6529 = [0, 518154487173, 1670290735206, 1241710643002, 143864295929, 1206465782, 0, 0] := by
  rw [show D2M8K2.u6529 = KTree.node D2M8K2.u6527 (nat_lit 14042416) (nat_lit 3448478989) (nat_lit 0) D2M8K2.u6528 from rfl, totK_node, atot6527, atot6528]
  decide +kernel

theorem arows6533 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6533 = true := by
  rw [show D2M8K2.u6533 = KTree.node D2M8K2.u6531 (nat_lit 14046976) (nat_lit 3735058750) (nat_lit 0) D2M8K2.u6532 from rfl, allE_node, arows6531, irow6533, arows6532]
  all_goals rfl

theorem atot6533 : totK PD2M8K2 D2M8K2.u6533 = [0, 417214161972, 1463684737246, 1352364987162, 307057040313, 13016197374, 0, 0] := by
  rw [show D2M8K2.u6533 = KTree.node D2M8K2.u6531 (nat_lit 14046976) (nat_lit 3735058750) (nat_lit 0) D2M8K2.u6532 from rfl, totK_node, atot6531, atot6532]
  decide +kernel

theorem arows6536 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6536 = true := by
  rw [show D2M8K2.u6536 = KTree.node D2M8K2.u6534 (nat_lit 14053837) (nat_lit 1361732872) (nat_lit 0) D2M8K2.u6535 from rfl, allE_node, arows6534, irow6536, arows6535]
  all_goals rfl

theorem atot6536 : totK PD2M8K2 D2M8K2.u6536 = [0, 471238294517, 1618002856617, 1246032691210, 177039489383, 4574395652, 0, 0] := by
  rw [show D2M8K2.u6536 = KTree.node D2M8K2.u6534 (nat_lit 14053837) (nat_lit 1361732872) (nat_lit 0) D2M8K2.u6535 from rfl, totK_node, atot6534, atot6535]
  decide +kernel

theorem arows6541 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6541 = true := by
  rw [show D2M8K2.u6541 = KTree.node D2M8K2.u6539 (nat_lit 14059736) (nat_lit 3459323288) (nat_lit 0) D2M8K2.u6540 from rfl, allE_node, arows6539, irow6541, arows6540]
  all_goals rfl

theorem atot6541 : totK PD2M8K2 D2M8K2.u6541 = [395471379465, 1322189192757, 1337775997982, 492587468105, 40146508159, 0, 0, 0] := by
  rw [show D2M8K2.u6541 = KTree.node D2M8K2.u6539 (nat_lit 14059736) (nat_lit 3459323288) (nat_lit 0) D2M8K2.u6540 from rfl, totK_node, atot6539, atot6540]
  decide +kernel

theorem arows6544 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6544 = true := by
  rw [show D2M8K2.u6544 = KTree.node D2M8K2.u6542 (nat_lit 14063430) (nat_lit 3872665113) (nat_lit 0) D2M8K2.u6543 from rfl, allE_node, arows6542, irow6544, arows6543]
  all_goals rfl

theorem atot6544 : totK PD2M8K2 D2M8K2.u6544 = [407209572491, 1498433511071, 1417843378103, 317906880314, 21383147344, 0, 0, 0] := by
  rw [show D2M8K2.u6544 = KTree.node D2M8K2.u6542 (nat_lit 14063430) (nat_lit 3872665113) (nat_lit 0) D2M8K2.u6543 from rfl, totK_node, atot6542, atot6543]
  decide +kernel

theorem arows6548 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6548 = true := by
  rw [show D2M8K2.u6548 = KTree.node D2M8K2.u6546 (nat_lit 14069765) (nat_lit 2109993808) (nat_lit 0) D2M8K2.u6547 from rfl, allE_node, arows6546, irow6548, arows6547]
  all_goals rfl

theorem atot6548 : totK PD2M8K2 D2M8K2.u6548 = [425945519996, 1419293607095, 1364564483716, 399139113829, 16179348042, 0, 0, 0] := by
  rw [show D2M8K2.u6548 = KTree.node D2M8K2.u6546 (nat_lit 14069765) (nat_lit 2109993808) (nat_lit 0) D2M8K2.u6547 from rfl, totK_node, atot6546, atot6547]
  decide +kernel

theorem arows6551 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6551 = true := by
  rw [show D2M8K2.u6551 = KTree.node D2M8K2.u6549 (nat_lit 14073100) (nat_lit 2648025678) (nat_lit 0) D2M8K2.u6550 from rfl, allE_node, arows6549, irow6551, arows6550]
  all_goals rfl

theorem atot6551 : totK PD2M8K2 D2M8K2.u6551 = [423317413309, 1452374435990, 1376892270484, 329949019170, 13250685261, 0, 0, 0] := by
  rw [show D2M8K2.u6551 = KTree.node D2M8K2.u6549 (nat_lit 14073100) (nat_lit 2648025678) (nat_lit 0) D2M8K2.u6550 from rfl, totK_node, atot6549, atot6550]
  decide +kernel

theorem arows6557 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6557 = true := by
  rw [show D2M8K2.u6557 = KTree.node D2M8K2.u6555 (nat_lit 14080331) (nat_lit 2812413324) (nat_lit 0) D2M8K2.u6556 from rfl, allE_node, arows6555, irow6557, arows6556]
  all_goals rfl

theorem atot6557 : totK PD2M8K2 D2M8K2.u6557 = [0, 777681819256, 1857107242059, 816209473118, 72458416088, 1239866073, 0, 0] := by
  rw [show D2M8K2.u6557 = KTree.node D2M8K2.u6555 (nat_lit 14080331) (nat_lit 2812413324) (nat_lit 0) D2M8K2.u6556 from rfl, totK_node, atot6555, atot6556]
  decide +kernel

theorem arows6560 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6560 = true := by
  rw [show D2M8K2.u6560 = KTree.node D2M8K2.u6558 (nat_lit 14084155) (nat_lit 2241415799) (nat_lit 0) D2M8K2.u6559 from rfl, allE_node, arows6558, irow6560, arows6559]
  all_goals rfl

theorem atot6560 : totK PD2M8K2 D2M8K2.u6560 = [0, 577247529935, 1738234955494, 1178315845332, 115217909580, 0, 0, 0] := by
  rw [show D2M8K2.u6560 = KTree.node D2M8K2.u6558 (nat_lit 14084155) (nat_lit 2241415799) (nat_lit 0) D2M8K2.u6559 from rfl, totK_node, atot6558, atot6559]
  decide +kernel

theorem arows6564 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6564 = true := by
  rw [show D2M8K2.u6564 = KTree.node D2M8K2.u6562 (nat_lit 14092185) (nat_lit 1393455115) (nat_lit 0) D2M8K2.u6563 from rfl, allE_node, arows6562, irow6564, arows6563]
  all_goals rfl

theorem atot6564 : totK PD2M8K2 D2M8K2.u6564 = [0, 422667235035, 1445751823242, 1343815739871, 305782495373, 13105450397, 0, 0] := by
  rw [show D2M8K2.u6564 = KTree.node D2M8K2.u6562 (nat_lit 14092185) (nat_lit 1393455115) (nat_lit 0) D2M8K2.u6563 from rfl, totK_node, atot6562, atot6563]
  decide +kernel

theorem arows6567 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6567 = true := by
  rw [show D2M8K2.u6567 = KTree.node D2M8K2.u6565 (nat_lit 14095629) (nat_lit 1430083073) (nat_lit 0) D2M8K2.u6566 from rfl, allE_node, arows6565, irow6567, arows6566]
  all_goals rfl

theorem atot6567 : totK PD2M8K2 D2M8K2.u6567 = [190180602404, 706290614637, 1326845262899, 1114006793306, 181633526053, 4720618446, 0, 0] := by
  rw [show D2M8K2.u6567 = KTree.node D2M8K2.u6565 (nat_lit 14095629) (nat_lit 1430083073) (nat_lit 0) D2M8K2.u6566 from rfl, totK_node, atot6565, atot6566]
  decide +kernel

theorem arows6572 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6572 = true := by
  rw [show D2M8K2.u6572 = KTree.node D2M8K2.u6570 (nat_lit 14102917) (nat_lit 1269757787) (nat_lit 0) D2M8K2.u6571 from rfl, allE_node, arows6570, irow6572, arows6571]
  all_goals rfl

theorem atot6572 : totK PD2M8K2 D2M8K2.u6572 = [470018962355, 1574830774544, 1343606473213, 194441203904, 1369150432, 0, 0, 0] := by
  rw [show D2M8K2.u6572 = KTree.node D2M8K2.u6570 (nat_lit 14102917) (nat_lit 1269757787) (nat_lit 0) D2M8K2.u6571 from rfl, totK_node, atot6570, atot6571]
  decide +kernel

theorem arows6575 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6575 = true := by
  rw [show D2M8K2.u6575 = KTree.node D2M8K2.u6573 (nat_lit 14106417) (nat_lit 1548520032) (nat_lit 0) D2M8K2.u6574 from rfl, allE_node, arows6573, irow6575, arows6574]
  all_goals rfl

theorem atot6575 : totK PD2M8K2 D2M8K2.u6575 = [305736514452, 1218056251814, 1472081628980, 571393705262, 37410486329, 0, 0, 0] := by
  rw [show D2M8K2.u6575 = KTree.node D2M8K2.u6573 (nat_lit 14106417) (nat_lit 1548520032) (nat_lit 0) D2M8K2.u6574 from rfl, totK_node, atot6573, atot6574]
  decide +kernel

theorem arows6579 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6579 = true := by
  rw [show D2M8K2.u6579 = KTree.node D2M8K2.u6577 (nat_lit 14109257) (nat_lit 1613280225) (nat_lit 0) D2M8K2.u6578 from rfl, allE_node, arows6577, irow6579, arows6578]
  all_goals rfl

theorem atot6579 : totK PD2M8K2 D2M8K2.u6579 = [370290975329, 1420587275228, 1446033756794, 333183228181, 13049727234, 0, 0, 0] := by
  rw [show D2M8K2.u6579 = KTree.node D2M8K2.u6577 (nat_lit 14109257) (nat_lit 1613280225) (nat_lit 0) D2M8K2.u6578 from rfl, totK_node, atot6577, atot6578]
  decide +kernel

theorem arows6582 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6582 = true := by
  rw [show D2M8K2.u6582 = KTree.node D2M8K2.u6580 (nat_lit 14112692) (nat_lit 3521211270) (nat_lit 0) D2M8K2.u6581 from rfl, allE_node, arows6580, irow6582, arows6581]
  all_goals rfl

theorem atot6582 : totK PD2M8K2 D2M8K2.u6582 = [404518943274, 1419334709384, 1396075926555, 332061189351, 13250685261, 0, 0, 0] := by
  rw [show D2M8K2.u6582 = KTree.node D2M8K2.u6580 (nat_lit 14112692) (nat_lit 3521211270) (nat_lit 0) D2M8K2.u6581 from rfl, totK_node, atot6580, atot6581]
  decide +kernel

theorem arows6589 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6589 = true := by
  rw [show D2M8K2.u6589 = KTree.node D2M8K2.u6587 (nat_lit 14115717) (nat_lit 1726220677) (nat_lit 0) D2M8K2.u6588 from rfl, allE_node, arows6587, irow6589, arows6588]
  all_goals rfl

theorem atot6589 : totK PD2M8K2 D2M8K2.u6589 = [357800183586, 1458647521458, 1530711418703, 301359011362, 6350335412, 0, 0, 0] := by
  rw [show D2M8K2.u6589 = KTree.node D2M8K2.u6587 (nat_lit 14115717) (nat_lit 1726220677) (nat_lit 0) D2M8K2.u6588 from rfl, totK_node, atot6587, atot6588]
  decide +kernel

theorem arows6592 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6592 = true := by
  rw [show D2M8K2.u6592 = KTree.node D2M8K2.u6590 (nat_lit 14123035) (nat_lit 2011960157) (nat_lit 0) D2M8K2.u6591 from rfl, allE_node, arows6590, irow6592, arows6591]
  all_goals rfl

theorem atot6592 : totK PD2M8K2 D2M8K2.u6592 = [0, 500693634399, 1684324661219, 1183918744057, 132820087328, 1138244013, 0, 0] := by
  rw [show D2M8K2.u6592 = KTree.node D2M8K2.u6590 (nat_lit 14123035) (nat_lit 2011960157) (nat_lit 0) D2M8K2.u6591 from rfl, totK_node, atot6590, atot6591]
  decide +kernel

theorem arows6596 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6596 = true := by
  rw [show D2M8K2.u6596 = KTree.node D2M8K2.u6594 (nat_lit 14128514) (nat_lit 4107375869) (nat_lit 0) D2M8K2.u6595 from rfl, allE_node, arows6594, irow6596, arows6595]
  all_goals rfl

theorem atot6596 : totK PD2M8K2 D2M8K2.u6596 = [0, 744100507174, 1888587946495, 895380168698, 51556853389, 0, 0, 0] := by
  rw [show D2M8K2.u6596 = KTree.node D2M8K2.u6594 (nat_lit 14128514) (nat_lit 4107375869) (nat_lit 0) D2M8K2.u6595 from rfl, totK_node, atot6594, atot6595]
  decide +kernel

theorem arows6599 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6599 = true := by
  rw [show D2M8K2.u6599 = KTree.node D2M8K2.u6597 (nat_lit 14135138) (nat_lit 3293782265) (nat_lit 0) D2M8K2.u6598 from rfl, allE_node, arows6597, irow6599, arows6598]
  all_goals rfl

theorem atot6599 : totK PD2M8K2 D2M8K2.u6599 = [0, 758748870675, 1871843573881, 905160275206, 58570118748, 0, 0, 0] := by
  rw [show D2M8K2.u6599 = KTree.node D2M8K2.u6597 (nat_lit 14135138) (nat_lit 3293782265) (nat_lit 0) D2M8K2.u6598 from rfl, totK_node, atot6597, atot6598]
  decide +kernel

theorem arows6604 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6604 = true := by
  rw [show D2M8K2.u6604 = KTree.node D2M8K2.u6602 (nat_lit 14183540) (nat_lit 3652605966) (nat_lit 0) D2M8K2.u6603 from rfl, allE_node, arows6602, irow6604, arows6603]
  all_goals rfl

theorem atot6604 : totK PD2M8K2 D2M8K2.u6604 = [0, 432369260669, 1585816522575, 1293450969565, 215863232374, 4977114383, 0, 0] := by
  rw [show D2M8K2.u6604 = KTree.node D2M8K2.u6602 (nat_lit 14183540) (nat_lit 3652605966) (nat_lit 0) D2M8K2.u6603 from rfl, totK_node, atot6602, atot6603]
  decide +kernel

theorem arows6607 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6607 = true := by
  rw [show D2M8K2.u6607 = KTree.node D2M8K2.u6605 (nat_lit 14190585) (nat_lit 1863757960) (nat_lit 0) D2M8K2.u6606 from rfl, allE_node, arows6605, irow6607, arows6606]
  all_goals rfl

theorem atot6607 : totK PD2M8K2 D2M8K2.u6607 = [0, 412248602064, 1572372166944, 1418778638092, 191497192195, 1369150432, 0, 0] := by
  rw [show D2M8K2.u6607 = KTree.node D2M8K2.u6605 (nat_lit 14190585) (nat_lit 1863757960) (nat_lit 0) D2M8K2.u6606 from rfl, totK_node, atot6605, atot6606]
  decide +kernel

theorem arows6611 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6611 = true := by
  rw [show D2M8K2.u6611 = KTree.node D2M8K2.u6609 (nat_lit 14194037) (nat_lit 2096901921) (nat_lit 0) D2M8K2.u6610 from rfl, allE_node, arows6609, irow6611, arows6610]
  all_goals rfl

theorem atot6611 : totK PD2M8K2 D2M8K2.u6611 = [0, 379257568760, 1403821570796, 1429048388711, 313534807747, 14181523188, 0, 0] := by
  rw [show D2M8K2.u6611 = KTree.node D2M8K2.u6609 (nat_lit 14194037) (nat_lit 2096901921) (nat_lit 0) D2M8K2.u6610 from rfl, totK_node, atot6609, atot6610]
  decide +kernel

theorem arows6614 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6614 = true := by
  rw [show D2M8K2.u6614 = KTree.node D2M8K2.u6612 (nat_lit 14197635) (nat_lit 3699985893) (nat_lit 0) D2M8K2.u6613 from rfl, allE_node, arows6612, irow6614, arows6613]
  all_goals rfl

theorem atot6614 : totK PD2M8K2 D2M8K2.u6614 = [0, 419246213715, 1442874311255, 1357480485217, 303979088377, 13082749112, 0, 0] := by
  rw [show D2M8K2.u6614 = KTree.node D2M8K2.u6612 (nat_lit 14197635) (nat_lit 3699985893) (nat_lit 0) D2M8K2.u6613 from rfl, totK_node, atot6612, atot6613]
  decide +kernel

theorem arows6620 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6620 = true := by
  rw [show D2M8K2.u6620 = KTree.node D2M8K2.u6618 (nat_lit 14201432) (nat_lit 3213956562) (nat_lit 0) D2M8K2.u6619 from rfl, allE_node, arows6618, irow6620, arows6619]
  all_goals rfl

theorem atot6620 : totK PD2M8K2 D2M8K2.u6620 = [0, 325571517576, 1426740961159, 1543731996749, 282807540675, 5152749158, 0, 0] := by
  rw [show D2M8K2.u6620 = KTree.node D2M8K2.u6618 (nat_lit 14201432) (nat_lit 3213956562) (nat_lit 0) D2M8K2.u6619 from rfl, totK_node, atot6618, atot6619]
  decide +kernel

theorem arows6623 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6623 = true := by
  rw [show D2M8K2.u6623 = KTree.node D2M8K2.u6621 (nat_lit 14205601) (nat_lit 1562614071) (nat_lit 0) D2M8K2.u6622 from rfl, allE_node, arows6621, irow6623, arows6622]
  all_goals rfl

theorem atot6623 : totK PD2M8K2 D2M8K2.u6623 = [0, 0, 560865519080, 1743308340374, 1026550193010, 110892860290, 1209030869, 0] := by
  rw [show D2M8K2.u6623 = KTree.node D2M8K2.u6621 (nat_lit 14205601) (nat_lit 1562614071) (nat_lit 0) D2M8K2.u6622 from rfl, totK_node, atot6621, atot6622]
  decide +kernel

theorem arows6627 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6627 = true := by
  rw [show D2M8K2.u6627 = KTree.node D2M8K2.u6625 (nat_lit 14215399) (nat_lit 2396299761) (nat_lit 0) D2M8K2.u6626 from rfl, allE_node, arows6625, irow6627, arows6626]
  all_goals rfl

theorem atot6627 : totK PD2M8K2 D2M8K2.u6627 = [0, 0, 887064832625, 1928123856890, 682594979333, 28572672040, 0, 0] := by
  rw [show D2M8K2.u6627 = KTree.node D2M8K2.u6625 (nat_lit 14215399) (nat_lit 2396299761) (nat_lit 0) D2M8K2.u6626 from rfl, totK_node, atot6625, atot6626]
  decide +kernel

theorem arows6630 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6630 = true := by
  rw [show D2M8K2.u6630 = KTree.node D2M8K2.u6628 (nat_lit 14222377) (nat_lit 1497769138) (nat_lit 0) D2M8K2.u6629 from rfl, allE_node, arows6628, irow6630, arows6629]
  all_goals rfl

theorem atot6630 : totK PD2M8K2 D2M8K2.u6630 = [0, 301804903204, 1277225162524, 1551540108762, 443340970641, 21916172627, 0, 0] := by
  rw [show D2M8K2.u6630 = KTree.node D2M8K2.u6628 (nat_lit 14222377) (nat_lit 1497769138) (nat_lit 0) D2M8K2.u6629 from rfl, totK_node, atot6628, atot6629]
  decide +kernel

theorem arows6635 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6635 = true := by
  rw [show D2M8K2.u6635 = KTree.node D2M8K2.u6633 (nat_lit 14231029) (nat_lit 1195141849) (nat_lit 0) D2M8K2.u6634 from rfl, allE_node, arows6633, irow6635, arows6634]
  all_goals rfl

theorem atot6635 : totK PD2M8K2 D2M8K2.u6635 = [0, 297430332530, 1217534622591, 1512845076738, 580256794610, 37498978443, 0, 0] := by
  rw [show D2M8K2.u6635 = KTree.node D2M8K2.u6633 (nat_lit 14231029) (nat_lit 1195141849) (nat_lit 0) D2M8K2.u6634 from rfl, totK_node, atot6633, atot6634]
  decide +kernel

theorem arows6638 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6638 = true := by
  rw [show D2M8K2.u6638 = KTree.node D2M8K2.u6636 (nat_lit 14234121) (nat_lit 1781978565) (nat_lit 0) D2M8K2.u6637 from rfl, allE_node, arows6636, irow6638, arows6637]
  all_goals rfl

theorem atot6638 : totK PD2M8K2 D2M8K2.u6638 = [0, 419115253154, 1487350396869, 1415724097476, 287675337623, 11873025674, 0, 0] := by
  rw [show D2M8K2.u6638 = KTree.node D2M8K2.u6636 (nat_lit 14234121) (nat_lit 1781978565) (nat_lit 0) D2M8K2.u6637 from rfl, totK_node, atot6636, atot6637]
  decide +kernel

theorem arows6642 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6642 = true := by
  rw [show D2M8K2.u6642 = KTree.node D2M8K2.u6640 (nat_lit 14238004) (nat_lit 1157755498) (nat_lit 0) D2M8K2.u6641 from rfl, allE_node, arows6640, irow6642, arows6641]
  all_goals rfl

theorem atot6642 : totK PD2M8K2 D2M8K2.u6642 = [0, 464797766992, 1518436336340, 1341368090895, 285298158296, 12040273252, 0, 0] := by
  rw [show D2M8K2.u6642 = KTree.node D2M8K2.u6640 (nat_lit 14238004) (nat_lit 1157755498) (nat_lit 0) D2M8K2.u6641 from rfl, totK_node, atot6640, atot6641]
  decide +kernel

theorem arows6645 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6645 = true := by
  rw [show D2M8K2.u6645 = KTree.node D2M8K2.u6643 (nat_lit 14241352) (nat_lit 3085972138) (nat_lit 0) D2M8K2.u6644 from rfl, allE_node, arows6643, irow6645, arows6644]
  all_goals rfl

theorem atot6645 : totK PD2M8K2 D2M8K2.u6645 = [0, 419883005751, 1581989878821, 1415778175886, 214575300450, 3880716147, 0, 0] := by
  rw [show D2M8K2.u6645 = KTree.node D2M8K2.u6643 (nat_lit 14241352) (nat_lit 3085972138) (nat_lit 0) D2M8K2.u6644 from rfl, totK_node, atot6643, atot6644]
  decide +kernel

theorem arows6655 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6655 = true := by
  rw [show D2M8K2.u6655 = KTree.node D2M8K2.u6653 (nat_lit 14245630) (nat_lit 3902226121) (nat_lit 0) D2M8K2.u6654 from rfl, allE_node, arows6653, irow6655, arows6654]
  all_goals rfl

theorem atot6655 : totK PD2M8K2 D2M8K2.u6655 = [0, 491073242718, 1497649000783, 1286549371935, 303351923038, 9730542555, 0, 0] := by
  rw [show D2M8K2.u6655 = KTree.node D2M8K2.u6653 (nat_lit 14245630) (nat_lit 3902226121) (nat_lit 0) D2M8K2.u6654 from rfl, totK_node, atot6653, atot6654]
  decide +kernel

theorem arows6658 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6658 = true := by
  rw [show D2M8K2.u6658 = KTree.node D2M8K2.u6656 (nat_lit 14270330) (nat_lit 4116241310) (nat_lit 0) D2M8K2.u6657 from rfl, allE_node, arows6656, irow6658, arows6657]
  all_goals rfl

theorem atot6658 : totK PD2M8K2 D2M8K2.u6658 = [0, 418030884682, 1593607649173, 1429401305711, 191825193802, 1310166938, 0, 0] := by
  rw [show D2M8K2.u6658 = KTree.node D2M8K2.u6656 (nat_lit 14270330) (nat_lit 4116241310) (nat_lit 0) D2M8K2.u6657 from rfl, totK_node, atot6656, atot6657]
  decide +kernel

theorem arows6662 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6662 = true := by
  rw [show D2M8K2.u6662 = KTree.node D2M8K2.u6660 (nat_lit 14273411) (nat_lit 2962100531) (nat_lit 0) D2M8K2.u6661 from rfl, allE_node, arows6660, irow6662, arows6661]
  all_goals rfl

theorem atot6662 : totK PD2M8K2 D2M8K2.u6662 = [0, 440344122106, 1450588249725, 1384443588313, 370374982522, 15013989272, 0, 0] := by
  rw [show D2M8K2.u6662 = KTree.node D2M8K2.u6660 (nat_lit 14273411) (nat_lit 2962100531) (nat_lit 0) D2M8K2.u6661 from rfl, totK_node, atot6660, atot6661]
  decide +kernel

theorem arows6665 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6665 = true := by
  rw [show D2M8K2.u6665 = KTree.node D2M8K2.u6663 (nat_lit 14276580) (nat_lit 3161088557) (nat_lit 0) D2M8K2.u6664 from rfl, allE_node, arows6663, irow6665, arows6664]
  all_goals rfl

theorem atot6665 : totK PD2M8K2 D2M8K2.u6665 = [0, 367583770567, 1403522707801, 1475988013533, 334069832792, 13049727234, 0, 0] := by
  rw [show D2M8K2.u6665 = KTree.node D2M8K2.u6663 (nat_lit 14276580) (nat_lit 3161088557) (nat_lit 0) D2M8K2.u6664 from rfl, totK_node, atot6663, atot6664]
  decide +kernel

theorem arows6670 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6670 = true := by
  rw [show D2M8K2.u6670 = KTree.node D2M8K2.u6668 (nat_lit 14283670) (nat_lit 3553329980) (nat_lit 0) D2M8K2.u6669 from rfl, allE_node, arows6668, irow6670, arows6669]
  all_goals rfl

theorem atot6670 : totK PD2M8K2 D2M8K2.u6670 = [0, 396425170794, 1524928258766, 1447114191015, 249623587825, 4980514959, 0, 0] := by
  rw [show D2M8K2.u6670 = KTree.node D2M8K2.u6668 (nat_lit 14283670) (nat_lit 3553329980) (nat_lit 0) D2M8K2.u6669 from rfl, totK_node, atot6668, atot6669]
  decide +kernel

theorem arows6673 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6673 = true := by
  rw [show D2M8K2.u6673 = KTree.node D2M8K2.u6671 (nat_lit 14308662) (nat_lit 2709339794) (nat_lit 0) D2M8K2.u6672 from rfl, allE_node, arows6671, irow6673, arows6672]
  all_goals rfl

theorem atot6673 : totK PD2M8K2 D2M8K2.u6673 = [0, 394198768217, 1444721217037, 1408627859112, 286579946693, 6191412344, 0, 0] := by
  rw [show D2M8K2.u6673 = KTree.node D2M8K2.u6671 (nat_lit 14308662) (nat_lit 2709339794) (nat_lit 0) D2M8K2.u6672 from rfl, totK_node, atot6671, atot6672]
  decide +kernel

theorem arows6677 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6677 = true := by
  rw [show D2M8K2.u6677 = KTree.node D2M8K2.u6675 (nat_lit 14312376) (nat_lit 3325214047) (nat_lit 0) D2M8K2.u6676 from rfl, allE_node, arows6675, irow6677, arows6676]
  all_goals rfl

theorem atot6677 : totK PD2M8K2 D2M8K2.u6677 = [0, 406679889658, 1535426092226, 1459536550190, 265683980614, 9654694938, 0, 0] := by
  rw [show D2M8K2.u6677 = KTree.node D2M8K2.u6675 (nat_lit 14312376) (nat_lit 3325214047) (nat_lit 0) D2M8K2.u6676 from rfl, totK_node, atot6675, atot6676]
  decide +kernel

theorem arows6680 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6680 = true := by
  rw [show D2M8K2.u6680 = KTree.node D2M8K2.u6678 (nat_lit 14319189) (nat_lit 1734347021) (nat_lit 0) D2M8K2.u6679 from rfl, allE_node, arows6678, irow6680, arows6679]
  all_goals rfl

theorem atot6680 : totK PD2M8K2 D2M8K2.u6680 = [0, 425319435262, 1472376659754, 1399136500443, 315126775923, 6590388537, 0, 0] := by
  rw [show D2M8K2.u6680 = KTree.node D2M8K2.u6678 (nat_lit 14319189) (nat_lit 1734347021) (nat_lit 0) D2M8K2.u6679 from rfl, totK_node, atot6678, atot6679]
  decide +kernel

theorem arows6686 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6686 = true := by
  rw [show D2M8K2.u6686 = KTree.node D2M8K2.u6684 (nat_lit 14322252) (nat_lit 3409983838) (nat_lit 0) D2M8K2.u6685 from rfl, allE_node, arows6684, irow6686, arows6685]
  all_goals rfl

theorem atot6686 : totK PD2M8K2 D2M8K2.u6686 = [0, 421785132785, 1443365872000, 1372809757352, 314354844225, 13088430220, 0, 0] := by
  rw [show D2M8K2.u6686 = KTree.node D2M8K2.u6684 (nat_lit 14322252) (nat_lit 3409983838) (nat_lit 0) D2M8K2.u6685 from rfl, totK_node, atot6684, atot6685]
  decide +kernel

theorem arows6689 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6689 = true := by
  rw [show D2M8K2.u6689 = KTree.node D2M8K2.u6687 (nat_lit 14350267) (nat_lit 2242977437) (nat_lit 0) D2M8K2.u6688 from rfl, allE_node, arows6687, irow6689, arows6688]
  all_goals rfl

theorem atot6689 : totK PD2M8K2 D2M8K2.u6689 = [0, 410144626012, 1503558488155, 1379224730683, 237453591536, 5210657474, 0, 0] := by
  rw [show D2M8K2.u6689 = KTree.node D2M8K2.u6687 (nat_lit 14350267) (nat_lit 2242977437) (nat_lit 0) D2M8K2.u6688 from rfl, totK_node, atot6687, atot6688]
  decide +kernel

theorem arows6693 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6693 = true := by
  rw [show D2M8K2.u6693 = KTree.node D2M8K2.u6691 (nat_lit 14353868) (nat_lit 3178873547) (nat_lit 0) D2M8K2.u6692 from rfl, allE_node, arows6691, irow6693, arows6692]
  all_goals rfl

theorem atot6693 : totK PD2M8K2 D2M8K2.u6693 = [0, 421755028760, 1477851708297, 1381690004265, 312565554102, 18317572719, 0, 0] := by
  rw [show D2M8K2.u6693 = KTree.node D2M8K2.u6691 (nat_lit 14353868) (nat_lit 3178873547) (nat_lit 0) D2M8K2.u6692 from rfl, totK_node, atot6691, atot6692]
  decide +kernel

theorem arows6696 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6696 = true := by
  rw [show D2M8K2.u6696 = KTree.node D2M8K2.u6694 (nat_lit 14356812) (nat_lit 3563894132) (nat_lit 0) D2M8K2.u6695 from rfl, allE_node, arows6694, irow6696, arows6695]
  all_goals rfl

theorem atot6696 : totK PD2M8K2 D2M8K2.u6696 = [0, 419852695886, 1464969500060, 1407630112833, 299547867920, 6522524465, 0, 0] := by
  rw [show D2M8K2.u6696 = KTree.node D2M8K2.u6694 (nat_lit 14356812) (nat_lit 3563894132) (nat_lit 0) D2M8K2.u6695 from rfl, totK_node, atot6694, atot6695]
  decide +kernel

theorem arows6701 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6701 = true := by
  rw [show D2M8K2.u6701 = KTree.node D2M8K2.u6699 (nat_lit 14360224) (nat_lit 3118554472) (nat_lit 0) D2M8K2.u6700 from rfl, allE_node, arows6699, irow6701, arows6700]
  all_goals rfl

theorem atot6701 : totK PD2M8K2 D2M8K2.u6701 = [0, 399677335881, 1425200974381, 1402089718860, 303400279326, 12943032596, 0, 0] := by
  rw [show D2M8K2.u6701 = KTree.node D2M8K2.u6699 (nat_lit 14360224) (nat_lit 3118554472) (nat_lit 0) D2M8K2.u6700 from rfl, totK_node, atot6699, atot6700]
  decide +kernel

theorem arows6704 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6704 = true := by
  rw [show D2M8K2.u6704 = KTree.node D2M8K2.u6702 (nat_lit 14363685) (nat_lit 1406107179) (nat_lit 0) D2M8K2.u6703 from rfl, allE_node, arows6702, irow6704, arows6703]
  all_goals rfl

theorem atot6704 : totK PD2M8K2 D2M8K2.u6704 = [0, 443484686597, 1479092133076, 1358424675865, 300835569302, 13043838850, 0, 0] := by
  rw [show D2M8K2.u6704 = KTree.node D2M8K2.u6702 (nat_lit 14363685) (nat_lit 1406107179) (nat_lit 0) D2M8K2.u6703 from rfl, totK_node, atot6702, atot6703]
  decide +kernel

theorem arows6708 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6708 = true := by
  rw [show D2M8K2.u6708 = KTree.node D2M8K2.u6706 (nat_lit 14370880) (nat_lit 3248582128) (nat_lit 0) D2M8K2.u6707 from rfl, allE_node, arows6706, irow6708, arows6707]
  all_goals rfl

theorem atot6708 : totK PD2M8K2 D2M8K2.u6708 = [0, 0, 720121578569, 1803565530445, 862122871136, 91635655053, 1138244013, 0] := by
  rw [show D2M8K2.u6708 = KTree.node D2M8K2.u6706 (nat_lit 14370880) (nat_lit 3248582128) (nat_lit 0) D2M8K2.u6707 from rfl, totK_node, atot6706, atot6707]
  decide +kernel

theorem arows6711 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6711 = true := by
  rw [show D2M8K2.u6711 = KTree.node D2M8K2.u6709 (nat_lit 14374709) (nat_lit 2375522777) (nat_lit 0) D2M8K2.u6710 from rfl, allE_node, arows6709, irow6711, arows6710]
  all_goals rfl

theorem atot6711 : totK PD2M8K2 D2M8K2.u6711 = [0, 0, 711286750514, 1851982658404, 909470595705, 66320614543, 0, 0] := by
  rw [show D2M8K2.u6711 = KTree.node D2M8K2.u6709 (nat_lit 14374709) (nat_lit 2375522777) (nat_lit 0) D2M8K2.u6710 from rfl, totK_node, atot6709, atot6710]
  decide +kernel

theorem arows6718 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6718 = true := by
  rw [show D2M8K2.u6718 = KTree.node D2M8K2.u6716 (nat_lit 14381600) (nat_lit 3817447700) (nat_lit 0) D2M8K2.u6717 from rfl, allE_node, arows6716, irow6718, arows6717]
  all_goals rfl

theorem atot6718 : totK PD2M8K2 D2M8K2.u6718 = [0, 0, 783987512145, 1882081104929, 813610763956, 51197708874, 0, 0] := by
  rw [show D2M8K2.u6718 = KTree.node D2M8K2.u6716 (nat_lit 14381600) (nat_lit 3817447700) (nat_lit 0) D2M8K2.u6717 from rfl, totK_node, atot6716, atot6717]
  decide +kernel

theorem arows6721 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6721 = true := by
  rw [show D2M8K2.u6721 = KTree.node D2M8K2.u6719 (nat_lit 14386586) (nat_lit 3451550394) (nat_lit 0) D2M8K2.u6720 from rfl, allE_node, arows6719, irow6721, arows6720]
  all_goals rfl

theorem atot6721 : totK PD2M8K2 D2M8K2.u6721 = [306235076213, 721791207661, 484784035905, 871952350649, 942331958291, 200225505474, 4977114383, 0] := by
  rw [show D2M8K2.u6721 = KTree.node D2M8K2.u6719 (nat_lit 14386586) (nat_lit 3451550394) (nat_lit 0) D2M8K2.u6720 from rfl, totK_node, atot6719, atot6720]
  decide +kernel

theorem arows6725 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6725 = true := by
  rw [show D2M8K2.u6725 = KTree.node D2M8K2.u6723 (nat_lit 14435238) (nat_lit 3782644040) (nat_lit 0) D2M8K2.u6724 from rfl, allE_node, arows6723, irow6725, arows6724]
  all_goals rfl

theorem atot6725 : totK PD2M8K2 D2M8K2.u6725 = [453764522136, 1607467778623, 1361999784984, 190161190386, 1369150432, 0, 0, 0] := by
  rw [show D2M8K2.u6725 = KTree.node D2M8K2.u6723 (nat_lit 14435238) (nat_lit 3782644040) (nat_lit 0) D2M8K2.u6724 from rfl, totK_node, atot6723, atot6724]
  decide +kernel

theorem arows6728 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6728 = true := by
  rw [show D2M8K2.u6728 = KTree.node D2M8K2.u6726 (nat_lit 14442219) (nat_lit 2386551541) (nat_lit 0) D2M8K2.u6727 from rfl, allE_node, arows6726, irow6728, arows6727]
  all_goals rfl

theorem atot6728 : totK PD2M8K2 D2M8K2.u6728 = [382045169521, 1421402225325, 1424515944382, 334579873923, 13049727234, 0, 0, 0] := by
  rw [show D2M8K2.u6728 = KTree.node D2M8K2.u6726 (nat_lit 14442219) (nat_lit 2386551541) (nat_lit 0) D2M8K2.u6727 from rfl, totK_node, atot6726, atot6727]
  decide +kernel

theorem arows6733 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6733 = true := by
  rw [show D2M8K2.u6733 = KTree.node D2M8K2.u6731 (nat_lit 14445812) (nat_lit 2387074149) (nat_lit 0) D2M8K2.u6732 from rfl, allE_node, arows6731, irow6733, arows6732]
  all_goals rfl

theorem atot6733 : totK PD2M8K2 D2M8K2.u6733 = [410789646938, 1442942072002, 1363733452306, 323787227488, 13250685261, 0, 0, 0] := by
  rw [show D2M8K2.u6733 = KTree.node D2M8K2.u6731 (nat_lit 14445812) (nat_lit 2387074149) (nat_lit 0) D2M8K2.u6732 from rfl, totK_node, atot6731, atot6732]
  decide +kernel

theorem arows6736 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6736 = true := by
  rw [show D2M8K2.u6736 = KTree.node D2M8K2.u6734 (nat_lit 14450017) (nat_lit 1161217576) (nat_lit 0) D2M8K2.u6735 from rfl, allE_node, arows6734, irow6736, arows6735]
  all_goals rfl

theorem atot6736 : totK PD2M8K2 D2M8K2.u6736 = [425769842308, 1481198193492, 1406711758305, 273535497597, 6249254262, 0, 0, 0] := by
  rw [show D2M8K2.u6736 = KTree.node D2M8K2.u6734 (nat_lit 14450017) (nat_lit 1161217576) (nat_lit 0) D2M8K2.u6735 from rfl, totK_node, atot6734, atot6735]
  decide +kernel

theorem arows6740 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6740 = true := by
  rw [show D2M8K2.u6740 = KTree.node D2M8K2.u6738 (nat_lit 14453131) (nat_lit 1607253014) (nat_lit 0) D2M8K2.u6739 from rfl, allE_node, arows6738, irow6740, arows6739]
  all_goals rfl

theorem atot6740 : totK PD2M8K2 D2M8K2.u6740 = [0, 767710483673, 1886280468225, 824412155981, 46422997607, 0, 0, 0] := by
  rw [show D2M8K2.u6740 = KTree.node D2M8K2.u6738 (nat_lit 14453131) (nat_lit 1607253014) (nat_lit 0) D2M8K2.u6739 from rfl, totK_node, atot6738, atot6739]
  decide +kernel

theorem arows6743 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6743 = true := by
  rw [show D2M8K2.u6743 = KTree.node D2M8K2.u6741 (nat_lit 14460249) (nat_lit 1760920496) (nat_lit 0) D2M8K2.u6742 from rfl, allE_node, arows6741, irow6743, arows6742]
  all_goals rfl

theorem atot6743 : totK PD2M8K2 D2M8K2.u6743 = [0, 499731872569, 1649764773462, 1218255531632, 165340844770, 1369150432, 0, 0] := by
  rw [show D2M8K2.u6743 = KTree.node D2M8K2.u6741 (nat_lit 14460249) (nat_lit 1760920496) (nat_lit 0) D2M8K2.u6742 from rfl, totK_node, atot6741, atot6742]
  decide +kernel

theorem arows6749 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6749 = true := by
  rw [show D2M8K2.u6749 = KTree.node D2M8K2.u6747 (nat_lit 14466947) (nat_lit 2818362936) (nat_lit 0) D2M8K2.u6748 from rfl, allE_node, arows6747, irow6749, arows6748]
  all_goals rfl

theorem atot6749 : totK PD2M8K2 D2M8K2.u6749 = [0, 724119846163, 1888008487661, 896442625028, 48788482533, 0, 0, 0] := by
  rw [show D2M8K2.u6749 = KTree.node D2M8K2.u6747 (nat_lit 14466947) (nat_lit 2818362936) (nat_lit 0) D2M8K2.u6748 from rfl, totK_node, atot6747, atot6748]
  decide +kernel

theorem arows6752 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6752 = true := by
  rw [show D2M8K2.u6752 = KTree.node D2M8K2.u6750 (nat_lit 14477574) (nat_lit 3801646707) (nat_lit 0) D2M8K2.u6751 from rfl, allE_node, arows6750, irow6752, arows6751]
  all_goals rfl

theorem atot6752 : totK PD2M8K2 D2M8K2.u6752 = [438692147823, 1340641186530, 1349463584581, 483243113628, 28363432085, 0, 0, 0] := by
  rw [show D2M8K2.u6752 = KTree.node D2M8K2.u6750 (nat_lit 14477574) (nat_lit 3801646707) (nat_lit 0) D2M8K2.u6751 from rfl, totK_node, atot6750, atot6751]
  decide +kernel

theorem arows6756 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6756 = true := by
  rw [show D2M8K2.u6756 = KTree.node D2M8K2.u6754 (nat_lit 14480212) (nat_lit 3248589534) (nat_lit 0) D2M8K2.u6755 from rfl, allE_node, arows6754, irow6756, arows6755]
  all_goals rfl

theorem atot6756 : totK PD2M8K2 D2M8K2.u6756 = [253921294036, 1176880506745, 1578464851010, 600150472950, 37609398105, 0, 0, 0] := by
  rw [show D2M8K2.u6756 = KTree.node D2M8K2.u6754 (nat_lit 14480212) (nat_lit 3248589534) (nat_lit 0) D2M8K2.u6755 from rfl, totK_node, atot6754, atot6755]
  decide +kernel

theorem arows6759 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6759 = true := by
  rw [show D2M8K2.u6759 = KTree.node D2M8K2.u6757 (nat_lit 14483198) (nat_lit 2310122502) (nat_lit 0) D2M8K2.u6758 from rfl, allE_node, arows6757, irow6759, arows6758]
  all_goals rfl

theorem atot6759 : totK PD2M8K2 D2M8K2.u6759 = [399838998866, 1439081542500, 1443584060079, 330582272548, 13005887585, 0, 0, 0] := by
  rw [show D2M8K2.u6759 = KTree.node D2M8K2.u6757 (nat_lit 14483198) (nat_lit 2310122502) (nat_lit 0) D2M8K2.u6758 from rfl, totK_node, atot6757, atot6758]
  decide +kernel

theorem arows6764 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6764 = true := by
  rw [show D2M8K2.u6764 = KTree.node D2M8K2.u6762 (nat_lit 14487050) (nat_lit 4016923976) (nat_lit 0) D2M8K2.u6763 from rfl, allE_node, arows6762, irow6764, arows6763]
  all_goals rfl

theorem atot6764 : totK PD2M8K2 D2M8K2.u6764 = [436652812837, 1481312286431, 1412008060935, 316329317790, 12054146908, 0, 0, 0] := by
  rw [show D2M8K2.u6764 = KTree.node D2M8K2.u6762 (nat_lit 14487050) (nat_lit 4016923976) (nat_lit 0) D2M8K2.u6763 from rfl, totK_node, atot6762, atot6763]
  decide +kernel

theorem arows6767 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6767 = true := by
  rw [show D2M8K2.u6767 = KTree.node D2M8K2.u6765 (nat_lit 14491375) (nat_lit 2414209680) (nat_lit 0) D2M8K2.u6766 from rfl, allE_node, arows6765, irow6767, arows6766]
  all_goals rfl

theorem atot6767 : totK PD2M8K2 D2M8K2.u6767 = [470400749399, 1627843272062, 1347307430067, 205630075705, 3869034280, 0, 0, 0] := by
  rw [show D2M8K2.u6767 = KTree.node D2M8K2.u6765 (nat_lit 14491375) (nat_lit 2414209680) (nat_lit 0) D2M8K2.u6766 from rfl, totK_node, atot6765, atot6766]
  decide +kernel

theorem arows6771 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6771 = true := by
  rw [show D2M8K2.u6771 = KTree.node D2M8K2.u6769 (nat_lit 14498250) (nat_lit 3881623076) (nat_lit 0) D2M8K2.u6770 from rfl, allE_node, arows6769, irow6771, arows6770]
  all_goals rfl

theorem atot6771 : totK PD2M8K2 D2M8K2.u6771 = [0, 776140540565, 1885377683553, 893541272977, 59278965929, 0, 0, 0] := by
  rw [show D2M8K2.u6771 = KTree.node D2M8K2.u6769 (nat_lit 14498250) (nat_lit 3881623076) (nat_lit 0) D2M8K2.u6770 from rfl, totK_node, atot6769, atot6770]
  decide +kernel

theorem arows6774 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6774 = true := by
  rw [show D2M8K2.u6774 = KTree.node D2M8K2.u6772 (nat_lit 14500869) (nat_lit 1428788940) (nat_lit 0) D2M8K2.u6773 from rfl, allE_node, arows6772, irow6774, arows6773]
  all_goals rfl

theorem atot6774 : totK PD2M8K2 D2M8K2.u6774 = [0, 301853936711, 1202404584079, 1508719933400, 563492946205, 36921873854, 0, 0] := by
  rw [show D2M8K2.u6774 = KTree.node D2M8K2.u6772 (nat_lit 14500869) (nat_lit 1428788940) (nat_lit 0) D2M8K2.u6773 from rfl, totK_node, atot6772, atot6773]
  decide +kernel

theorem arows6782 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6782 = true := by
  rw [show D2M8K2.u6782 = KTree.node D2M8K2.u6780 (nat_lit 14504286) (nat_lit 3448927892) (nat_lit 0) D2M8K2.u6781 from rfl, allE_node, arows6780, irow6782, arows6781]
  all_goals rfl

theorem atot6782 : totK PD2M8K2 D2M8K2.u6782 = [0, 435814947174, 1523815027085, 1399969551977, 251852103207, 5159868635, 0, 0] := by
  rw [show D2M8K2.u6782 = KTree.node D2M8K2.u6780 (nat_lit 14504286) (nat_lit 3448927892) (nat_lit 0) D2M8K2.u6781 from rfl, totK_node, atot6780, atot6781]
  decide +kernel

theorem arows6785 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6785 = true := by
  rw [show D2M8K2.u6785 = KTree.node D2M8K2.u6783 (nat_lit 14508047) (nat_lit 2130895919) (nat_lit 0) D2M8K2.u6784 from rfl, allE_node, arows6783, irow6785, arows6784]
  all_goals rfl

theorem atot6785 : totK PD2M8K2 D2M8K2.u6785 = [0, 445059706855, 1569560649989, 1366696898863, 250917841085, 5218872685, 0, 0] := by
  rw [show D2M8K2.u6785 = KTree.node D2M8K2.u6783 (nat_lit 14508047) (nat_lit 2130895919) (nat_lit 0) D2M8K2.u6784 from rfl, totK_node, atot6783, atot6784]
  decide +kernel

theorem arows6789 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6789 = true := by
  rw [show D2M8K2.u6789 = KTree.node D2M8K2.u6787 (nat_lit 14512306) (nat_lit 4143879860) (nat_lit 0) D2M8K2.u6788 from rfl, allE_node, arows6787, irow6789, arows6788]
  all_goals rfl

theorem atot6789 : totK PD2M8K2 D2M8K2.u6789 = [0, 425746390404, 1604664314079, 1415469353441, 208807297037, 1415142070, 0, 0] := by
  rw [show D2M8K2.u6789 = KTree.node D2M8K2.u6787 (nat_lit 14512306) (nat_lit 4143879860) (nat_lit 0) D2M8K2.u6788 from rfl, totK_node, atot6787, atot6788]
  decide +kernel

theorem arows6792 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6792 = true := by
  rw [show D2M8K2.u6792 = KTree.node D2M8K2.u6790 (nat_lit 14515948) (nat_lit 3923897557) (nat_lit 0) D2M8K2.u6791 from rfl, allE_node, arows6790, irow6792, arows6791]
  all_goals rfl

theorem atot6792 : totK PD2M8K2 D2M8K2.u6792 = [407993187048, 1162718019337, 1010939060911, 710183631169, 244433112917, 9302370699, 0, 0] := by
  rw [show D2M8K2.u6792 = KTree.node D2M8K2.u6790 (nat_lit 14515948) (nat_lit 3923897557) (nat_lit 0) D2M8K2.u6791 from rfl, totK_node, atot6790, atot6791]
  decide +kernel

theorem arows6797 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6797 = true := by
  rw [show D2M8K2.u6797 = KTree.node D2M8K2.u6795 (nat_lit 14519600) (nat_lit 3062743386) (nat_lit 0) D2M8K2.u6796 from rfl, allE_node, arows6795, irow6797, arows6796]
  all_goals rfl

theorem atot6797 : totK PD2M8K2 D2M8K2.u6797 = [419403558970, 1528811567662, 1396805897532, 297704688402, 21382878902, 0, 0, 0] := by
  rw [show D2M8K2.u6797 = KTree.node D2M8K2.u6795 (nat_lit 14519600) (nat_lit 3062743386) (nat_lit 0) D2M8K2.u6796 from rfl, totK_node, atot6795, atot6796]
  decide +kernel

theorem arows6800 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6800 = true := by
  rw [show D2M8K2.u6800 = KTree.node D2M8K2.u6798 (nat_lit 14522452) (nat_lit 4041295213) (nat_lit 0) D2M8K2.u6799 from rfl, allE_node, arows6798, irow6800, arows6799]
  all_goals rfl

theorem atot6800 : totK PD2M8K2 D2M8K2.u6800 = [441236582993, 1417993704196, 1360626109775, 412265751451, 16027375701, 0, 0, 0] := by
  rw [show D2M8K2.u6800 = KTree.node D2M8K2.u6798 (nat_lit 14522452) (nat_lit 4041295213) (nat_lit 0) D2M8K2.u6799 from rfl, totK_node, atot6798, atot6799]
  decide +kernel

theorem arows6804 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6804 = true := by
  rw [show D2M8K2.u6804 = KTree.node D2M8K2.u6802 (nat_lit 14529156) (nat_lit 3267676036) (nat_lit 0) D2M8K2.u6803 from rfl, allE_node, arows6802, irow6804, arows6803]
  all_goals rfl

theorem atot6804 : totK PD2M8K2 D2M8K2.u6804 = [343039199400, 1357248532536, 1507207042335, 373534462251, 14146232338, 0, 0, 0] := by
  rw [show D2M8K2.u6804 = KTree.node D2M8K2.u6802 (nat_lit 14529156) (nat_lit 3267676036) (nat_lit 0) D2M8K2.u6803 from rfl, totK_node, atot6802, atot6803]
  decide +kernel

theorem arows6807 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6807 = true := by
  rw [show D2M8K2.u6807 = KTree.node D2M8K2.u6805 (nat_lit 14533069) (nat_lit 1382812956) (nat_lit 0) D2M8K2.u6806 from rfl, allE_node, arows6805, irow6807, arows6806]
  all_goals rfl

theorem atot6807 : totK PD2M8K2 D2M8K2.u6807 = [428052439055, 1513687162550, 1422578537282, 275661617975, 5152749158, 0, 0, 0] := by
  rw [show D2M8K2.u6807 = KTree.node D2M8K2.u6805 (nat_lit 14533069) (nat_lit 1382812956) (nat_lit 0) D2M8K2.u6806 from rfl, totK_node, atot6805, atot6806]
  decide +kernel

theorem arows6813 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6813 = true := by
  rw [show D2M8K2.u6813 = KTree.node D2M8K2.u6811 (nat_lit 14536568) (nat_lit 3741770008) (nat_lit 0) D2M8K2.u6812 from rfl, allE_node, arows6811, irow6813, arows6812]
  all_goals rfl

theorem atot6813 : totK PD2M8K2 D2M8K2.u6813 = [0, 678471326752, 1788734782253, 962118709598, 94525521542, 1206465782, 0, 0] := by
  rw [show D2M8K2.u6813 = KTree.node D2M8K2.u6811 (nat_lit 14536568) (nat_lit 3741770008) (nat_lit 0) D2M8K2.u6812 from rfl, totK_node, atot6811, atot6812]
  decide +kernel

theorem arows6816 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6816 = true := by
  rw [show D2M8K2.u6816 = KTree.node D2M8K2.u6814 (nat_lit 14540341) (nat_lit 906531001) (nat_lit 0) D2M8K2.u6815 from rfl, allE_node, arows6814, irow6816, arows6815]
  all_goals rfl

theorem atot6816 : totK PD2M8K2 D2M8K2.u6816 = [0, 593393243912, 1779371825806, 1151173010989, 102899927184, 0, 0, 0] := by
  rw [show D2M8K2.u6816 = KTree.node D2M8K2.u6814 (nat_lit 14540341) (nat_lit 906531001) (nat_lit 0) D2M8K2.u6815 from rfl, totK_node, atot6814, atot6815]
  decide +kernel

theorem arows6820 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6820 = true := by
  rw [show D2M8K2.u6820 = KTree.node D2M8K2.u6818 (nat_lit 14544902) (nat_lit 4023455683) (nat_lit 0) D2M8K2.u6819 from rfl, allE_node, arows6818, irow6820, arows6819]
  all_goals rfl

theorem atot6820 : totK PD2M8K2 D2M8K2.u6820 = [0, 426710946911, 1472369610466, 1335808253822, 297598807147, 13016197374, 0, 0] := by
  rw [show D2M8K2.u6820 = KTree.node D2M8K2.u6818 (nat_lit 14544902) (nat_lit 4023455683) (nat_lit 0) D2M8K2.u6819 from rfl, totK_node, atot6818, atot6819]
  decide +kernel

theorem arows6823 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6823 = true := by
  rw [show D2M8K2.u6823 = KTree.node D2M8K2.u6821 (nat_lit 14552196) (nat_lit 2816192788) (nat_lit 0) D2M8K2.u6822 from rfl, allE_node, arows6821, irow6823, arows6822]
  all_goals rfl

theorem atot6823 : totK PD2M8K2 D2M8K2.u6823 = [0, 480536767046, 1605237620795, 1284528726107, 193784255507, 4574395652, 0, 0] := by
  rw [show D2M8K2.u6823 = KTree.node D2M8K2.u6821 (nat_lit 14552196) (nat_lit 2816192788) (nat_lit 0) D2M8K2.u6822 from rfl, totK_node, atot6821, atot6822]
  decide +kernel

theorem arows6828 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6828 = true := by
  rw [show D2M8K2.u6828 = KTree.node D2M8K2.u6826 (nat_lit 14557760) (nat_lit 3610118551) (nat_lit 0) D2M8K2.u6827 from rfl, allE_node, arows6826, irow6828, arows6827]
  all_goals rfl

theorem atot6828 : totK PD2M8K2 D2M8K2.u6828 = [396283652373, 1406596549788, 1379453133610, 368978714126, 18845624966, 0, 0, 0] := by
  rw [show D2M8K2.u6828 = KTree.node D2M8K2.u6826 (nat_lit 14557760) (nat_lit 3610118551) (nat_lit 0) D2M8K2.u6827 from rfl, totK_node, atot6826, atot6827]
  decide +kernel

theorem arows6831 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6831 = true := by
  rw [show D2M8K2.u6831 = KTree.node D2M8K2.u6829 (nat_lit 14561451) (nat_lit 3727771151) (nat_lit 0) D2M8K2.u6830 from rfl, allE_node, arows6829, irow6831, arows6830]
  all_goals rfl

theorem atot6831 : totK PD2M8K2 D2M8K2.u6831 = [408170031933, 1418670671162, 1402087621689, 414794842908, 28205077490, 0, 0, 0] := by
  rw [show D2M8K2.u6831 = KTree.node D2M8K2.u6829 (nat_lit 14561451) (nat_lit 3727771151) (nat_lit 0) D2M8K2.u6830 from rfl, totK_node, atot6829, atot6830]
  decide +kernel

theorem arows6835 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6835 = true := by
  rw [show D2M8K2.u6835 = KTree.node D2M8K2.u6833 (nat_lit 14567998) (nat_lit 3883642573) (nat_lit 0) D2M8K2.u6834 from rfl, allE_node, arows6833, irow6835, arows6834]
  all_goals rfl

theorem atot6835 : totK PD2M8K2 D2M8K2.u6835 = [426400766099, 1459116009244, 1401189797683, 339042212985, 10551942191, 0, 0, 0] := by
  rw [show D2M8K2.u6835 = KTree.node D2M8K2.u6833 (nat_lit 14567998) (nat_lit 3883642573) (nat_lit 0) D2M8K2.u6834 from rfl, totK_node, atot6833, atot6834]
  decide +kernel

theorem arows6838 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6838 = true := by
  rw [show D2M8K2.u6838 = KTree.node D2M8K2.u6836 (nat_lit 14574515) (nat_lit 2957674858) (nat_lit 0) D2M8K2.u6837 from rfl, allE_node, arows6836, irow6838, arows6837]
  all_goals rfl

theorem atot6838 : totK PD2M8K2 D2M8K2.u6838 = [427166866107, 1448637735298, 1385306407453, 336707972463, 13321351172, 0, 0, 0] := by
  rw [show D2M8K2.u6838 = KTree.node D2M8K2.u6836 (nat_lit 14574515) (nat_lit 2957674858) (nat_lit 0) D2M8K2.u6837 from rfl, totK_node, atot6836, atot6837]
  decide +kernel

theorem arows6845 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6845 = true := by
  rw [show D2M8K2.u6845 = KTree.node D2M8K2.u6843 (nat_lit 14578035) (nat_lit 2799369883) (nat_lit 0) D2M8K2.u6844 from rfl, allE_node, arows6843, irow6845, arows6844]
  all_goals rfl

theorem atot6845 : totK PD2M8K2 D2M8K2.u6845 = [0, 685122028495, 1796614056891, 955318021088, 94290164423, 1239866073, 0, 0] := by
  rw [show D2M8K2.u6845 = KTree.node D2M8K2.u6843 (nat_lit 14578035) (nat_lit 2799369883) (nat_lit 0) D2M8K2.u6844 from rfl, totK_node, atot6843, atot6844]
  decide +kernel

theorem arows6848 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6848 = true := by
  rw [show D2M8K2.u6848 = KTree.node D2M8K2.u6846 (nat_lit 14581840) (nat_lit 2114507177) (nat_lit 0) D2M8K2.u6847 from rfl, allE_node, arows6846, irow6848, arows6847]
  all_goals rfl

theorem atot6848 : totK PD2M8K2 D2M8K2.u6848 = [0, 579361473728, 1753085899518, 1185175863484, 108536276100, 0, 0, 0] := by
  rw [show D2M8K2.u6848 = KTree.node D2M8K2.u6846 (nat_lit 14581840) (nat_lit 2114507177) (nat_lit 0) D2M8K2.u6847 from rfl, totK_node, atot6846, atot6847]
  decide +kernel

theorem arows6852 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6852 = true := by
  rw [show D2M8K2.u6852 = KTree.node D2M8K2.u6850 (nat_lit 14589866) (nat_lit 4126665669) (nat_lit 0) D2M8K2.u6851 from rfl, allE_node, arows6850, irow6852, arows6851]
  all_goals rfl

theorem atot6852 : totK PD2M8K2 D2M8K2.u6852 = [0, 425332534743, 1469329954554, 1346260035150, 303091528413, 13105450397, 0, 0] := by
  rw [show D2M8K2.u6852 = KTree.node D2M8K2.u6850 (nat_lit 14589866) (nat_lit 4126665669) (nat_lit 0) D2M8K2.u6851 from rfl, totK_node, atot6850, atot6851]
  decide +kernel

theorem arows6855 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6855 = true := by
  rw [show D2M8K2.u6855 = KTree.node D2M8K2.u6853 (nat_lit 14639856) (nat_lit 3589670634) (nat_lit 0) D2M8K2.u6854 from rfl, allE_node, arows6853, irow6855, arows6854]
  all_goals rfl

theorem atot6855 : totK PD2M8K2 D2M8K2.u6855 = [414024072134, 1348297865711, 1298348274718, 499707011748, 38720155712, 0, 0, 0] := by
  rw [show D2M8K2.u6855 = KTree.node D2M8K2.u6853 (nat_lit 14639856) (nat_lit 3589670634) (nat_lit 0) D2M8K2.u6854 from rfl, totK_node, atot6853, atot6854]
  decide +kernel

theorem arows6860 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6860 = true := by
  rw [show D2M8K2.u6860 = KTree.node D2M8K2.u6858 (nat_lit 14643704) (nat_lit 3670439703) (nat_lit 0) D2M8K2.u6859 from rfl, allE_node, arows6858, irow6860, arows6859]
  all_goals rfl

theorem atot6860 : totK PD2M8K2 D2M8K2.u6860 = [424522310219, 1559952926910, 1437501100955, 219064382871, 1369150432, 0, 0, 0] := by
  rw [show D2M8K2.u6860 = KTree.node D2M8K2.u6858 (nat_lit 14643704) (nat_lit 3670439703) (nat_lit 0) D2M8K2.u6859 from rfl, totK_node, atot6858, atot6859]
  decide +kernel

theorem arows6863 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6863 = true := by
  rw [show D2M8K2.u6863 = KTree.node D2M8K2.u6861 (nat_lit 14646528) (nat_lit 3757117624) (nat_lit 0) D2M8K2.u6862 from rfl, allE_node, arows6861, irow6863, arows6862]
  all_goals rfl

theorem atot6863 : totK PD2M8K2 D2M8K2.u6863 = [387953291601, 1262821093046, 1378803555507, 543435002723, 37370690916, 0, 0, 0] := by
  rw [show D2M8K2.u6863 = KTree.node D2M8K2.u6861 (nat_lit 14646528) (nat_lit 3757117624) (nat_lit 0) D2M8K2.u6862 from rfl, totK_node, atot6861, atot6862]
  decide +kernel

theorem arows6867 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6867 = true := by
  rw [show D2M8K2.u6867 = KTree.node D2M8K2.u6865 (nat_lit 14649752) (nat_lit 2905495574) (nat_lit 0) D2M8K2.u6866 from rfl, allE_node, arows6865, irow6867, arows6866]
  all_goals rfl

theorem atot6867 : totK PD2M8K2 D2M8K2.u6867 = [384347098273, 1429692316091, 1439142869862, 328545188657, 13020426360, 0, 0, 0] := by
  rw [show D2M8K2.u6867 = KTree.node D2M8K2.u6865 (nat_lit 14649752) (nat_lit 2905495574) (nat_lit 0) D2M8K2.u6866 from rfl, totK_node, atot6865, atot6866]
  decide +kernel

theorem arows6870 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6870 = true := by
  rw [show D2M8K2.u6870 = KTree.node D2M8K2.u6868 (nat_lit 14653224) (nat_lit 3497358080) (nat_lit 0) D2M8K2.u6869 from rfl, allE_node, arows6868, irow6870, arows6869]
  all_goals rfl

theorem atot6870 : totK PD2M8K2 D2M8K2.u6870 = [407134670851, 1463101499104, 1427506707797, 317792372624, 10571929038, 0, 0, 0] := by
  rw [show D2M8K2.u6870 = KTree.node D2M8K2.u6868 (nat_lit 14653224) (nat_lit 3497358080) (nat_lit 0) D2M8K2.u6869 from rfl, totK_node, atot6868, atot6869]
  decide +kernel

theorem arows6876 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6876 = true := by
  rw [show D2M8K2.u6876 = KTree.node D2M8K2.u6874 (nat_lit 14659632) (nat_lit 3602122962) (nat_lit 0) D2M8K2.u6875 from rfl, allE_node, arows6874, irow6876, arows6875]
  all_goals rfl

theorem atot6876 : totK PD2M8K2 D2M8K2.u6876 = [93924006320, 963465390239, 1825881946054, 680327328600, 31403331363, 0, 0, 0] := by
  rw [show D2M8K2.u6876 = KTree.node D2M8K2.u6874 (nat_lit 14659632) (nat_lit 3602122962) (nat_lit 0) D2M8K2.u6875 from rfl, totK_node, atot6874, atot6875]
  decide +kernel

theorem arows6879 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6879 = true := by
  rw [show D2M8K2.u6879 = KTree.node D2M8K2.u6877 (nat_lit 14663332) (nat_lit 3464006457) (nat_lit 0) D2M8K2.u6878 from rfl, allE_node, arows6877, irow6879, arows6878]
  all_goals rfl

theorem atot6879 : totK PD2M8K2 D2M8K2.u6879 = [0, 485511308304, 1596296408336, 1322572698106, 158258267498, 1310285577, 0, 0] := by
  rw [show D2M8K2.u6879 = KTree.node D2M8K2.u6877 (nat_lit 14663332) (nat_lit 3464006457) (nat_lit 0) D2M8K2.u6878 from rfl, totK_node, atot6877, atot6878]
  decide +kernel

theorem arows6883 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6883 = true := by
  rw [show D2M8K2.u6883 = KTree.node D2M8K2.u6881 (nat_lit 14668037) (nat_lit 2384514699) (nat_lit 0) D2M8K2.u6882 from rfl, allE_node, arows6881, irow6883, arows6882]
  all_goals rfl

theorem atot6883 : totK PD2M8K2 D2M8K2.u6883 = [0, 510653895488, 1642202838758, 1247845962367, 190065849034, 4879840392, 0, 0] := by
  rw [show D2M8K2.u6883 = KTree.node D2M8K2.u6881 (nat_lit 14668037) (nat_lit 2384514699) (nat_lit 0) D2M8K2.u6882 from rfl, totK_node, atot6881, atot6882]
  decide +kernel

theorem arows6886 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6886 = true := by
  rw [show D2M8K2.u6886 = KTree.node D2M8K2.u6884 (nat_lit 14671901) (nat_lit 1640295660) (nat_lit 0) D2M8K2.u6885 from rfl, allE_node, arows6884, irow6886, arows6885]
  all_goals rfl

theorem atot6886 : totK PD2M8K2 D2M8K2.u6886 = [0, 401034062454, 1518552563390, 1375424218812, 232619835821, 4931404646, 0, 0] := by
  rw [show D2M8K2.u6886 = KTree.node D2M8K2.u6884 (nat_lit 14671901) (nat_lit 1640295660) (nat_lit 0) D2M8K2.u6885 from rfl, totK_node, atot6884, atot6885]
  decide +kernel

theorem arows6891 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6891 = true := by
  rw [show D2M8K2.u6891 = KTree.node D2M8K2.u6889 (nat_lit 14678738) (nat_lit 3734632250) (nat_lit 0) D2M8K2.u6890 from rfl, allE_node, arows6889, irow6891, arows6890]
  all_goals rfl

theorem atot6891 : totK PD2M8K2 D2M8K2.u6891 = [0, 445469203148, 1529499518184, 1364348864930, 259578287353, 5842784248, 0, 0] := by
  rw [show D2M8K2.u6891 = KTree.node D2M8K2.u6889 (nat_lit 14678738) (nat_lit 3734632250) (nat_lit 0) D2M8K2.u6890 from rfl, totK_node, atot6889, atot6890]
  decide +kernel

theorem arows6894 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6894 = true := by
  rw [show D2M8K2.u6894 = KTree.node D2M8K2.u6892 (nat_lit 14682201) (nat_lit 1872246337) (nat_lit 0) D2M8K2.u6893 from rfl, allE_node, arows6892, irow6894, arows6893]
  all_goals rfl

theorem atot6894 : totK PD2M8K2 D2M8K2.u6894 = [0, 433489038150, 1474040246662, 1340619489374, 310282632143, 17277534250, 0, 0] := by
  rw [show D2M8K2.u6894 = KTree.node D2M8K2.u6892 (nat_lit 14682201) (nat_lit 1872246337) (nat_lit 0) D2M8K2.u6893 from rfl, totK_node, atot6892, atot6893]
  decide +kernel

theorem arows6898 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6898 = true := by
  rw [show D2M8K2.u6898 = KTree.node D2M8K2.u6896 (nat_lit 14689242) (nat_lit 2727210981) (nat_lit 0) D2M8K2.u6897 from rfl, allE_node, arows6896, irow6898, arows6897]
  all_goals rfl

theorem atot6898 : totK PD2M8K2 D2M8K2.u6898 = [0, 414284477259, 1506151038308, 1415751276670, 252460424624, 5172807878, 0, 0] := by
  rw [show D2M8K2.u6898 = KTree.node D2M8K2.u6896 (nat_lit 14689242) (nat_lit 2727210981) (nat_lit 0) D2M8K2.u6897 from rfl, totK_node, atot6896, atot6897]
  decide +kernel

theorem arows6901 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6901 = true := by
  rw [show D2M8K2.u6901 = KTree.node D2M8K2.u6899 (nat_lit 14692912) (nat_lit 3081642644) (nat_lit 0) D2M8K2.u6900 from rfl, allE_node, arows6899, irow6901, arows6900]
  all_goals rfl

theorem atot6901 : totK PD2M8K2 D2M8K2.u6901 = [0, 392801915487, 1464986588059, 1440275386056, 274680657174, 5228939780, 0, 0] := by
  rw [show D2M8K2.u6901 = KTree.node D2M8K2.u6899 (nat_lit 14692912) (nat_lit 3081642644) (nat_lit 0) D2M8K2.u6900 from rfl, totK_node, atot6899, atot6900]
  decide +kernel

theorem arows6910 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6910 = true := by
  rw [show D2M8K2.u6910 = KTree.node D2M8K2.u6908 (nat_lit 14696794) (nat_lit 3075571968) (nat_lit 0) D2M8K2.u6909 from rfl, allE_node, arows6908, irow6910, arows6909]
  all_goals rfl

theorem atot6910 : totK PD2M8K2 D2M8K2.u6910 = [0, 556506034366, 1690720016736, 1183624727740, 137910565412, 1096505104, 0, 0] := by
  rw [show D2M8K2.u6910 = KTree.node D2M8K2.u6908 (nat_lit 14696794) (nat_lit 3075571968) (nat_lit 0) D2M8K2.u6909 from rfl, totK_node, atot6908, atot6909]
  decide +kernel

theorem arows6913 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6913 = true := by
  rw [show D2M8K2.u6913 = KTree.node D2M8K2.u6911 (nat_lit 14700732) (nat_lit 3179192343) (nat_lit 0) D2M8K2.u6912 from rfl, allE_node, arows6911, irow6913, arows6912]
  all_goals rfl

theorem atot6913 : totK PD2M8K2 D2M8K2.u6913 = [0, 177879713851, 1133281556462, 1702311353812, 525575056153, 23286209526, 0, 0] := by
  rw [show D2M8K2.u6913 = KTree.node D2M8K2.u6911 (nat_lit 14700732) (nat_lit 3179192343) (nat_lit 0) D2M8K2.u6912 from rfl, totK_node, atot6911, atot6912]
  decide +kernel

theorem arows6917 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6917 = true := by
  rw [show D2M8K2.u6917 = KTree.node D2M8K2.u6915 (nat_lit 14704135) (nat_lit 1896628016) (nat_lit 0) D2M8K2.u6916 from rfl, allE_node, arows6915, irow6917, arows6916]
  all_goals rfl

theorem atot6917 : totK PD2M8K2 D2M8K2.u6917 = [0, 0, 501473236708, 1684505549257, 1144343271636, 127528409045, 1369150432, 0] := by
  rw [show D2M8K2.u6917 = KTree.node D2M8K2.u6915 (nat_lit 14704135) (nat_lit 1896628016) (nat_lit 0) D2M8K2.u6916 from rfl, totK_node, atot6915, atot6916]
  decide +kernel

theorem arows6920 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6920 = true := by
  rw [show D2M8K2.u6920 = KTree.node D2M8K2.u6918 (nat_lit 14713180) (nat_lit 3030407212) (nat_lit 0) D2M8K2.u6919 from rfl, allE_node, arows6918, irow6920, arows6919]
  all_goals rfl

theorem atot6920 : totK PD2M8K2 D2M8K2.u6920 = [0, 0, 751708261417, 1923847494606, 805029432443, 33081322867, 0, 0] := by
  rw [show D2M8K2.u6920 = KTree.node D2M8K2.u6918 (nat_lit 14713180) (nat_lit 3030407212) (nat_lit 0) D2M8K2.u6919 from rfl, totK_node, atot6918, atot6919]
  decide +kernel

theorem arows6925 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6925 = true := by
  rw [show D2M8K2.u6925 = KTree.node D2M8K2.u6923 (nat_lit 14719975) (nat_lit 2386616747) (nat_lit 0) D2M8K2.u6924 from rfl, allE_node, arows6923, irow6925, arows6924]
  all_goals rfl

theorem atot6925 : totK PD2M8K2 D2M8K2.u6925 = [0, 182603865993, 1000708323679, 1690326053156, 668633057337, 31823675696, 0, 0] := by
  rw [show D2M8K2.u6925 = KTree.node D2M8K2.u6923 (nat_lit 14719975) (nat_lit 2386616747) (nat_lit 0) D2M8K2.u6924 from rfl, totK_node, atot6923, atot6924]
  decide +kernel

theorem arows6928 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6928 = true := by
  rw [show D2M8K2.u6928 = KTree.node D2M8K2.u6926 (nat_lit 14728320) (nat_lit 2809586871) (nat_lit 0) D2M8K2.u6927 from rfl, allE_node, arows6926, irow6928, arows6927]
  all_goals rfl

theorem atot6928 : totK PD2M8K2 D2M8K2.u6928 = [0, 327975039362, 1212664592700, 1475176482148, 573941270828, 37500656948, 0, 0] := by
  rw [show D2M8K2.u6928 = KTree.node D2M8K2.u6926 (nat_lit 14728320) (nat_lit 2809586871) (nat_lit 0) D2M8K2.u6927 from rfl, totK_node, atot6926, atot6927]
  decide +kernel

theorem arows6932 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6932 = true := by
  rw [show D2M8K2.u6932 = KTree.node D2M8K2.u6930 (nat_lit 14731128) (nat_lit 2784649686) (nat_lit 0) D2M8K2.u6931 from rfl, allE_node, arows6930, irow6932, arows6931]
  all_goals rfl

theorem atot6932 : totK PD2M8K2 D2M8K2.u6932 = [0, 401901772966, 1463728410094, 1436323603865, 315819746491, 9067749566, 0, 0] := by
  rw [show D2M8K2.u6932 = KTree.node D2M8K2.u6930 (nat_lit 14731128) (nat_lit 2784649686) (nat_lit 0) D2M8K2.u6931 from rfl, totK_node, atot6930, atot6931]
  decide +kernel

theorem arows6935 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6935 = true := by
  rw [show D2M8K2.u6935 = KTree.node D2M8K2.u6933 (nat_lit 14734655) (nat_lit 2760131092) (nat_lit 0) D2M8K2.u6934 from rfl, allE_node, arows6933, irow6935, arows6934]
  all_goals rfl

theorem atot6935 : totK PD2M8K2 D2M8K2.u6935 = [0, 422672874352, 1476343531917, 1420446782113, 318058052016, 9178989717, 0, 0] := by
  rw [show D2M8K2.u6935 = KTree.node D2M8K2.u6933 (nat_lit 14734655) (nat_lit 2760131092) (nat_lit 0) D2M8K2.u6934 from rfl, totK_node, atot6933, atot6934]
  decide +kernel

theorem arows6941 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6941 = true := by
  rw [show D2M8K2.u6941 = KTree.node D2M8K2.u6939 (nat_lit 14739048) (nat_lit 2902828671) (nat_lit 0) D2M8K2.u6940 from rfl, allE_node, arows6939, irow6941, arows6940]
  all_goals rfl

theorem atot6941 : totK PD2M8K2 D2M8K2.u6941 = [0, 504558765341, 1644829310496, 1315446893184, 190018330747, 1429815836, 0, 0] := by
  rw [show D2M8K2.u6941 = KTree.node D2M8K2.u6939 (nat_lit 14739048) (nat_lit 2902828671) (nat_lit 0) D2M8K2.u6940 from rfl, totK_node, atot6939, atot6940]
  decide +kernel

theorem arows6944 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6944 = true := by
  rw [show D2M8K2.u6944 = KTree.node D2M8K2.u6942 (nat_lit 14742358) (nat_lit 2928667812) (nat_lit 0) D2M8K2.u6943 from rfl, allE_node, arows6942, irow6944, arows6943]
  all_goals rfl

theorem atot6944 : totK PD2M8K2 D2M8K2.u6944 = [0, 358677311997, 1336173741058, 1442501431798, 424942945245, 21930582058, 0, 0] := by
  rw [show D2M8K2.u6944 = KTree.node D2M8K2.u6942 (nat_lit 14742358) (nat_lit 2928667812) (nat_lit 0) D2M8K2.u6943 from rfl, totK_node, atot6942, atot6943]
  decide +kernel

theorem arows6948 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6948 = true := by
  rw [show D2M8K2.u6948 = KTree.node D2M8K2.u6946 (nat_lit 14766698) (nat_lit 2772820576) (nat_lit 0) D2M8K2.u6947 from rfl, allE_node, arows6946, irow6948, arows6947]
  all_goals rfl

theorem atot6948 : totK PD2M8K2 D2M8K2.u6948 = [0, 462656689951, 1594644772330, 1355303578465, 183817289722, 1369150432, 0, 0] := by
  rw [show D2M8K2.u6948 = KTree.node D2M8K2.u6946 (nat_lit 14766698) (nat_lit 2772820576) (nat_lit 0) D2M8K2.u6947 from rfl, totK_node, atot6946, atot6947]
  decide +kernel

theorem arows6951 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6951 = true := by
  rw [show D2M8K2.u6951 = KTree.node D2M8K2.u6949 (nat_lit 14770111) (nat_lit 2355443833) (nat_lit 0) D2M8K2.u6950 from rfl, allE_node, arows6949, irow6951, arows6950]
  all_goals rfl

theorem atot6951 : totK PD2M8K2 D2M8K2.u6951 = [0, 343479827603, 1266827522290, 1444759881956, 543627011153, 32764831815, 0, 0] := by
  rw [show D2M8K2.u6951 = KTree.node D2M8K2.u6949 (nat_lit 14770111) (nat_lit 2355443833) (nat_lit 0) D2M8K2.u6950 from rfl, totK_node, atot6949, atot6950]
  decide +kernel

theorem arows6956 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6956 = true := by
  rw [show D2M8K2.u6956 = KTree.node D2M8K2.u6954 (nat_lit 14772918) (nat_lit 2447764286) (nat_lit 0) D2M8K2.u6955 from rfl, allE_node, arows6954, irow6956, arows6955]
  all_goals rfl

theorem atot6956 : totK PD2M8K2 D2M8K2.u6956 = [0, 384311551833, 1417851485805, 1451232540550, 329567277806, 13049727234, 0, 0] := by
  rw [show D2M8K2.u6956 = KTree.node D2M8K2.u6954 (nat_lit 14772918) (nat_lit 2447764286) (nat_lit 0) D2M8K2.u6955 from rfl, totK_node, atot6954, atot6955]
  decide +kernel

theorem arows6959 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6959 = true := by
  rw [show D2M8K2.u6959 = KTree.node D2M8K2.u6957 (nat_lit 14780188) (nat_lit 3940517389) (nat_lit 0) D2M8K2.u6958 from rfl, allE_node, arows6957, irow6959, arows6958]
  all_goals rfl

theorem atot6959 : totK PD2M8K2 D2M8K2.u6959 = [0, 486642451673, 1598570874628, 1325113587326, 208095692981, 4783062791, 0, 0] := by
  rw [show D2M8K2.u6959 = KTree.node D2M8K2.u6957 (nat_lit 14780188) (nat_lit 3940517389) (nat_lit 0) D2M8K2.u6958 from rfl, totK_node, atot6957, atot6958]
  decide +kernel

theorem arows6963 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6963 = true := by
  rw [show D2M8K2.u6963 = KTree.node D2M8K2.u6961 (nat_lit 14783768) (nat_lit 2793612047) (nat_lit 0) D2M8K2.u6962 from rfl, allE_node, arows6961, irow6963, arows6962]
  all_goals rfl

theorem atot6963 : totK PD2M8K2 D2M8K2.u6963 = [0, 164699952579, 1068417786142, 1708449769321, 598891234627, 27399001333, 0, 0] := by
  rw [show D2M8K2.u6963 = KTree.node D2M8K2.u6961 (nat_lit 14783768) (nat_lit 2793612047) (nat_lit 0) D2M8K2.u6962 from rfl, totK_node, atot6961, atot6962]
  decide +kernel

theorem arows6966 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6966 = true := by
  rw [show D2M8K2.u6966 = KTree.node D2M8K2.u6964 (nat_lit 14787661) (nat_lit 1357182259) (nat_lit 0) D2M8K2.u6965 from rfl, allE_node, arows6964, irow6966, arows6965]
  all_goals rfl

theorem atot6966 : totK PD2M8K2 D2M8K2.u6966 = [0, 0, 628567401668, 1750977296881, 1051779211637, 97359209235, 1166720416, 0] := by
  rw [show D2M8K2.u6966 = KTree.node D2M8K2.u6964 (nat_lit 14787661) (nat_lit 1357182259) (nat_lit 0) D2M8K2.u6965 from rfl, totK_node, atot6964, atot6965]
  decide +kernel

theorem arows6973 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6973 = true := by
  rw [show D2M8K2.u6973 = KTree.node D2M8K2.u6971 (nat_lit 14793126) (nat_lit 3243100158) (nat_lit 0) D2M8K2.u6972 from rfl, allE_node, arows6971, irow6973, arows6972]
  all_goals rfl

theorem atot6973 : totK PD2M8K2 D2M8K2.u6973 = [0, 0, 449881685659, 1584074297961, 1265994756309, 204085807880, 5134755853, 0] := by
  rw [show D2M8K2.u6973 = KTree.node D2M8K2.u6971 (nat_lit 14793126) (nat_lit 3243100158) (nat_lit 0) D2M8K2.u6972 from rfl, totK_node, atot6971, atot6972]
  decide +kernel

theorem arows6976 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6976 = true := by
  rw [show D2M8K2.u6976 = KTree.node D2M8K2.u6974 (nat_lit 14802406) (nat_lit 3795838006) (nat_lit 0) D2M8K2.u6975 from rfl, allE_node, arows6974, irow6976, arows6975]
  all_goals rfl

theorem atot6976 : totK PD2M8K2 D2M8K2.u6976 = [0, 89204917003, 873037919316, 1787451544485, 755330560067, 42907812837, 0, 0] := by
  rw [show D2M8K2.u6976 = KTree.node D2M8K2.u6974 (nat_lit 14802406) (nat_lit 3795838006) (nat_lit 0) D2M8K2.u6975 from rfl, totK_node, atot6974, atot6975]
  decide +kernel

theorem arows6980 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6980 = true := by
  rw [show D2M8K2.u6980 = KTree.node D2M8K2.u6978 (nat_lit 14807302) (nat_lit 3380970544) (nat_lit 0) D2M8K2.u6979 from rfl, allE_node, arows6978, irow6980, arows6979]
  all_goals rfl

theorem atot6980 : totK PD2M8K2 D2M8K2.u6980 = [0, 469044647850, 1595249653489, 1345218029373, 180044552642, 1369150432, 0, 0] := by
  rw [show D2M8K2.u6980 = KTree.node D2M8K2.u6978 (nat_lit 14807302) (nat_lit 3380970544) (nat_lit 0) D2M8K2.u6979 from rfl, totK_node, atot6978, atot6979]
  decide +kernel

theorem arows6983 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6983 = true := by
  rw [show D2M8K2.u6983 = KTree.node D2M8K2.u6981 (nat_lit 14811220) (nat_lit 3286535312) (nat_lit 0) D2M8K2.u6982 from rfl, allE_node, arows6981, irow6983, arows6982]
  all_goals rfl

theorem atot6983 : totK PD2M8K2 D2M8K2.u6983 = [0, 329909005082, 1264191323462, 1456271968979, 540659986344, 32805585335, 0, 0] := by
  rw [show D2M8K2.u6983 = KTree.node D2M8K2.u6981 (nat_lit 14811220) (nat_lit 3286535312) (nat_lit 0) D2M8K2.u6982 from rfl, totK_node, atot6981, atot6982]
  decide +kernel

theorem arows6988 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6988 = true := by
  rw [show D2M8K2.u6988 = KTree.node D2M8K2.u6986 (nat_lit 14817537) (nat_lit 1541330370) (nat_lit 0) D2M8K2.u6987 from rfl, allE_node, arows6986, irow6988, arows6987]
  all_goals rfl

theorem atot6988 : totK PD2M8K2 D2M8K2.u6988 = [0, 376676424046, 1419036864377, 1457142376296, 343926813262, 13189998508, 0, 0] := by
  rw [show D2M8K2.u6988 = KTree.node D2M8K2.u6986 (nat_lit 14817537) (nat_lit 1541330370) (nat_lit 0) D2M8K2.u6987 from rfl, totK_node, atot6986, atot6987]
  decide +kernel

theorem arows6991 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6991 = true := by
  rw [show D2M8K2.u6991 = KTree.node D2M8K2.u6989 (nat_lit 14824348) (nat_lit 3875180351) (nat_lit 0) D2M8K2.u6990 from rfl, allE_node, arows6989, irow6991, arows6990]
  all_goals rfl

theorem atot6991 : totK PD2M8K2 D2M8K2.u6991 = [0, 391838415980, 1443585271064, 1430046463725, 328190246744, 8641950322, 0, 0] := by
  rw [show D2M8K2.u6991 = KTree.node D2M8K2.u6989 (nat_lit 14824348) (nat_lit 3875180351) (nat_lit 0) D2M8K2.u6990 from rfl, totK_node, atot6989, atot6990]
  decide +kernel

theorem arows6995 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6995 = true := by
  rw [show D2M8K2.u6995 = KTree.node D2M8K2.u6993 (nat_lit 14827715) (nat_lit 2881151202) (nat_lit 0) D2M8K2.u6994 from rfl, allE_node, arows6993, irow6995, arows6994]
  all_goals rfl

theorem atot6995 : totK PD2M8K2 D2M8K2.u6995 = [0, 0, 516273820002, 1718565716711, 1147873179942, 111583229398, 1200365979, 0] := by
  rw [show D2M8K2.u6995 = KTree.node D2M8K2.u6993 (nat_lit 14827715) (nat_lit 2881151202) (nat_lit 0) D2M8K2.u6994 from rfl, totK_node, atot6993, atot6994]
  decide +kernel

theorem arows6998 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u6998 = true := by
  rw [show D2M8K2.u6998 = KTree.node D2M8K2.u6996 (nat_lit 14837012) (nat_lit 3518759008) (nat_lit 0) D2M8K2.u6997 from rfl, allE_node, arows6996, irow6998, arows6997]
  all_goals rfl

theorem atot6998 : totK PD2M8K2 D2M8K2.u6998 = [0, 0, 733120388323, 1804485760687, 953729149968, 87032634317, 1135526696, 0] := by
  rw [show D2M8K2.u6998 = KTree.node D2M8K2.u6996 (nat_lit 14837012) (nat_lit 3518759008) (nat_lit 0) D2M8K2.u6997 from rfl, totK_node, atot6996, atot6997]
  decide +kernel

theorem arows7004 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7004 = true := by
  rw [show D2M8K2.u7004 = KTree.node D2M8K2.u7002 (nat_lit 14844086) (nat_lit 3834405570) (nat_lit 0) D2M8K2.u7003 from rfl, allE_node, arows7002, irow7004, arows7003]
  all_goals rfl

theorem atot7004 : totK PD2M8K2 D2M8K2.u7004 = [0, 141987590768, 716476105127, 1483716773534, 1058214182912, 161820073623, 4028038878, 0] := by
  rw [show D2M8K2.u7004 = KTree.node D2M8K2.u7002 (nat_lit 14844086) (nat_lit 3834405570) (nat_lit 0) D2M8K2.u7003 from rfl, totK_node, atot7002, atot7003]
  decide +kernel

theorem arows7007 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7007 = true := by
  rw [show D2M8K2.u7007 = KTree.node D2M8K2.u7005 (nat_lit 14890376) (nat_lit 3240600169) (nat_lit 0) D2M8K2.u7006 from rfl, allE_node, arows7005, irow7007, arows7006]
  all_goals rfl

theorem atot7007 : totK PD2M8K2 D2M8K2.u7007 = [0, 452093671834, 1594381004704, 1364771460018, 175453355896, 1369150432, 0, 0] := by
  rw [show D2M8K2.u7007 = KTree.node D2M8K2.u7005 (nat_lit 14890376) (nat_lit 3240600169) (nat_lit 0) D2M8K2.u7006 from rfl, totK_node, atot7005, atot7006]
  decide +kernel

theorem arows7011 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7011 = true := by
  rw [show D2M8K2.u7011 = KTree.node D2M8K2.u7009 (nat_lit 14894206) (nat_lit 3766012543) (nat_lit 0) D2M8K2.u7010 from rfl, allE_node, arows7009, irow7011, arows7010]
  all_goals rfl

theorem atot7011 : totK PD2M8K2 D2M8K2.u7011 = [0, 328372485553, 1227012295411, 1463198323200, 544204085623, 30407432289, 0, 0] := by
  rw [show D2M8K2.u7011 = KTree.node D2M8K2.u7009 (nat_lit 14894206) (nat_lit 3766012543) (nat_lit 0) D2M8K2.u7010 from rfl, totK_node, atot7009, atot7010]
  decide +kernel

theorem arows7014 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7014 = true := by
  rw [show D2M8K2.u7014 = KTree.node D2M8K2.u7012 (nat_lit 14897068) (nat_lit 3832638052) (nat_lit 0) D2M8K2.u7013 from rfl, allE_node, arows7012, irow7014, arows7013]
  all_goals rfl

theorem atot7014 : totK PD2M8K2 D2M8K2.u7014 = [0, 402307041405, 1447855141981, 1429842718891, 300491789330, 8557595888, 0, 0] := by
  rw [show D2M8K2.u7014 = KTree.node D2M8K2.u7012 (nat_lit 14897068) (nat_lit 3832638052) (nat_lit 0) D2M8K2.u7013 from rfl, totK_node, atot7012, atot7013]
  decide +kernel

theorem arows7019 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7019 = true := by
  rw [show D2M8K2.u7019 = KTree.node D2M8K2.u7017 (nat_lit 14900492) (nat_lit 1509987460) (nat_lit 0) D2M8K2.u7018 from rfl, allE_node, arows7017, irow7019, arows7018]
  all_goals rfl

theorem atot7019 : totK PD2M8K2 D2M8K2.u7019 = [0, 416814237493, 1451140919673, 1393109196125, 300436445504, 8656689423, 0, 0] := by
  rw [show D2M8K2.u7019 = KTree.node D2M8K2.u7017 (nat_lit 14900492) (nat_lit 1509987460) (nat_lit 0) D2M8K2.u7018 from rfl, totK_node, atot7017, atot7018]
  decide +kernel

theorem arows7022 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7022 = true := by
  rw [show D2M8K2.u7022 = KTree.node D2M8K2.u7020 (nat_lit 14907316) (nat_lit 3740860155) (nat_lit 0) D2M8K2.u7021 from rfl, allE_node, arows7020, irow7022, arows7021]
  all_goals rfl

theorem atot7022 : totK PD2M8K2 D2M8K2.u7022 = [0, 364636407204, 1442812625877, 1485236737040, 336862497955, 8710740030, 0, 0] := by
  rw [show D2M8K2.u7022 = KTree.node D2M8K2.u7020 (nat_lit 14907316) (nat_lit 3740860155) (nat_lit 0) D2M8K2.u7021 from rfl, totK_node, atot7020, atot7021]
  decide +kernel

theorem arows7026 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7026 = true := by
  rw [show D2M8K2.u7026 = KTree.node D2M8K2.u7024 (nat_lit 14910553) (nat_lit 1413477595) (nat_lit 0) D2M8K2.u7025 from rfl, allE_node, arows7024, irow7026, arows7025]
  all_goals rfl

theorem atot7026 : totK PD2M8K2 D2M8K2.u7026 = [0, 0, 477933665990, 1624735739125, 1233932904267, 142733389398, 1288491354, 0] := by
  rw [show D2M8K2.u7026 = KTree.node D2M8K2.u7024 (nat_lit 14910553) (nat_lit 1413477595) (nat_lit 0) D2M8K2.u7025 from rfl, totK_node, atot7024, atot7025]
  decide +kernel

theorem arows7029 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7029 = true := by
  rw [show D2M8K2.u7029 = KTree.node D2M8K2.u7027 (nat_lit 14916101) (nat_lit 2330038851) (nat_lit 0) D2M8K2.u7028 from rfl, allE_node, arows7027, irow7029, arows7028]
  all_goals rfl

theorem atot7029 : totK PD2M8K2 D2M8K2.u7029 = [0, 0, 804689150494, 1909862584707, 824953643749, 52062508521, 0, 0] := by
  rw [show D2M8K2.u7029 = KTree.node D2M8K2.u7027 (nat_lit 14916101) (nat_lit 2330038851) (nat_lit 0) D2M8K2.u7028 from rfl, totK_node, atot7027, atot7028]
  decide +kernel

theorem arows7037 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7037 = true := by
  rw [show D2M8K2.u7037 = KTree.node D2M8K2.u7035 (nat_lit 14919776) (nat_lit 3389680236) (nat_lit 0) D2M8K2.u7036 from rfl, allE_node, arows7035, irow7037, arows7036]
  all_goals rfl

theorem atot7037 : totK PD2M8K2 D2M8K2.u7037 = [0, 0, 397542143160, 1536657759487, 1334333181974, 205789397153, 4787054165, 0] := by
  rw [show D2M8K2.u7037 = KTree.node D2M8K2.u7035 (nat_lit 14919776) (nat_lit 3389680236) (nat_lit 0) D2M8K2.u7036 from rfl, totK_node, atot7035, atot7036]
  decide +kernel

theorem arows7040 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7040 = true := by
  rw [show D2M8K2.u7040 = KTree.node D2M8K2.u7038 (nat_lit 14926952) (nat_lit 3216022416) (nat_lit 0) D2M8K2.u7039 from rfl, allE_node, arows7038, irow7040, arows7039]
  all_goals rfl

theorem atot7040 : totK PD2M8K2 D2M8K2.u7040 = [0, 0, 442463770589, 1529099502733, 1322018956707, 241685994245, 6080382018, 0] := by
  rw [show D2M8K2.u7040 = KTree.node D2M8K2.u7038 (nat_lit 14926952) (nat_lit 3216022416) (nat_lit 0) D2M8K2.u7039 from rfl, totK_node, atot7038, atot7039]
  decide +kernel

theorem arows7044 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7044 = true := by
  rw [show D2M8K2.u7044 = KTree.node D2M8K2.u7042 (nat_lit 14930080) (nat_lit 2819724516) (nat_lit 0) D2M8K2.u7043 from rfl, allE_node, arows7042, irow7044, arows7043]
  all_goals rfl

theorem atot7044 : totK PD2M8K2 D2M8K2.u7044 = [0, 442425092496, 1109231482915, 871810153842, 809163583462, 316956160101, 20509029466, 0] := by
  rw [show D2M8K2.u7044 = KTree.node D2M8K2.u7042 (nat_lit 14930080) (nat_lit 2819724516) (nat_lit 0) D2M8K2.u7043 from rfl, totK_node, atot7042, atot7043]
  decide +kernel

theorem arows7047 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7047 = true := by
  rw [show D2M8K2.u7047 = KTree.node D2M8K2.u7045 (nat_lit 14937160) (nat_lit 3875655435) (nat_lit 0) D2M8K2.u7046 from rfl, allE_node, arows7045, irow7047, arows7046]
  all_goals rfl

theorem atot7047 : totK PD2M8K2 D2M8K2.u7047 = [0, 421179288580, 1583782674664, 1427107123168, 201473391454, 1369150432, 0, 0] := by
  rw [show D2M8K2.u7047 = KTree.node D2M8K2.u7045 (nat_lit 14937160) (nat_lit 3875655435) (nat_lit 0) D2M8K2.u7046 from rfl, totK_node, atot7045, atot7046]
  decide +kernel

theorem arows7052 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7052 = true := by
  rw [show D2M8K2.u7052 = KTree.node D2M8K2.u7050 (nat_lit 14940485) (nat_lit 2297674318) (nat_lit 0) D2M8K2.u7051 from rfl, allE_node, arows7050, irow7052, arows7051]
  all_goals rfl

theorem atot7052 : totK PD2M8K2 D2M8K2.u7052 = [0, 399936882060, 1427889171804, 1402581436425, 316986367008, 13049727234, 0, 0] := by
  rw [show D2M8K2.u7052 = KTree.node D2M8K2.u7050 (nat_lit 14940485) (nat_lit 2297674318) (nat_lit 0) D2M8K2.u7051 from rfl, totK_node, atot7050, atot7051]
  decide +kernel

theorem arows7055 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7055 = true := by
  rw [show D2M8K2.u7055 = KTree.node D2M8K2.u7053 (nat_lit 14943944) (nat_lit 3656448241) (nat_lit 0) D2M8K2.u7054 from rfl, allE_node, arows7053, irow7055, arows7054]
  all_goals rfl

theorem atot7055 : totK PD2M8K2 D2M8K2.u7055 = [0, 414217542484, 1425788530319, 1358803563005, 309059407922, 13250685261, 0, 0] := by
  rw [show D2M8K2.u7055 = KTree.node D2M8K2.u7053 (nat_lit 14943944) (nat_lit 3656448241) (nat_lit 0) D2M8K2.u7054 from rfl, totK_node, atot7053, atot7054]
  decide +kernel

theorem arows7059 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7059 = true := by
  rw [show D2M8K2.u7059 = KTree.node D2M8K2.u7057 (nat_lit 14947527) (nat_lit 3589503829) (nat_lit 0) D2M8K2.u7058 from rfl, allE_node, arows7057, irow7059, arows7058]
  all_goals rfl

theorem atot7059 : totK PD2M8K2 D2M8K2.u7059 = [0, 419234341778, 1506530012312, 1414602087123, 245337677495, 4980514959, 0, 0] := by
  rw [show D2M8K2.u7059 = KTree.node D2M8K2.u7057 (nat_lit 14947527) (nat_lit 3589503829) (nat_lit 0) D2M8K2.u7058 from rfl, totK_node, atot7057, atot7058]
  decide +kernel

theorem arows7062 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7062 = true := by
  rw [show D2M8K2.u7062 = KTree.node D2M8K2.u7060 (nat_lit 14950676) (nat_lit 3255924874) (nat_lit 0) D2M8K2.u7061 from rfl, allE_node, arows7060, irow7062, arows7061]
  all_goals rfl

theorem atot7062 : totK PD2M8K2 D2M8K2.u7062 = [0, 0, 790746807928, 1901122920245, 792085645030, 43865840370, 0, 0] := by
  rw [show D2M8K2.u7062 = KTree.node D2M8K2.u7060 (nat_lit 14950676) (nat_lit 3255924874) (nat_lit 0) D2M8K2.u7061 from rfl, totK_node, atot7060, atot7061]
  decide +kernel

theorem arows7068 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7068 = true := by
  rw [show D2M8K2.u7068 = KTree.node D2M8K2.u7066 (nat_lit 14957716) (nat_lit 3685469850) (nat_lit 0) D2M8K2.u7067 from rfl, allE_node, arows7066, irow7068, arows7067]
  all_goals rfl

theorem atot7068 : totK PD2M8K2 D2M8K2.u7068 = [0, 0, 454545061048, 1638066295217, 1261937998776, 169183964232, 1369150432, 0] := by
  rw [show D2M8K2.u7068 = KTree.node D2M8K2.u7066 (nat_lit 14957716) (nat_lit 3685469850) (nat_lit 0) D2M8K2.u7067 from rfl, totK_node, atot7066, atot7067]
  decide +kernel

theorem arows7071 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7071 = true := by
  rw [show D2M8K2.u7071 = KTree.node D2M8K2.u7069 (nat_lit 14962661) (nat_lit 1877491139) (nat_lit 0) D2M8K2.u7070 from rfl, allE_node, arows7069, irow7071, arows7070]
  all_goals rfl

theorem atot7071 : totK PD2M8K2 D2M8K2.u7071 = [0, 0, 756617958210, 1887239535231, 809103406012, 42132450812, 0, 0] := by
  rw [show D2M8K2.u7071 = KTree.node D2M8K2.u7069 (nat_lit 14962661) (nat_lit 1877491139) (nat_lit 0) D2M8K2.u7070 from rfl, totK_node, atot7069, atot7070]
  decide +kernel

theorem arows7075 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7075 = true := by
  rw [show D2M8K2.u7075 = KTree.node D2M8K2.u7073 (nat_lit 14969030) (nat_lit 1986335526) (nat_lit 8) D2M8K2.u7074 from rfl, allE_node, arows7073, irow7075, arows7074]
  all_goals rfl

theorem atot7075 : totK PD2M8K2 D2M8K2.u7075 = [0, 275066998334, 1123450272112, 1539261334275, 613050891996, 30944204704, 0, 0] := by
  rw [show D2M8K2.u7075 = KTree.node D2M8K2.u7073 (nat_lit 14969030) (nat_lit 1986335526) (nat_lit 8) D2M8K2.u7074 from rfl, totK_node, atot7073, atot7074]
  decide +kernel

theorem arows7078 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7078 = true := by
  rw [show D2M8K2.u7078 = KTree.node D2M8K2.u7076 (nat_lit 15015834) (nat_lit 3559924113) (nat_lit 0) D2M8K2.u7077 from rfl, allE_node, arows7076, irow7078, arows7077]
  all_goals rfl

theorem atot7078 : totK PD2M8K2 D2M8K2.u7078 = [0, 493752604208, 1617789686293, 1341706727696, 184951500050, 1369150432, 0, 0] := by
  rw [show D2M8K2.u7078 = KTree.node D2M8K2.u7076 (nat_lit 15015834) (nat_lit 3559924113) (nat_lit 0) D2M8K2.u7077 from rfl, totK_node, atot7076, atot7077]
  decide +kernel

theorem arows7083 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7083 = true := by
  rw [show D2M8K2.u7083 = KTree.node D2M8K2.u7081 (nat_lit 15019752) (nat_lit 2873184272) (nat_lit 0) D2M8K2.u7082 from rfl, allE_node, arows7081, irow7083, arows7082]
  all_goals rfl

theorem atot7083 : totK PD2M8K2 D2M8K2.u7083 = [0, 370065916009, 1363708908553, 1437735644013, 461611093088, 24683636622, 0, 0] := by
  rw [show D2M8K2.u7083 = KTree.node D2M8K2.u7081 (nat_lit 15019752) (nat_lit 2873184272) (nat_lit 0) D2M8K2.u7082 from rfl, totK_node, atot7081, atot7082]
  decide +kernel

theorem arows7086 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7086 = true := by
  rw [show D2M8K2.u7086 = KTree.node D2M8K2.u7084 (nat_lit 15022881) (nat_lit 1603695859) (nat_lit 0) D2M8K2.u7085 from rfl, allE_node, arows7084, irow7086, arows7085]
  all_goals rfl

theorem atot7086 : totK PD2M8K2 D2M8K2.u7086 = [0, 389683383944, 1416123560353, 1450499955711, 333943919028, 13049727234, 0, 0] := by
  rw [show D2M8K2.u7086 = KTree.node D2M8K2.u7084 (nat_lit 15022881) (nat_lit 1603695859) (nat_lit 0) D2M8K2.u7085 from rfl, totK_node, atot7084, atot7085]
  decide +kernel

theorem arows7090 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7090 = true := by
  rw [show D2M8K2.u7090 = KTree.node D2M8K2.u7088 (nat_lit 15029724) (nat_lit 2994405604) (nat_lit 0) D2M8K2.u7089 from rfl, allE_node, arows7088, irow7090, arows7089]
  all_goals rfl

theorem atot7090 : totK PD2M8K2 D2M8K2.u7090 = [0, 439488396724, 1536987396743, 1381369075304, 240806872847, 4980514959, 0, 0] := by
  rw [show D2M8K2.u7090 = KTree.node D2M8K2.u7088 (nat_lit 15029724) (nat_lit 2994405604) (nat_lit 0) D2M8K2.u7089 from rfl, totK_node, atot7088, atot7089]
  decide +kernel

theorem arows7093 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7093 = true := by
  rw [show D2M8K2.u7093 = KTree.node D2M8K2.u7091 (nat_lit 15033344) (nat_lit 2810952291) (nat_lit 0) D2M8K2.u7092 from rfl, allE_node, arows7091, irow7093, arows7092]
  all_goals rfl

theorem atot7093 : totK PD2M8K2 D2M8K2.u7093 = [0, 62729537426, 949542438970, 1856281700919, 664515688132, 28573281114, 0, 0] := by
  rw [show D2M8K2.u7093 = KTree.node D2M8K2.u7091 (nat_lit 15033344) (nat_lit 2810952291) (nat_lit 0) D2M8K2.u7092 from rfl, totK_node, atot7091, atot7092]
  decide +kernel

theorem arows7100 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7100 = true := by
  rw [show D2M8K2.u7100 = KTree.node D2M8K2.u7098 (nat_lit 15037378) (nat_lit 4061605012) (nat_lit 0) D2M8K2.u7099 from rfl, allE_node, arows7098, irow7100, arows7099]
  all_goals rfl

theorem atot7100 : totK PD2M8K2 D2M8K2.u7100 = [0, 0, 489957247583, 1677473085083, 1260113824152, 143652571966, 1206465782, 0] := by
  rw [show D2M8K2.u7100 = KTree.node D2M8K2.u7098 (nat_lit 15037378) (nat_lit 4061605012) (nat_lit 0) D2M8K2.u7099 from rfl, totK_node, atot7098, atot7099]
  decide +kernel

theorem arows7103 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7103 = true := by
  rw [show D2M8K2.u7103 = KTree.node D2M8K2.u7101 (nat_lit 15042101) (nat_lit 1844231283) (nat_lit 0) D2M8K2.u7102 from rfl, allE_node, arows7101, irow7103, arows7102]
  all_goals rfl

theorem atot7103 : totK PD2M8K2 D2M8K2.u7103 = [0, 0, 381508382736, 1464742314653, 1383195186064, 304505394308, 13016197374, 0] := by
  rw [show D2M8K2.u7103 = KTree.node D2M8K2.u7101 (nat_lit 15042101) (nat_lit 1844231283) (nat_lit 0) D2M8K2.u7102 from rfl, totK_node, atot7101, atot7102]
  decide +kernel

theorem arows7107 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7107 = true := by
  rw [show D2M8K2.u7107 = KTree.node D2M8K2.u7105 (nat_lit 15048690) (nat_lit 3417341343) (nat_lit 0) D2M8K2.u7106 from rfl, allE_node, arows7105, irow7107, arows7106]
  all_goals rfl

theorem atot7107 : totK PD2M8K2 D2M8K2.u7107 = [0, 0, 492717034230, 1597988619909, 1202915437811, 179293157027, 4574395652, 0] := by
  rw [show D2M8K2.u7107 = KTree.node D2M8K2.u7105 (nat_lit 15048690) (nat_lit 3417341343) (nat_lit 0) D2M8K2.u7106 from rfl, totK_node, atot7105, atot7106]
  decide +kernel

theorem arows7110 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7110 = true := by
  rw [show D2M8K2.u7110 = KTree.node D2M8K2.u7108 (nat_lit 15054410) (nat_lit 3217370337) (nat_lit 0) D2M8K2.u7109 from rfl, allE_node, arows7108, irow7110, arows7109]
  all_goals rfl

theorem atot7110 : totK PD2M8K2 D2M8K2.u7110 = [0, 420970288622, 1334482135615, 1329448833162, 497258549982, 32133299995, 0, 0] := by
  rw [show D2M8K2.u7110 = KTree.node D2M8K2.u7108 (nat_lit 15054410) (nat_lit 3217370337) (nat_lit 0) D2M8K2.u7109 from rfl, totK_node, atot7108, atot7109]
  decide +kernel

theorem arows7115 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7115 = true := by
  rw [show D2M8K2.u7115 = KTree.node D2M8K2.u7113 (nat_lit 15064949) (nat_lit 2066174698) (nat_lit 0) D2M8K2.u7114 from rfl, allE_node, arows7113, irow7115, arows7114]
  all_goals rfl

theorem atot7115 : totK PD2M8K2 D2M8K2.u7115 = [0, 425767693660, 1591435655931, 1404918085407, 196272816497, 1369150432, 0, 0] := by
  rw [show D2M8K2.u7115 = KTree.node D2M8K2.u7113 (nat_lit 15064949) (nat_lit 2066174698) (nat_lit 0) D2M8K2.u7114 from rfl, totK_node, atot7113, atot7114]
  decide +kernel

theorem arows7118 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7118 = true := by
  rw [show D2M8K2.u7118 = KTree.node D2M8K2.u7116 (nat_lit 15068270) (nat_lit 3083916650) (nat_lit 0) D2M8K2.u7117 from rfl, allE_node, arows7116, irow7118, arows7117]
  all_goals rfl

theorem atot7118 : totK PD2M8K2 D2M8K2.u7118 = [0, 398089907899, 1423763181510, 1401959645089, 328305422123, 13250685261, 0, 0] := by
  rw [show D2M8K2.u7118 = KTree.node D2M8K2.u7116 (nat_lit 15068270) (nat_lit 3083916650) (nat_lit 0) D2M8K2.u7117 from rfl, totK_node, atot7116, atot7117]
  decide +kernel

theorem arows7122 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7122 = true := by
  rw [show D2M8K2.u7122 = KTree.node D2M8K2.u7120 (nat_lit 15071954) (nat_lit 4005952936) (nat_lit 0) D2M8K2.u7121 from rfl, allE_node, arows7120, irow7122, arows7121]
  all_goals rfl

theorem atot7122 : totK PD2M8K2 D2M8K2.u7122 = [0, 403614254217, 1509150323037, 1453765547498, 238465849320, 4980514959, 0, 0] := by
  rw [show D2M8K2.u7122 = KTree.node D2M8K2.u7120 (nat_lit 15071954) (nat_lit 4005952936) (nat_lit 0) D2M8K2.u7121 from rfl, totK_node, atot7120, atot7121]
  decide +kernel

theorem arows7125 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7125 = true := by
  rw [show D2M8K2.u7125 = KTree.node D2M8K2.u7123 (nat_lit 15075656) (nat_lit 3550418313) (nat_lit 0) D2M8K2.u7124 from rfl, allE_node, arows7123, irow7125, arows7124]
  all_goals rfl

theorem atot7125 : totK PD2M8K2 D2M8K2.u7125 = [0, 0, 735376639432, 1895134426268, 856926008978, 47793232987, 0, 0] := by
  rw [show D2M8K2.u7125 = KTree.node D2M8K2.u7123 (nat_lit 15075656) (nat_lit 3550418313) (nat_lit 0) D2M8K2.u7124 from rfl, totK_node, atot7123, atot7124]
  decide +kernel

theorem arows7131 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7131 = true := by
  rw [show D2M8K2.u7131 = KTree.node D2M8K2.u7129 (nat_lit 15086385) (nat_lit 1851908170) (nat_lit 0) D2M8K2.u7130 from rfl, allE_node, arows7129, irow7131, arows7130]
  all_goals rfl

theorem atot7131 : totK PD2M8K2 D2M8K2.u7131 = [0, 0, 576388526559, 1748829674719, 1096478060815, 113812284384, 1239866073, 0] := by
  rw [show D2M8K2.u7131 = KTree.node D2M8K2.u7129 (nat_lit 15086385) (nat_lit 1851908170) (nat_lit 0) D2M8K2.u7130 from rfl, totK_node, atot7129, atot7130]
  decide +kernel

theorem arows7134 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7134 = true := by
  rw [show D2M8K2.u7134 = KTree.node D2M8K2.u7132 (nat_lit 15092765) (nat_lit 2062016309) (nat_lit 0) D2M8K2.u7133 from rfl, allE_node, arows7132, irow7134, arows7133]
  all_goals rfl

theorem atot7134 : totK PD2M8K2 D2M8K2.u7134 = [0, 90861460542, 861775629299, 1752622907723, 830920879179, 47631000328, 0, 0] := by
  rw [show D2M8K2.u7134 = KTree.node D2M8K2.u7132 (nat_lit 15092765) (nat_lit 2062016309) (nat_lit 0) D2M8K2.u7133 from rfl, totK_node, atot7132, atot7133]
  decide +kernel

theorem arows7138 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7138 = true := by
  rw [show D2M8K2.u7138 = KTree.node D2M8K2.u7136 (nat_lit 15097614) (nat_lit 3988799751) (nat_lit 0) D2M8K2.u7137 from rfl, allE_node, arows7136, irow7138, arows7137]
  all_goals rfl

theorem atot7138 : totK PD2M8K2 D2M8K2.u7138 = [0, 486598391392, 1603965766276, 1329279352495, 183346766084, 1369150432, 0, 0] := by
  rw [show D2M8K2.u7138 = KTree.node D2M8K2.u7136 (nat_lit 15097614) (nat_lit 3988799751) (nat_lit 0) D2M8K2.u7137 from rfl, totK_node, atot7136, atot7137]
  decide +kernel

theorem arows7141 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7141 = true := by
  rw [show D2M8K2.u7141 = KTree.node D2M8K2.u7139 (nat_lit 15101862) (nat_lit 3814176466) (nat_lit 0) D2M8K2.u7140 from rfl, allE_node, arows7139, irow7141, arows7140]
  all_goals rfl

theorem atot7141 : totK PD2M8K2 D2M8K2.u7141 = [0, 428002302948, 1418312533410, 1363887266705, 402785849342, 16462868735, 0, 0] := by
  rw [show D2M8K2.u7141 = KTree.node D2M8K2.u7139 (nat_lit 15101862) (nat_lit 3814176466) (nat_lit 0) D2M8K2.u7140 from rfl, totK_node, atot7139, atot7140]
  decide +kernel

theorem arows7146 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7146 = true := by
  rw [show D2M8K2.u7146 = KTree.node D2M8K2.u7144 (nat_lit 15105178) (nat_lit 3422382967) (nat_lit 0) D2M8K2.u7145 from rfl, allE_node, arows7144, irow7146, arows7145]
  all_goals rfl

theorem atot7146 : totK PD2M8K2 D2M8K2.u7146 = [0, 396608771916, 1430442228422, 1419200904116, 321897373708, 13049727234, 0, 0] := by
  rw [show D2M8K2.u7146 = KTree.node D2M8K2.u7144 (nat_lit 15105178) (nat_lit 3422382967) (nat_lit 0) D2M8K2.u7145 from rfl, totK_node, atot7144, atot7145]
  decide +kernel

theorem arows7149 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7149 = true := by
  rw [show D2M8K2.u7149 = KTree.node D2M8K2.u7147 (nat_lit 15109029) (nat_lit 1453953423) (nat_lit 0) D2M8K2.u7148 from rfl, allE_node, arows7147, irow7149, arows7148]
  all_goals rfl

theorem atot7149 : totK PD2M8K2 D2M8K2.u7149 = [0, 397973178292, 1434298650365, 1403943158419, 315022315099, 13250685261, 0, 0] := by
  rw [show D2M8K2.u7149 = KTree.node D2M8K2.u7147 (nat_lit 15109029) (nat_lit 1453953423) (nat_lit 0) D2M8K2.u7148 from rfl, totK_node, atot7147, atot7148]
  decide +kernel

theorem arows7153 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7153 = true := by
  rw [show D2M8K2.u7153 = KTree.node D2M8K2.u7151 (nat_lit 15112259) (nat_lit 1591451405) (nat_lit 0) D2M8K2.u7152 from rfl, allE_node, arows7151, irow7153, arows7152]
  all_goals rfl

theorem atot7153 : totK PD2M8K2 D2M8K2.u7153 = [0, 177806637211, 1159371286496, 1710329214401, 490229507051, 20694825899, 0, 0] := by
  rw [show D2M8K2.u7153 = KTree.node D2M8K2.u7151 (nat_lit 15112259) (nat_lit 1591451405) (nat_lit 0) D2M8K2.u7152 from rfl, totK_node, atot7151, atot7152]
  decide +kernel

theorem arows7156 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7156 = true := by
  rw [show D2M8K2.u7156 = KTree.node D2M8K2.u7154 (nat_lit 15119734) (nat_lit 3045974916) (nat_lit 0) D2M8K2.u7155 from rfl, allE_node, arows7154, irow7156, arows7155]
  all_goals rfl

theorem atot7156 : totK PD2M8K2 D2M8K2.u7156 = [0, 0, 554792567509, 1741902098429, 1124001512434, 117135316741, 1138244013, 0] := by
  rw [show D2M8K2.u7156 = KTree.node D2M8K2.u7154 (nat_lit 15119734) (nat_lit 3045974916) (nat_lit 0) D2M8K2.u7155 from rfl, totK_node, atot7154, atot7155]
  decide +kernel

theorem arows7167 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7167 = true := by
  rw [show D2M8K2.u7167 = KTree.node D2M8K2.u7165 (nat_lit 15125163) (nat_lit 2976010588) (nat_lit 128) D2M8K2.u7166 from rfl, allE_node, arows7165, irow7167, arows7166]
  all_goals rfl

theorem atot7167 : totK PD2M8K2 D2M8K2.u7167 = [0, 0, 722644163332, 1907683778058, 884925835993, 43457984493, 0, 0] := by
  rw [show D2M8K2.u7167 = KTree.node D2M8K2.u7165 (nat_lit 15125163) (nat_lit 2976010588) (nat_lit 128) D2M8K2.u7166 from rfl, totK_node, atot7165, atot7166]
  decide +kernel

theorem arows7170 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7170 = true := by
  rw [show D2M8K2.u7170 = KTree.node D2M8K2.u7168 (nat_lit 15131572) (nat_lit 3992702721) (nat_lit 0) D2M8K2.u7169 from rfl, allE_node, arows7168, irow7170, arows7169]
  all_goals rfl

theorem atot7170 : totK PD2M8K2 D2M8K2.u7170 = [0, 55323524080, 510939528989, 1526164752860, 1210574691033, 202004362960, 4977114383, 0] := by
  rw [show D2M8K2.u7170 = KTree.node D2M8K2.u7168 (nat_lit 15131572) (nat_lit 3992702721) (nat_lit 0) D2M8K2.u7169 from rfl, totK_node, atot7168, atot7169]
  decide +kernel

theorem arows7174 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7174 = true := by
  rw [show D2M8K2.u7174 = KTree.node D2M8K2.u7172 (nat_lit 15138916) (nat_lit 3985178986) (nat_lit 0) D2M8K2.u7173 from rfl, allE_node, arows7172, irow7174, arows7173]
  all_goals rfl

theorem atot7174 : totK PD2M8K2 D2M8K2.u7174 = [0, 453546466085, 1605607363402, 1354218578262, 189025710820, 1369150432, 0, 0] := by
  rw [show D2M8K2.u7174 = KTree.node D2M8K2.u7172 (nat_lit 15138916) (nat_lit 3985178986) (nat_lit 0) D2M8K2.u7173 from rfl, totK_node, atot7172, atot7173]
  decide +kernel

theorem arows7177 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7177 = true := by
  rw [show D2M8K2.u7177 = KTree.node D2M8K2.u7175 (nat_lit 15143051) (nat_lit 2352653459) (nat_lit 0) D2M8K2.u7176 from rfl, allE_node, arows7175, irow7177, arows7176]
  all_goals rfl

theorem atot7177 : totK PD2M8K2 D2M8K2.u7177 = [0, 409613526758, 1373996788714, 1382664936173, 469295045697, 31027424900, 0, 0] := by
  rw [show D2M8K2.u7177 = KTree.node D2M8K2.u7175 (nat_lit 15143051) (nat_lit 2352653459) (nat_lit 0) D2M8K2.u7176 from rfl, totK_node, atot7175, atot7176]
  decide +kernel

theorem arows7182 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7182 = true := by
  rw [show D2M8K2.u7182 = KTree.node D2M8K2.u7180 (nat_lit 15146255) (nat_lit 2126493717) (nat_lit 0) D2M8K2.u7181 from rfl, allE_node, arows7180, irow7182, arows7181]
  all_goals rfl

theorem atot7182 : totK PD2M8K2 D2M8K2.u7182 = [0, 400563190310, 1433863002869, 1433343792040, 328763749532, 13043783340, 0, 0] := by
  rw [show D2M8K2.u7182 = KTree.node D2M8K2.u7180 (nat_lit 15146255) (nat_lit 2126493717) (nat_lit 0) D2M8K2.u7181 from rfl, totK_node, atot7180, atot7181]
  decide +kernel

theorem arows7185 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7185 = true := by
  rw [show D2M8K2.u7185 = KTree.node D2M8K2.u7183 (nat_lit 15149756) (nat_lit 2818102197) (nat_lit 0) D2M8K2.u7184 from rfl, allE_node, arows7183, irow7185, arows7184]
  all_goals rfl

theorem atot7185 : totK PD2M8K2 D2M8K2.u7185 = [0, 438355425290, 1505212251967, 1403133901153, 267324554703, 5455647540, 0, 0] := by
  rw [show D2M8K2.u7185 = KTree.node D2M8K2.u7183 (nat_lit 15149756) (nat_lit 2818102197) (nat_lit 0) D2M8K2.u7184 from rfl, totK_node, atot7183, atot7184]
  decide +kernel

theorem arows7189 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7189 = true := by
  rw [show D2M8K2.u7189 = KTree.node D2M8K2.u7187 (nat_lit 15156676) (nat_lit 3578739131) (nat_lit 0) D2M8K2.u7188 from rfl, allE_node, arows7187, irow7189, arows7188]
  all_goals rfl

theorem atot7189 : totK PD2M8K2 D2M8K2.u7189 = [0, 231594451109, 1182485255370, 1641926882623, 513247548455, 23418599596, 0, 0] := by
  rw [show D2M8K2.u7189 = KTree.node D2M8K2.u7187 (nat_lit 15156676) (nat_lit 3578739131) (nat_lit 0) D2M8K2.u7188 from rfl, totK_node, atot7187, atot7188]
  decide +kernel

theorem arows7192 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7192 = true := by
  rw [show D2M8K2.u7192 = KTree.node D2M8K2.u7190 (nat_lit 15159889) (nat_lit 1545975605) (nat_lit 0) D2M8K2.u7191 from rfl, allE_node, arows7190, irow7192, arows7191]
  all_goals rfl

theorem atot7192 : totK PD2M8K2 D2M8K2.u7192 = [0, 0, 479175854333, 1627617020825, 1292770185616, 152132718120, 1310285577, 0] := by
  rw [show D2M8K2.u7192 = KTree.node D2M8K2.u7190 (nat_lit 15159889) (nat_lit 1545975605) (nat_lit 0) D2M8K2.u7191 from rfl, totK_node, atot7190, atot7191]
  decide +kernel

theorem arows7198 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7198 = true := by
  rw [show D2M8K2.u7198 = KTree.node D2M8K2.u7196 (nat_lit 15165569) (nat_lit 2224460729) (nat_lit 0) D2M8K2.u7197 from rfl, allE_node, arows7196, irow7198, arows7197]
  all_goals rfl

theorem atot7198 : totK PD2M8K2 D2M8K2.u7198 = [0, 0, 571612612700, 1728276046307, 1182727181362, 127421603621, 1075657031, 0] := by
  rw [show D2M8K2.u7198 = KTree.node D2M8K2.u7196 (nat_lit 15165569) (nat_lit 2224460729) (nat_lit 0) D2M8K2.u7197 from rfl, totK_node, atot7196, atot7197]
  decide +kernel

theorem arows7201 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7201 = true := by
  rw [show D2M8K2.u7201 = KTree.node D2M8K2.u7199 (nat_lit 15169546) (nat_lit 2801871273) (nat_lit 0) D2M8K2.u7200 from rfl, allE_node, arows7199, irow7201, arows7200]
  all_goals rfl

theorem atot7201 : totK PD2M8K2 D2M8K2.u7201 = [0, 0, 639571372015, 1747671649609, 1064093637039, 133020453139, 3804183361, 0] := by
  rw [show D2M8K2.u7201 = KTree.node D2M8K2.u7199 (nat_lit 15169546) (nat_lit 2801871273) (nat_lit 0) D2M8K2.u7200 from rfl, totK_node, atot7199, atot7200]
  decide +kernel

theorem arows7205 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7205 = true := by
  rw [show D2M8K2.u7205 = KTree.node D2M8K2.u7203 (nat_lit 15177745) (nat_lit 1466536523) (nat_lit 0) D2M8K2.u7204 from rfl, allE_node, arows7203, irow7205, arows7204]
  all_goals rfl

theorem atot7205 : totK PD2M8K2 D2M8K2.u7205 = [0, 0, 426231702379, 1502751307229, 1340875959699, 299582323110, 13786494048, 0] := by
  rw [show D2M8K2.u7205 = KTree.node D2M8K2.u7203 (nat_lit 15177745) (nat_lit 1466536523) (nat_lit 0) D2M8K2.u7204 from rfl, totK_node, atot7203, atot7204]
  decide +kernel

theorem arows7208 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7208 = true := by
  rw [show D2M8K2.u7208 = KTree.node D2M8K2.u7206 (nat_lit 15181378) (nat_lit 3784851736) (nat_lit 0) D2M8K2.u7207 from rfl, allE_node, arows7206, irow7208, arows7207]
  all_goals rfl

theorem atot7208 : totK PD2M8K2 D2M8K2.u7208 = [0, 0, 435552175627, 1601613193028, 1379665999205, 182985630666, 1369150432, 0] := by
  rw [show D2M8K2.u7208 = KTree.node D2M8K2.u7206 (nat_lit 15181378) (nat_lit 3784851736) (nat_lit 0) D2M8K2.u7207 from rfl, totK_node, atot7206, atot7207]
  decide +kernel

theorem arows7213 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7213 = true := by
  rw [show D2M8K2.u7213 = KTree.node D2M8K2.u7211 (nat_lit 15188177) (nat_lit 2164627135) (nat_lit 0) D2M8K2.u7212 from rfl, allE_node, arows7211, irow7213, arows7212]
  all_goals rfl

theorem atot7213 : totK PD2M8K2 D2M8K2.u7213 = [0, 0, 428663325387, 1444522250032, 1358643206719, 280130416872, 12891658009, 0] := by
  rw [show D2M8K2.u7213 = KTree.node D2M8K2.u7211 (nat_lit 15188177) (nat_lit 2164627135) (nat_lit 0) D2M8K2.u7212 from rfl, totK_node, atot7211, atot7212]
  decide +kernel

theorem arows7216 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7216 = true := by
  rw [show D2M8K2.u7216 = KTree.node D2M8K2.u7214 (nat_lit 15192372) (nat_lit 3173569772) (nat_lit 0) D2M8K2.u7215 from rfl, allE_node, arows7214, irow7216, arows7215]
  all_goals rfl

theorem atot7216 : totK PD2M8K2 D2M8K2.u7216 = [0, 0, 498955532886, 1632803480470, 1231448728684, 139090803865, 1198073392, 0] := by
  rw [show D2M8K2.u7216 = KTree.node D2M8K2.u7214 (nat_lit 15192372) (nat_lit 3173569772) (nat_lit 0) D2M8K2.u7215 from rfl, totK_node, atot7214, atot7215]
  decide +kernel

theorem arows7220 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7220 = true := by
  rw [show D2M8K2.u7220 = KTree.node D2M8K2.u7218 (nat_lit 15196111) (nat_lit 2421340595) (nat_lit 0) D2M8K2.u7219 from rfl, allE_node, arows7218, irow7220, arows7219]
  all_goals rfl

theorem atot7220 : totK PD2M8K2 D2M8K2.u7220 = [0, 0, 453750280337, 1571149269198, 1327522970754, 189092334061, 4934531535, 0] := by
  rw [show D2M8K2.u7220 = KTree.node D2M8K2.u7218 (nat_lit 15196111) (nat_lit 2421340595) (nat_lit 0) D2M8K2.u7219 from rfl, totK_node, atot7218, atot7219]
  decide +kernel

theorem arows7223 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7223 = true := by
  rw [show D2M8K2.u7223 = KTree.node D2M8K2.u7221 (nat_lit 15199596) (nat_lit 3216297692) (nat_lit 0) D2M8K2.u7222 from rfl, allE_node, arows7221, irow7223, arows7222]
  all_goals rfl

theorem atot7223 : totK PD2M8K2 D2M8K2.u7223 = [0, 0, 0, 863264649052, 1934335053032, 682297983452, 32224664412, 0] := by
  rw [show D2M8K2.u7223 = KTree.node D2M8K2.u7221 (nat_lit 15199596) (nat_lit 3216297692) (nat_lit 0) D2M8K2.u7222 from rfl, totK_node, atot7221, atot7222]
  decide +kernel

theorem arows7230 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7230 = true := by
  rw [show D2M8K2.u7230 = KTree.node D2M8K2.u7228 (nat_lit 15207005) (nat_lit 2332668471) (nat_lit 0) D2M8K2.u7229 from rfl, allE_node, arows7228, irow7230, arows7229]
  all_goals rfl

theorem atot7230 : totK PD2M8K2 D2M8K2.u7230 = [0, 0, 0, 599534264443, 1720318262128, 1027740523023, 123748292949, 1369150432] := by
  rw [show D2M8K2.u7230 = KTree.node D2M8K2.u7228 (nat_lit 15207005) (nat_lit 2332668471) (nat_lit 0) D2M8K2.u7229 from rfl, totK_node, atot7228, atot7229]
  decide +kernel

theorem arows7233 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7233 = true := by
  rw [show D2M8K2.u7233 = KTree.node D2M8K2.u7231 (nat_lit 15214276) (nat_lit 3017917433) (nat_lit 0) D2M8K2.u7232 from rfl, allE_node, arows7231, irow7233, arows7232]
  all_goals rfl

theorem atot7233 : totK PD2M8K2 D2M8K2.u7233 = [0, 0, 0, 954903394611, 1966259441142, 564004690234, 20951781549, 0] := by
  rw [show D2M8K2.u7233 = KTree.node D2M8K2.u7231 (nat_lit 15214276) (nat_lit 3017917433) (nat_lit 0) D2M8K2.u7232 from rfl, totK_node, atot7231, atot7232]
  decide +kernel

theorem arows7237 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7237 = true := by
  rw [show D2M8K2.u7237 = KTree.node D2M8K2.u7235 (nat_lit 15263003) (nat_lit 1249659897) (nat_lit 0) D2M8K2.u7236 from rfl, allE_node, arows7235, irow7237, arows7236]
  all_goals rfl

theorem atot7237 : totK PD2M8K2 D2M8K2.u7237 = [0, 0, 415868634734, 1503413806251, 1371273721228, 243017496478, 10301178929, 0] := by
  rw [show D2M8K2.u7237 = KTree.node D2M8K2.u7235 (nat_lit 15263003) (nat_lit 1249659897) (nat_lit 0) D2M8K2.u7236 from rfl, totK_node, atot7235, atot7236]
  decide +kernel

theorem arows7240 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7240 = true := by
  rw [show D2M8K2.u7240 = KTree.node D2M8K2.u7238 (nat_lit 15267209) (nat_lit 1794605220) (nat_lit 0) D2M8K2.u7239 from rfl, allE_node, arows7238, irow7240, arows7239]
  all_goals rfl

theorem atot7240 : totK PD2M8K2 D2M8K2.u7240 = [0, 0, 517509224338, 1621259456078, 1295174138283, 233910618363, 5284349065, 0] := by
  rw [show D2M8K2.u7240 = KTree.node D2M8K2.u7238 (nat_lit 15267209) (nat_lit 1794605220) (nat_lit 0) D2M8K2.u7239 from rfl, totK_node, atot7238, atot7239]
  decide +kernel

theorem arows7245 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7245 = true := by
  rw [show D2M8K2.u7245 = KTree.node D2M8K2.u7243 (nat_lit 15270539) (nat_lit 2166252278) (nat_lit 0) D2M8K2.u7244 from rfl, allE_node, arows7243, irow7245, arows7244]
  all_goals rfl

theorem atot7245 : totK PD2M8K2 D2M8K2.u7245 = [0, 0, 370645405725, 1423100081591, 1463255969367, 319961334877, 13049727234, 0] := by
  rw [show D2M8K2.u7245 = KTree.node D2M8K2.u7243 (nat_lit 15270539) (nat_lit 2166252278) (nat_lit 0) D2M8K2.u7244 from rfl, totK_node, atot7243, atot7244]
  decide +kernel

theorem arows7248 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7248 = true := by
  rw [show D2M8K2.u7248 = KTree.node D2M8K2.u7246 (nat_lit 15277390) (nat_lit 3464034730) (nat_lit 0) D2M8K2.u7247 from rfl, allE_node, arows7246, irow7248, arows7247]
  all_goals rfl

theorem atot7248 : totK PD2M8K2 D2M8K2.u7248 = [0, 0, 469179281895, 1555697267696, 1325598452884, 202584764224, 4917269347, 0] := by
  rw [show D2M8K2.u7248 = KTree.node D2M8K2.u7246 (nat_lit 15277390) (nat_lit 3464034730) (nat_lit 0) D2M8K2.u7247 from rfl, totK_node, atot7246, atot7247]
  decide +kernel

theorem arows7252 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7252 = true := by
  rw [show D2M8K2.u7252 = KTree.node D2M8K2.u7250 (nat_lit 15281064) (nat_lit 1661285134) (nat_lit 128) D2M8K2.u7251 from rfl, allE_node, arows7250, irow7252, arows7251]
  all_goals rfl

theorem atot7252 : totK PD2M8K2 D2M8K2.u7252 = [0, 0, 406746344020, 1461904194000, 1405729788924, 300458471293, 13684302317, 0] := by
  rw [show D2M8K2.u7252 = KTree.node D2M8K2.u7250 (nat_lit 15281064) (nat_lit 1661285134) (nat_lit 128) D2M8K2.u7251 from rfl, totK_node, atot7250, atot7251]
  decide +kernel

theorem arows7255 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7255 = true := by
  rw [show D2M8K2.u7255 = KTree.node D2M8K2.u7253 (nat_lit 15305572) (nat_lit 3780315073) (nat_lit 0) D2M8K2.u7254 from rfl, allE_node, arows7253, irow7255, arows7254]
  all_goals rfl

theorem atot7255 : totK PD2M8K2 D2M8K2.u7255 = [0, 0, 509729756085, 1648404363644, 1274746777409, 150493878570, 1369150432, 0] := by
  rw [show D2M8K2.u7255 = KTree.node D2M8K2.u7253 (nat_lit 15305572) (nat_lit 3780315073) (nat_lit 0) D2M8K2.u7254 from rfl, totK_node, atot7253, atot7254]
  decide +kernel

theorem arows7261 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7261 = true := by
  rw [show D2M8K2.u7261 = KTree.node D2M8K2.u7259 (nat_lit 15317600) (nat_lit 3764603619) (nat_lit 0) D2M8K2.u7260 from rfl, allE_node, arows7259, irow7261, arows7260]
  all_goals rfl

theorem atot7261 : totK PD2M8K2 D2M8K2.u7261 = [0, 0, 568424840723, 1730947200564, 1131683951132, 111110580343, 1096505104, 0] := by
  rw [show D2M8K2.u7261 = KTree.node D2M8K2.u7259 (nat_lit 15317600) (nat_lit 3764603619) (nat_lit 0) D2M8K2.u7260 from rfl, totK_node, atot7259, atot7260]
  decide +kernel

theorem arows7264 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7264 = true := by
  rw [show D2M8K2.u7264 = KTree.node D2M8K2.u7262 (nat_lit 15321895) (nat_lit 2348484743) (nat_lit 0) D2M8K2.u7263 from rfl, allE_node, arows7262, irow7264, arows7263]
  all_goals rfl

theorem atot7264 : totK PD2M8K2 D2M8K2.u7264 = [0, 0, 691809699755, 1813897106789, 1022398018865, 76976640283, 0, 0] := by
  rw [show D2M8K2.u7264 = KTree.node D2M8K2.u7262 (nat_lit 15321895) (nat_lit 2348484743) (nat_lit 0) D2M8K2.u7263 from rfl, totK_node, atot7262, atot7263]
  decide +kernel

theorem arows7268 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7268 = true := by
  rw [show D2M8K2.u7268 = KTree.node D2M8K2.u7266 (nat_lit 15347815) (nat_lit 2316084732) (nat_lit 0) D2M8K2.u7267 from rfl, allE_node, arows7266, irow7268, arows7267]
  all_goals rfl

theorem atot7268 : totK PD2M8K2 D2M8K2.u7268 = [0, 0, 451058014569, 1615795079438, 1340089062193, 167402100079, 1369150432, 0] := by
  rw [show D2M8K2.u7268 = KTree.node D2M8K2.u7266 (nat_lit 15347815) (nat_lit 2316084732) (nat_lit 0) D2M8K2.u7267 from rfl, totK_node, atot7266, atot7267]
  decide +kernel

theorem arows7271 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7271 = true := by
  rw [show D2M8K2.u7271 = KTree.node D2M8K2.u7269 (nat_lit 15352177) (nat_lit 1504877981) (nat_lit 0) D2M8K2.u7270 from rfl, allE_node, arows7269, irow7271, arows7270]
  all_goals rfl

theorem atot7271 : totK PD2M8K2 D2M8K2.u7271 = [0, 0, 411951061046, 1561033802724, 1406072534964, 209538073639, 2573880433, 0] := by
  rw [show D2M8K2.u7271 = KTree.node D2M8K2.u7269 (nat_lit 15352177) (nat_lit 1504877981) (nat_lit 0) D2M8K2.u7270 from rfl, totK_node, atot7269, atot7270]
  decide +kernel

theorem arows7276 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7276 = true := by
  rw [show D2M8K2.u7276 = KTree.node D2M8K2.u7274 (nat_lit 15355988) (nat_lit 3665217836) (nat_lit 0) D2M8K2.u7275 from rfl, allE_node, arows7274, irow7276, arows7275]
  all_goals rfl

theorem atot7276 : totK PD2M8K2 D2M8K2.u7276 = [0, 0, 377767641247, 1454972014116, 1411754755374, 273509710756, 13017203568, 0] := by
  rw [show D2M8K2.u7276 = KTree.node D2M8K2.u7274 (nat_lit 15355988) (nat_lit 3665217836) (nat_lit 0) D2M8K2.u7275 from rfl, totK_node, atot7274, atot7275]
  decide +kernel

theorem arows7279 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7279 = true := by
  rw [show D2M8K2.u7279 = KTree.node D2M8K2.u7277 (nat_lit 15359638) (nat_lit 2624461013) (nat_lit 0) D2M8K2.u7278 from rfl, allE_node, arows7277, irow7279, arows7278]
  all_goals rfl

theorem atot7279 : totK PD2M8K2 D2M8K2.u7279 = [0, 0, 433886737069, 1564278895592, 1386100324649, 200364836404, 2165917952, 0] := by
  rw [show D2M8K2.u7279 = KTree.node D2M8K2.u7277 (nat_lit 15359638) (nat_lit 2624461013) (nat_lit 0) D2M8K2.u7278 from rfl, totK_node, atot7277, atot7278]
  decide +kernel

theorem arows7283 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7283 = true := by
  rw [show D2M8K2.u7283 = KTree.node D2M8K2.u7281 (nat_lit 15387645) (nat_lit 1056186219) (nat_lit 512) D2M8K2.u7282 from rfl, allE_node, arows7281, irow7283, arows7282]
  all_goals rfl

theorem atot7283 : totK PD2M8K2 D2M8K2.u7283 = [0, 0, 505185190147, 1629532975062, 1260943632252, 173194487331, 4183747439, 0] := by
  rw [show D2M8K2.u7283 = KTree.node D2M8K2.u7281 (nat_lit 15387645) (nat_lit 1056186219) (nat_lit 512) D2M8K2.u7282 from rfl, totK_node, atot7281, atot7282]
  decide +kernel

theorem arows7286 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7286 = true := by
  rw [show D2M8K2.u7286 = KTree.node D2M8K2.u7284 (nat_lit 15393345) (nat_lit 1639738405) (nat_lit 0) D2M8K2.u7285 from rfl, allE_node, arows7284, irow7286, arows7285]
  all_goals rfl

theorem atot7286 : totK PD2M8K2 D2M8K2.u7286 = [0, 0, 656552972949, 1813748481262, 1087161477237, 92609843893, 0, 0] := by
  rw [show D2M8K2.u7286 = KTree.node D2M8K2.u7284 (nat_lit 15393345) (nat_lit 1639738405) (nat_lit 0) D2M8K2.u7285 from rfl, totK_node, atot7284, atot7285]
  decide +kernel

theorem arows7294 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7294 = true := by
  rw [show D2M8K2.u7294 = KTree.node D2M8K2.u7292 (nat_lit 15396940) (nat_lit 3542743622) (nat_lit 0) D2M8K2.u7293 from rfl, allE_node, arows7292, irow7294, arows7293]
  all_goals rfl

theorem atot7294 : totK PD2M8K2 D2M8K2.u7294 = [0, 0, 553159486454, 1606536094726, 1265461300718, 214476671453, 5138457373, 0] := by
  rw [show D2M8K2.u7294 = KTree.node D2M8K2.u7292 (nat_lit 15396940) (nat_lit 3542743622) (nat_lit 0) D2M8K2.u7293 from rfl, totK_node, atot7292, atot7293]
  decide +kernel

theorem arows7297 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7297 = true := by
  rw [show D2M8K2.u7297 = KTree.node D2M8K2.u7295 (nat_lit 15405270) (nat_lit 3596172723) (nat_lit 0) D2M8K2.u7296 from rfl, allE_node, arows7295, irow7297, arows7296]
  all_goals rfl

theorem atot7297 : totK PD2M8K2 D2M8K2.u7297 = [0, 94445126902, 506670672447, 1355317734874, 1373483290298, 315701777383, 13864292063, 0] := by
  rw [show D2M8K2.u7297 = KTree.node D2M8K2.u7295 (nat_lit 15405270) (nat_lit 3596172723) (nat_lit 0) D2M8K2.u7296 from rfl, totK_node, atot7295, atot7296]
  decide +kernel

theorem arows7301 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7301 = true := by
  rw [show D2M8K2.u7301 = KTree.node D2M8K2.u7299 (nat_lit 15474569) (nat_lit 1794605220) (nat_lit 0) D2M8K2.u7300 from rfl, allE_node, arows7299, irow7301, arows7300]
  all_goals rfl

theorem atot7301 : totK PD2M8K2 D2M8K2.u7301 = [0, 354984806307, 1320246515281, 1460509436956, 494494691317, 30804453458, 0, 0] := by
  rw [show D2M8K2.u7301 = KTree.node D2M8K2.u7299 (nat_lit 15474569) (nat_lit 1794605220) (nat_lit 0) D2M8K2.u7300 from rfl, totK_node, atot7299, atot7300]
  decide +kernel

theorem arows7304 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7304 = true := by
  rw [show D2M8K2.u7304 = KTree.node D2M8K2.u7302 (nat_lit 15477268) (nat_lit 3546210843) (nat_lit 0) D2M8K2.u7303 from rfl, allE_node, arows7302, irow7304, arows7303]
  all_goals rfl

theorem atot7304 : totK PD2M8K2 D2M8K2.u7304 = [0, 423438397692, 1457542664169, 1399715700795, 341402679708, 15207866557, 0, 0] := by
  rw [show D2M8K2.u7304 = KTree.node D2M8K2.u7302 (nat_lit 15477268) (nat_lit 3546210843) (nat_lit 0) D2M8K2.u7303 from rfl, totK_node, atot7302, atot7303]
  decide +kernel

theorem arows7309 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7309 = true := by
  rw [show D2M8K2.u7309 = KTree.node D2M8K2.u7307 (nat_lit 15480678) (nat_lit 3836535373) (nat_lit 0) D2M8K2.u7308 from rfl, allE_node, arows7307, irow7309, arows7308]
  all_goals rfl

theorem atot7309 : totK PD2M8K2 D2M8K2.u7309 = [0, 404363623294, 1443730012825, 1427262024656, 314027594560, 10295059931, 0, 0] := by
  rw [show D2M8K2.u7309 = KTree.node D2M8K2.u7307 (nat_lit 15480678) (nat_lit 3836535373) (nat_lit 0) D2M8K2.u7308 from rfl, totK_node, atot7307, atot7308]
  decide +kernel

theorem arows7312 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7312 = true := by
  rw [show D2M8K2.u7312 = KTree.node D2M8K2.u7310 (nat_lit 15483852) (nat_lit 3075521331) (nat_lit 0) D2M8K2.u7311 from rfl, allE_node, arows7310, irow7312, arows7311]
  all_goals rfl

theorem atot7312 : totK PD2M8K2 D2M8K2.u7312 = [0, 417592767332, 1532796848353, 1419496474576, 232021059332, 2348208889, 0, 0] := by
  rw [show D2M8K2.u7312 = KTree.node D2M8K2.u7310 (nat_lit 15483852) (nat_lit 3075521331) (nat_lit 0) D2M8K2.u7311 from rfl, totK_node, atot7310, atot7311]
  decide +kernel

theorem arows7316 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7316 = true := by
  rw [show D2M8K2.u7316 = KTree.node D2M8K2.u7314 (nat_lit 15487374) (nat_lit 3942508459) (nat_lit 0) D2M8K2.u7315 from rfl, allE_node, arows7314, irow7316, arows7315]
  all_goals rfl

theorem atot7316 : totK PD2M8K2 D2M8K2.u7316 = [0, 422883574688, 1453513131126, 1404020336482, 319896725840, 8796828500, 0, 0] := by
  rw [show D2M8K2.u7316 = KTree.node D2M8K2.u7314 (nat_lit 15487374) (nat_lit 3942508459) (nat_lit 0) D2M8K2.u7315 from rfl, totK_node, atot7314, atot7315]
  decide +kernel

theorem arows7319 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7319 = true := by
  rw [show D2M8K2.u7319 = KTree.node D2M8K2.u7317 (nat_lit 15494248) (nat_lit 3100749918) (nat_lit 0) D2M8K2.u7318 from rfl, allE_node, arows7317, irow7319, arows7318]
  all_goals rfl

theorem atot7319 : totK PD2M8K2 D2M8K2.u7319 = [0, 0, 540160219506, 1646934710800, 1202114368563, 248536557530, 21385604922, 0] := by
  rw [show D2M8K2.u7319 = KTree.node D2M8K2.u7317 (nat_lit 15494248) (nat_lit 3100749918) (nat_lit 0) D2M8K2.u7318 from rfl, totK_node, atot7317, atot7318]
  decide +kernel

theorem arows7325 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7325 = true := by
  rw [show D2M8K2.u7325 = KTree.node D2M8K2.u7323 (nat_lit 15497083) (nat_lit 2093697876) (nat_lit 0) D2M8K2.u7324 from rfl, allE_node, arows7323, irow7325, arows7324]
  all_goals rfl

theorem atot7325 : totK PD2M8K2 D2M8K2.u7325 = [0, 0, 421515400663, 1394790868033, 1365760764776, 394587205595, 15536268932, 0] := by
  rw [show D2M8K2.u7325 = KTree.node D2M8K2.u7323 (nat_lit 15497083) (nat_lit 2093697876) (nat_lit 0) D2M8K2.u7324 from rfl, totK_node, atot7323, atot7324]
  decide +kernel

theorem arows7328 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7328 = true := by
  rw [show D2M8K2.u7328 = KTree.node D2M8K2.u7326 (nat_lit 15500648) (nat_lit 3520120852) (nat_lit 0) D2M8K2.u7327 from rfl, allE_node, arows7326, irow7328, arows7327]
  all_goals rfl

theorem atot7328 : totK PD2M8K2 D2M8K2.u7328 = [0, 0, 402447167899, 1529078680686, 1435809916433, 258534016101, 5159868635, 0] := by
  rw [show D2M8K2.u7328 = KTree.node D2M8K2.u7326 (nat_lit 15500648) (nat_lit 3520120852) (nat_lit 0) D2M8K2.u7327 from rfl, totK_node, atot7326, atot7327]
  decide +kernel

theorem arows7332 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7332 = true := by
  rw [show D2M8K2.u7332 = KTree.node D2M8K2.u7330 (nat_lit 15504205) (nat_lit 1258701087) (nat_lit 0) D2M8K2.u7331 from rfl, allE_node, arows7330, irow7332, arows7331]
  all_goals rfl

theorem atot7332 : totK PD2M8K2 D2M8K2.u7332 = [0, 0, 415692793784, 1519201673906, 1399248646218, 240443075411, 5218872685, 0] := by
  rw [show D2M8K2.u7332 = KTree.node D2M8K2.u7330 (nat_lit 15504205) (nat_lit 1258701087) (nat_lit 0) D2M8K2.u7331 from rfl, totK_node, atot7330, atot7331]
  decide +kernel

theorem arows7335 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7335 = true := by
  rw [show D2M8K2.u7335 = KTree.node D2M8K2.u7333 (nat_lit 15507823) (nat_lit 1635698009) (nat_lit 0) D2M8K2.u7334 from rfl, allE_node, arows7333, irow7335, arows7334]
  all_goals rfl

theorem atot7335 : totK PD2M8K2 D2M8K2.u7335 = [0, 0, 420912922752, 1542252511629, 1418051174440, 239362132425, 2653815552, 0] := by
  rw [show D2M8K2.u7335 = KTree.node D2M8K2.u7333 (nat_lit 15507823) (nat_lit 1635698009) (nat_lit 0) D2M8K2.u7334 from rfl, totK_node, atot7333, atot7334]
  decide +kernel

theorem arows7340 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7340 = true := by
  rw [show D2M8K2.u7340 = KTree.node D2M8K2.u7338 (nat_lit 15511824) (nat_lit 3683708532) (nat_lit 0) D2M8K2.u7339 from rfl, allE_node, arows7338, irow7340, arows7339]
  all_goals rfl

theorem atot7340 : totK PD2M8K2 D2M8K2.u7340 = [0, 400733087007, 1299812465712, 1174770838200, 541160394762, 172767637699, 8063697217, 0] := by
  rw [show D2M8K2.u7340 = KTree.node D2M8K2.u7338 (nat_lit 15511824) (nat_lit 3683708532) (nat_lit 0) D2M8K2.u7339 from rfl, totK_node, atot7338, atot7339]
  decide +kernel

theorem arows7343 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7343 = true := by
  rw [show D2M8K2.u7343 = KTree.node D2M8K2.u7341 (nat_lit 15515573) (nat_lit 1813637861) (nat_lit 0) D2M8K2.u7342 from rfl, allE_node, arows7341, irow7343, arows7342]
  all_goals rfl

theorem atot7343 : totK PD2M8K2 D2M8K2.u7343 = [0, 367189792200, 1357395999097, 1437159824871, 460120010006, 29387185185, 0, 0] := by
  rw [show D2M8K2.u7343 = KTree.node D2M8K2.u7341 (nat_lit 15515573) (nat_lit 1813637861) (nat_lit 0) D2M8K2.u7342 from rfl, totK_node, atot7341, atot7342]
  decide +kernel

theorem arows7347 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7347 = true := by
  rw [show D2M8K2.u7347 = KTree.node D2M8K2.u7345 (nat_lit 15518290) (nat_lit 4093410283) (nat_lit 0) D2M8K2.u7346 from rfl, allE_node, arows7345, irow7347, arows7346]
  all_goals rfl

theorem atot7347 : totK PD2M8K2 D2M8K2.u7347 = [0, 441464276821, 1480864820749, 1385290124814, 335243441818, 10519537793, 0, 0] := by
  rw [show D2M8K2.u7347 = KTree.node D2M8K2.u7345 (nat_lit 15518290) (nat_lit 4093410283) (nat_lit 0) D2M8K2.u7346 from rfl, totK_node, atot7345, atot7346]
  decide +kernel

theorem arows7350 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7350 = true := by
  rw [show D2M8K2.u7350 = KTree.node D2M8K2.u7348 (nat_lit 15525052) (nat_lit 3946198869) (nat_lit 0) D2M8K2.u7349 from rfl, allE_node, arows7348, irow7350, arows7349]
  all_goals rfl

theorem atot7350 : totK PD2M8K2 D2M8K2.u7350 = [0, 411709460236, 1476365943983, 1407126722126, 285344087551, 11836626177, 0, 0] := by
  rw [show D2M8K2.u7350 = KTree.node D2M8K2.u7348 (nat_lit 15525052) (nat_lit 3946198869) (nat_lit 0) D2M8K2.u7349 from rfl, totK_node, atot7348, atot7349]
  decide +kernel

theorem arows7357 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7357 = true := by
  rw [show D2M8K2.u7357 = KTree.node D2M8K2.u7355 (nat_lit 15528596) (nat_lit 3084738630) (nat_lit 0) D2M8K2.u7356 from rfl, allE_node, arows7355, irow7357, arows7356]
  all_goals rfl

theorem atot7357 : totK PD2M8K2 D2M8K2.u7357 = [0, 417115925447, 1482776127759, 1423775023495, 294736736815, 6188177409, 0, 0] := by
  rw [show D2M8K2.u7357 = KTree.node D2M8K2.u7355 (nat_lit 15528596) (nat_lit 3084738630) (nat_lit 0) D2M8K2.u7356 from rfl, totK_node, atot7355, atot7356]
  decide +kernel

theorem arows7360 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7360 = true := by
  rw [show D2M8K2.u7360 = KTree.node D2M8K2.u7358 (nat_lit 15532460) (nat_lit 3750605561) (nat_lit 0) D2M8K2.u7359 from rfl, allE_node, arows7358, irow7360, arows7359]
  all_goals rfl

theorem atot7360 : totK PD2M8K2 D2M8K2.u7360 = [0, 0, 736571998299, 1866003412241, 925536142815, 69926477087, 0, 0] := by
  rw [show D2M8K2.u7360 = KTree.node D2M8K2.u7358 (nat_lit 15532460) (nat_lit 3750605561) (nat_lit 0) D2M8K2.u7359 from rfl, totK_node, atot7358, atot7359]
  decide +kernel

theorem arows7364 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7364 = true := by
  rw [show D2M8K2.u7364 = KTree.node D2M8K2.u7362 (nat_lit 15538706) (nat_lit 4088148442) (nat_lit 0) D2M8K2.u7363 from rfl, allE_node, arows7362, irow7364, arows7363]
  all_goals rfl

theorem atot7364 : totK PD2M8K2 D2M8K2.u7364 = [0, 0, 632277083281, 1778143189760, 1070400818366, 122113097794, 1162935789, 0] := by
  rw [show D2M8K2.u7364 = KTree.node D2M8K2.u7362 (nat_lit 15538706) (nat_lit 4088148442) (nat_lit 0) D2M8K2.u7363 from rfl, totK_node, atot7362, atot7363]
  decide +kernel

theorem arows7367 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7367 = true := by
  rw [show D2M8K2.u7367 = KTree.node D2M8K2.u7365 (nat_lit 15545550) (nat_lit 3777177957) (nat_lit 0) D2M8K2.u7366 from rfl, allE_node, arows7365, irow7367, arows7366]
  all_goals rfl

theorem atot7367 : totK PD2M8K2 D2M8K2.u7367 = [0, 0, 410637294450, 1505620769859, 1315922567512, 281053573710, 12874862223, 0] := by
  rw [show D2M8K2.u7367 = KTree.node D2M8K2.u7365 (nat_lit 15545550) (nat_lit 3777177957) (nat_lit 0) D2M8K2.u7366 from rfl, totK_node, atot7365, atot7366]
  decide +kernel

theorem arows7372 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7372 = true := by
  rw [show D2M8K2.u7372 = KTree.node D2M8K2.u7370 (nat_lit 15549228) (nat_lit 2837175760) (nat_lit 0) D2M8K2.u7371 from rfl, allE_node, arows7370, irow7372, arows7371]
  all_goals rfl

theorem atot7372 : totK PD2M8K2 D2M8K2.u7372 = [0, 166746023996, 797280928343, 1519880318178, 984608208401, 136139254366, 3552795014, 0] := by
  rw [show D2M8K2.u7372 = KTree.node D2M8K2.u7370 (nat_lit 15549228) (nat_lit 2837175760) (nat_lit 0) D2M8K2.u7371 from rfl, totK_node, atot7370, atot7371]
  decide +kernel

theorem arows7375 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7375 = true := by
  rw [show D2M8K2.u7375 = KTree.node D2M8K2.u7373 (nat_lit 15557697) (nat_lit 1697897288) (nat_lit 0) D2M8K2.u7374 from rfl, allE_node, arows7373, irow7375, arows7374]
  all_goals rfl

theorem atot7375 : totK PD2M8K2 D2M8K2.u7375 = [0, 299392163243, 1201449329623, 1503660954368, 580236768563, 37595089999, 0, 0] := by
  rw [show D2M8K2.u7375 = KTree.node D2M8K2.u7373 (nat_lit 15557697) (nat_lit 1697897288) (nat_lit 0) D2M8K2.u7374 from rfl, totK_node, atot7373, atot7374]
  decide +kernel

theorem arows7379 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7379 = true := by
  rw [show D2M8K2.u7379 = KTree.node D2M8K2.u7377 (nat_lit 15563941) (nat_lit 1359356173) (nat_lit 0) D2M8K2.u7378 from rfl, allE_node, arows7377, irow7379, arows7378]
  all_goals rfl

theorem atot7379 : totK PD2M8K2 D2M8K2.u7379 = [0, 390292462438, 1442758711567, 1427857224884, 333025429863, 13250685261, 0, 0] := by
  rw [show D2M8K2.u7379 = KTree.node D2M8K2.u7377 (nat_lit 15563941) (nat_lit 1359356173) (nat_lit 0) D2M8K2.u7378 from rfl, totK_node, atot7377, atot7378]
  decide +kernel

theorem arows7382 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7382 = true := by
  rw [show D2M8K2.u7382 = KTree.node D2M8K2.u7380 (nat_lit 15567051) (nat_lit 3631454252) (nat_lit 0) D2M8K2.u7381 from rfl, allE_node, arows7380, irow7382, arows7381]
  all_goals rfl

theorem atot7382 : totK PD2M8K2 D2M8K2.u7382 = [0, 468122229880, 1593741597846, 1337101650358, 213538008362, 3884009855, 0, 0] := by
  rw [show D2M8K2.u7382 = KTree.node D2M8K2.u7380 (nat_lit 15567051) (nat_lit 3631454252) (nat_lit 0) D2M8K2.u7381 from rfl, totK_node, atot7380, atot7381]
  decide +kernel

theorem arows7388 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7388 = true := by
  rw [show D2M8K2.u7388 = KTree.node D2M8K2.u7386 (nat_lit 15571028) (nat_lit 2586440166) (nat_lit 0) D2M8K2.u7387 from rfl, allE_node, arows7386, irow7388, arows7387]
  all_goals rfl

theorem atot7388 : totK PD2M8K2 D2M8K2.u7388 = [0, 337788462646, 1327083319001, 1509846472269, 433816127837, 18302234057, 0, 0] := by
  rw [show D2M8K2.u7388 = KTree.node D2M8K2.u7386 (nat_lit 15571028) (nat_lit 2586440166) (nat_lit 0) D2M8K2.u7387 from rfl, totK_node, atot7386, atot7387]
  decide +kernel

theorem arows7391 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7391 = true := by
  rw [show D2M8K2.u7391 = KTree.node D2M8K2.u7389 (nat_lit 15577768) (nat_lit 3734820684) (nat_lit 0) D2M8K2.u7390 from rfl, allE_node, arows7389, irow7391, arows7390]
  all_goals rfl

theorem atot7391 : totK PD2M8K2 D2M8K2.u7391 = [0, 0, 728839104903, 1860810404600, 986168987852, 75009651504, 0, 0] := by
  rw [show D2M8K2.u7391 = KTree.node D2M8K2.u7389 (nat_lit 15577768) (nat_lit 3734820684) (nat_lit 0) D2M8K2.u7390 from rfl, totK_node, atot7389, atot7390]
  decide +kernel

theorem arows7395 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7395 = true := by
  rw [show D2M8K2.u7395 = KTree.node D2M8K2.u7393 (nat_lit 15586356) (nat_lit 3155980153) (nat_lit 0) D2M8K2.u7394 from rfl, allE_node, arows7393, irow7395, arows7394]
  all_goals rfl

theorem atot7395 : totK PD2M8K2 D2M8K2.u7395 = [0, 0, 486140364600, 1596533037867, 1271831221622, 219054621256, 5757108999, 0] := by
  rw [show D2M8K2.u7395 = KTree.node D2M8K2.u7393 (nat_lit 15586356) (nat_lit 3155980153) (nat_lit 0) D2M8K2.u7394 from rfl, totK_node, atot7393, atot7394]
  decide +kernel

theorem arows7398 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7398 = true := by
  rw [show D2M8K2.u7398 = KTree.node D2M8K2.u7396 (nat_lit 15590420) (nat_lit 3494746384) (nat_lit 0) D2M8K2.u7397 from rfl, allE_node, arows7396, irow7398, arows7397]
  all_goals rfl

theorem atot7398 : totK PD2M8K2 D2M8K2.u7398 = [0, 85146215446, 552830990931, 1545940782474, 1244546459214, 149603482882, 1376099875, 0] := by
  rw [show D2M8K2.u7398 = KTree.node D2M8K2.u7396 (nat_lit 15590420) (nat_lit 3494746384) (nat_lit 0) D2M8K2.u7397 from rfl, totK_node, atot7396, atot7397]
  decide +kernel

theorem arows7403 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7403 = true := by
  rw [show D2M8K2.u7403 = KTree.node D2M8K2.u7401 (nat_lit 15595879) (nat_lit 2026952211) (nat_lit 0) D2M8K2.u7402 from rfl, allE_node, arows7401, irow7403, arows7402]
  all_goals rfl

theorem atot7403 : totK PD2M8K2 D2M8K2.u7403 = [0, 504939763918, 1657169417598, 1277900179427, 163598431030, 1369150432, 0, 0] := by
  rw [show D2M8K2.u7403 = KTree.node D2M8K2.u7401 (nat_lit 15595879) (nat_lit 2026952211) (nat_lit 0) D2M8K2.u7402 from rfl, totK_node, atot7401, atot7402]
  decide +kernel

theorem arows7406 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7406 = true := by
  rw [show D2M8K2.u7406 = KTree.node D2M8K2.u7404 (nat_lit 15599547) (nat_lit 3765549472) (nat_lit 0) D2M8K2.u7405 from rfl, allE_node, arows7404, irow7406, arows7405]
  all_goals rfl

theorem atot7406 : totK PD2M8K2 D2M8K2.u7406 = [0, 328472384908, 1218812883742, 1459307944159, 583620810702, 37601708222, 0, 0] := by
  rw [show D2M8K2.u7406 = KTree.node D2M8K2.u7404 (nat_lit 15599547) (nat_lit 3765549472) (nat_lit 0) D2M8K2.u7405 from rfl, totK_node, atot7404, atot7405]
  decide +kernel

theorem arows7410 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7410 = true := by
  rw [show D2M8K2.u7410 = KTree.node D2M8K2.u7408 (nat_lit 15602445) (nat_lit 1476459923) (nat_lit 0) D2M8K2.u7409 from rfl, allE_node, arows7408, irow7410, arows7409]
  all_goals rfl

theorem atot7410 : totK PD2M8K2 D2M8K2.u7410 = [0, 400769359181, 1433543984999, 1424303929683, 330768596924, 13049727234, 0, 0] := by
  rw [show D2M8K2.u7410 = KTree.node D2M8K2.u7408 (nat_lit 15602445) (nat_lit 1476459923) (nat_lit 0) D2M8K2.u7409 from rfl, totK_node, atot7408, atot7409]
  decide +kernel

theorem arows7413 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7413 = true := by
  rw [show D2M8K2.u7413 = KTree.node D2M8K2.u7411 (nat_lit 15606450) (nat_lit 3439854659) (nat_lit 0) D2M8K2.u7412 from rfl, allE_node, arows7411, irow7413, arows7412]
  all_goals rfl

theorem atot7413 : totK PD2M8K2 D2M8K2.u7413 = [0, 402410711683, 1479007803471, 1411218253184, 297033667827, 12052611869, 0, 0] := by
  rw [show D2M8K2.u7413 = KTree.node D2M8K2.u7411 (nat_lit 15606450) (nat_lit 3439854659) (nat_lit 0) D2M8K2.u7412 from rfl, totK_node, atot7411, atot7412]
  decide +kernel

theorem arows7422 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7422 = true := by
  rw [show D2M8K2.u7422 = KTree.node D2M8K2.u7420 (nat_lit 15609405) (nat_lit 1491616865) (nat_lit 0) D2M8K2.u7421 from rfl, allE_node, arows7420, irow7422, arows7421]
  all_goals rfl

theorem atot7422 : totK PD2M8K2 D2M8K2.u7422 = [0, 265686162196, 1293557234773, 1597847493840, 409302131661, 14720655943, 0, 0] := by
  rw [show D2M8K2.u7422 = KTree.node D2M8K2.u7420 (nat_lit 15609405) (nat_lit 1491616865) (nat_lit 0) D2M8K2.u7421 from rfl, totK_node, atot7420, atot7421]
  decide +kernel

theorem arows7425 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7425 = true := by
  rw [show D2M8K2.u7425 = KTree.node D2M8K2.u7423 (nat_lit 15618636) (nat_lit 2929899914) (nat_lit 0) D2M8K2.u7424 from rfl, allE_node, arows7423, irow7425, arows7424]
  all_goals rfl

theorem atot7425 : totK PD2M8K2 D2M8K2.u7425 = [0, 0, 731494072899, 1887370705194, 929646944627, 64577402978, 0, 0] := by
  rw [show D2M8K2.u7425 = KTree.node D2M8K2.u7423 (nat_lit 15618636) (nat_lit 2929899914) (nat_lit 0) D2M8K2.u7424 from rfl, totK_node, atot7423, atot7424]
  decide +kernel

theorem arows7429 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7429 = true := by
  rw [show D2M8K2.u7429 = KTree.node D2M8K2.u7427 (nat_lit 15625064) (nat_lit 3596544973) (nat_lit 0) D2M8K2.u7428 from rfl, allE_node, arows7427, irow7429, arows7428]
  all_goals rfl

theorem atot7429 : totK PD2M8K2 D2M8K2.u7429 = [0, 0, 778943490349, 1922708376097, 860404924315, 41150962780, 0, 0] := by
  rw [show D2M8K2.u7429 = KTree.node D2M8K2.u7427 (nat_lit 15625064) (nat_lit 3596544973) (nat_lit 0) D2M8K2.u7428 from rfl, totK_node, atot7427, atot7428]
  decide +kernel

theorem arows7432 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7432 = true := by
  rw [show D2M8K2.u7432 = KTree.node D2M8K2.u7430 (nat_lit 15629909) (nat_lit 1988992452) (nat_lit 0) D2M8K2.u7431 from rfl, allE_node, arows7430, irow7432, arows7431]
  all_goals rfl

theorem atot7432 : totK PD2M8K2 D2M8K2.u7432 = [0, 169606407816, 633453598134, 1329297868025, 1172043919838, 222340230680, 4977114383, 0] := by
  rw [show D2M8K2.u7432 = KTree.node D2M8K2.u7430 (nat_lit 15629909) (nat_lit 1988992452) (nat_lit 0) D2M8K2.u7431 from rfl, totK_node, atot7430, atot7431]
  decide +kernel

theorem arows7437 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7437 = true := by
  rw [show D2M8K2.u7437 = KTree.node D2M8K2.u7435 (nat_lit 15638143) (nat_lit 2162673414) (nat_lit 0) D2M8K2.u7436 from rfl, allE_node, arows7435, irow7437, arows7436]
  all_goals rfl

theorem atot7437 : totK PD2M8K2 D2M8K2.u7437 = [0, 496297763421, 1639407506980, 1331873819354, 177589177073, 1369150432, 0, 0] := by
  rw [show D2M8K2.u7437 = KTree.node D2M8K2.u7435 (nat_lit 15638143) (nat_lit 2162673414) (nat_lit 0) D2M8K2.u7436 from rfl, totK_node, atot7435, atot7436]
  decide +kernel

theorem arows7440 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7440 = true := by
  rw [show D2M8K2.u7440 = KTree.node D2M8K2.u7438 (nat_lit 15641233) (nat_lit 563709657) (nat_lit 0) D2M8K2.u7439 from rfl, allE_node, arows7438, irow7440, arows7439]
  all_goals rfl

theorem atot7440 : totK PD2M8K2 D2M8K2.u7440 = [0, 309268077236, 1195146807093, 1515904892317, 588313381185, 37589446790, 0, 0] := by
  rw [show D2M8K2.u7440 = KTree.node D2M8K2.u7438 (nat_lit 15641233) (nat_lit 563709657) (nat_lit 0) D2M8K2.u7439 from rfl, totK_node, atot7438, atot7439]
  decide +kernel

theorem arows7444 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7444 = true := by
  rw [show D2M8K2.u7444 = KTree.node D2M8K2.u7442 (nat_lit 15644210) (nat_lit 4078828690) (nat_lit 0) D2M8K2.u7443 from rfl, allE_node, arows7442, irow7444, arows7443]
  all_goals rfl

theorem atot7444 : totK PD2M8K2 D2M8K2.u7444 = [0, 401585696969, 1451205723646, 1443319058549, 319890237420, 12035546132, 0, 0] := by
  rw [show D2M8K2.u7444 = KTree.node D2M8K2.u7442 (nat_lit 15644210) (nat_lit 4078828690) (nat_lit 0) D2M8K2.u7443 from rfl, totK_node, atot7442, atot7443]
  decide +kernel

theorem arows7447 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7447 = true := by
  rw [show D2M8K2.u7447 = KTree.node D2M8K2.u7445 (nat_lit 15648048) (nat_lit 3596829569) (nat_lit 0) D2M8K2.u7446 from rfl, allE_node, arows7445, irow7447, arows7446]
  all_goals rfl

theorem atot7447 : totK PD2M8K2 D2M8K2.u7447 = [0, 438366119785, 1500564838926, 1384427474337, 304623190185, 9599934714, 0, 0] := by
  rw [show D2M8K2.u7447 = KTree.node D2M8K2.u7445 (nat_lit 15648048) (nat_lit 3596829569) (nat_lit 0) D2M8K2.u7446 from rfl, totK_node, atot7445, atot7446]
  decide +kernel

theorem arows7453 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7453 = true := by
  rw [show D2M8K2.u7453 = KTree.node D2M8K2.u7451 (nat_lit 15654579) (nat_lit 3635052595) (nat_lit 0) D2M8K2.u7452 from rfl, allE_node, arows7451, irow7453, arows7452]
  all_goals rfl

theorem atot7453 : totK PD2M8K2 D2M8K2.u7453 = [0, 180187839875, 1139396150828, 1707108916611, 535502706389, 23418599596, 0, 0] := by
  rw [show D2M8K2.u7453 = KTree.node D2M8K2.u7451 (nat_lit 15654579) (nat_lit 3635052595) (nat_lit 0) D2M8K2.u7452 from rfl, totK_node, atot7451, atot7452]
  decide +kernel

theorem arows7456 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7456 = true := by
  rw [show D2M8K2.u7456 = KTree.node D2M8K2.u7454 (nat_lit 15658904) (nat_lit 2217154858) (nat_lit 0) D2M8K2.u7455 from rfl, allE_node, arows7454, irow7456, arows7455]
  all_goals rfl

theorem atot7456 : totK PD2M8K2 D2M8K2.u7456 = [0, 0, 494385267526, 1665458336283, 1307686783438, 149653303205, 1310285577, 0] := by
  rw [show D2M8K2.u7456 = KTree.node D2M8K2.u7454 (nat_lit 15658904) (nat_lit 2217154858) (nat_lit 0) D2M8K2.u7455 from rfl, totK_node, atot7454, atot7455]
  decide +kernel

theorem arows7460 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7460 = true := by
  rw [show D2M8K2.u7460 = KTree.node D2M8K2.u7458 (nat_lit 15663772) (nat_lit 3869945590) (nat_lit 0) D2M8K2.u7459 from rfl, allE_node, arows7458, irow7460, arows7459]
  all_goals rfl

theorem atot7460 : totK PD2M8K2 D2M8K2.u7460 = [0, 0, 505289580210, 1607514441672, 1275062312546, 204500381860, 4879840392, 0] := by
  rw [show D2M8K2.u7460 = KTree.node D2M8K2.u7458 (nat_lit 15663772) (nat_lit 3869945590) (nat_lit 0) D2M8K2.u7459 from rfl, totK_node, atot7458, atot7459]
  decide +kernel

theorem arows7463 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7463 = true := by
  rw [show D2M8K2.u7463 = KTree.node D2M8K2.u7461 (nat_lit 15667537) (nat_lit 1380361445) (nat_lit 0) D2M8K2.u7462 from rfl, allE_node, arows7461, irow7463, arows7462]
  all_goals rfl

theorem atot7463 : totK PD2M8K2 D2M8K2.u7463 = [0, 0, 497380585680, 1686853321500, 1287481140672, 165173844636, 1444560764, 0] := by
  rw [show D2M8K2.u7463 = KTree.node D2M8K2.u7461 (nat_lit 15667537) (nat_lit 1380361445) (nat_lit 0) D2M8K2.u7462 from rfl, totK_node, atot7461, atot7462]
  decide +kernel

theorem arows7468 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7468 = true := by
  rw [show D2M8K2.u7468 = KTree.node D2M8K2.u7466 (nat_lit 15674744) (nat_lit 2872771753) (nat_lit 0) D2M8K2.u7467 from rfl, allE_node, arows7466, irow7468, arows7467]
  all_goals rfl

theorem atot7468 : totK PD2M8K2 D2M8K2.u7468 = [0, 37283609705, 365986625361, 1305852942709, 1461579604989, 392566184472, 18014152641, 0] := by
  rw [show D2M8K2.u7468 = KTree.node D2M8K2.u7466 (nat_lit 15674744) (nat_lit 2872771753) (nat_lit 0) D2M8K2.u7467 from rfl, totK_node, atot7466, atot7467]
  decide +kernel

theorem arows7471 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7471 = true := by
  rw [show D2M8K2.u7471 = KTree.node D2M8K2.u7469 (nat_lit 15926815) (nat_lit 2323947316) (nat_lit 0) D2M8K2.u7470 from rfl, allE_node, arows7469, irow7471, arows7470]
  all_goals rfl

theorem atot7471 : totK PD2M8K2 D2M8K2.u7471 = [0, 485905938418, 1631492361325, 1315461542300, 177062372331, 1369150432, 0, 0] := by
  rw [show D2M8K2.u7471 = KTree.node D2M8K2.u7469 (nat_lit 15926815) (nat_lit 2323947316) (nat_lit 0) D2M8K2.u7470 from rfl, totK_node, atot7469, atot7470]
  decide +kernel

theorem arows7475 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7475 = true := by
  rw [show D2M8K2.u7475 = KTree.node D2M8K2.u7473 (nat_lit 15933826) (nat_lit 3945797548) (nat_lit 0) D2M8K2.u7474 from rfl, allE_node, arows7473, irow7475, arows7474]
  all_goals rfl

theorem atot7475 : totK PD2M8K2 D2M8K2.u7475 = [0, 371701466681, 1415488427332, 1462102905191, 335630754868, 13049727234, 0, 0] := by
  rw [show D2M8K2.u7475 = KTree.node D2M8K2.u7473 (nat_lit 15933826) (nat_lit 3945797548) (nat_lit 0) D2M8K2.u7474 from rfl, totK_node, atot7473, atot7474]
  decide +kernel

theorem arows7478 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7478 = true := by
  rw [show D2M8K2.u7478 = KTree.node D2M8K2.u7476 (nat_lit 15937614) (nat_lit 3776321014) (nat_lit 0) D2M8K2.u7477 from rfl, allE_node, arows7476, irow7478, arows7477]
  all_goals rfl

theorem atot7478 : totK PD2M8K2 D2M8K2.u7478 = [0, 530459869475, 1612113176752, 1217799616660, 199653428761, 4780023221, 0, 0] := by
  rw [show D2M8K2.u7478 = KTree.node D2M8K2.u7476 (nat_lit 15937614) (nat_lit 3776321014) (nat_lit 0) D2M8K2.u7477 from rfl, totK_node, atot7476, atot7477]
  decide +kernel

theorem arows7485 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7485 = true := by
  rw [show D2M8K2.u7485 = KTree.node D2M8K2.u7483 (nat_lit 15941509) (nat_lit 1127134840) (nat_lit 0) D2M8K2.u7484 from rfl, allE_node, arows7483, irow7485, arows7484]
  all_goals rfl

theorem atot7485 : totK PD2M8K2 D2M8K2.u7485 = [0, 410998322315, 1525538279836, 1387737630014, 240513269853, 4980514959, 0, 0] := by
  rw [show D2M8K2.u7485 = KTree.node D2M8K2.u7483 (nat_lit 15941509) (nat_lit 1127134840) (nat_lit 0) D2M8K2.u7484 from rfl, totK_node, atot7483, atot7484]
  decide +kernel

theorem arows7488 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7488 = true := by
  rw [show D2M8K2.u7488 = KTree.node D2M8K2.u7486 (nat_lit 15945005) (nat_lit 1608101537) (nat_lit 0) D2M8K2.u7487 from rfl, allE_node, arows7486, irow7488, arows7487]
  all_goals rfl

theorem atot7488 : totK PD2M8K2 D2M8K2.u7488 = [0, 169300515430, 1064806527296, 1708552390888, 592324577864, 27162964736, 0, 0] := by
  rw [show D2M8K2.u7488 = KTree.node D2M8K2.u7486 (nat_lit 15945005) (nat_lit 1608101537) (nat_lit 0) D2M8K2.u7487 from rfl, totK_node, atot7486, atot7487]
  decide +kernel

theorem arows7492 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7492 = true := by
  rw [show D2M8K2.u7492 = KTree.node D2M8K2.u7490 (nat_lit 15948418) (nat_lit 4091777343) (nat_lit 0) D2M8K2.u7491 from rfl, allE_node, arows7490, irow7492, arows7491]
  all_goals rfl

theorem atot7492 : totK PD2M8K2 D2M8K2.u7492 = [0, 0, 489038416299, 1669243648257, 1191949178514, 143591564894, 1369150432, 0] := by
  rw [show D2M8K2.u7492 = KTree.node D2M8K2.u7490 (nat_lit 15948418) (nat_lit 4091777343) (nat_lit 0) D2M8K2.u7491 from rfl, totK_node, atot7490, atot7491]
  decide +kernel

theorem arows7495 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7495 = true := by
  rw [show D2M8K2.u7495 = KTree.node D2M8K2.u7493 (nat_lit 15957608) (nat_lit 3943022322) (nat_lit 0) D2M8K2.u7494 from rfl, allE_node, arows7493, irow7495, arows7494]
  all_goals rfl

theorem atot7495 : totK PD2M8K2 D2M8K2.u7495 = [0, 0, 765456858316, 1916964835614, 817163266520, 35842978801, 0, 0] := by
  rw [show D2M8K2.u7495 = KTree.node D2M8K2.u7493 (nat_lit 15957608) (nat_lit 3943022322) (nat_lit 0) D2M8K2.u7494 from rfl, totK_node, atot7493, atot7494]
  decide +kernel

theorem arows7500 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7500 = true := by
  rw [show D2M8K2.u7500 = KTree.node D2M8K2.u7498 (nat_lit 15964042) (nat_lit 3946046732) (nat_lit 0) D2M8K2.u7499 from rfl, allE_node, arows7498, irow7500, arows7499]
  all_goals rfl

theorem atot7500 : totK PD2M8K2 D2M8K2.u7500 = [0, 183243395725, 1002131804468, 1699525230871, 695307299414, 29988113471, 0, 0] := by
  rw [show D2M8K2.u7500 = KTree.node D2M8K2.u7498 (nat_lit 15964042) (nat_lit 3946046732) (nat_lit 0) D2M8K2.u7499 from rfl, totK_node, atot7498, atot7499]
  decide +kernel

theorem arows7503 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7503 = true := by
  rw [show D2M8K2.u7503 = KTree.node D2M8K2.u7501 (nat_lit 15972462) (nat_lit 3705515176) (nat_lit 0) D2M8K2.u7502 from rfl, allE_node, arows7501, irow7503, arows7502]
  all_goals rfl

theorem atot7503 : totK PD2M8K2 D2M8K2.u7503 = [0, 314184190207, 1211868672269, 1497805365589, 582508666392, 37609398105, 0, 0] := by
  rw [show D2M8K2.u7503 = KTree.node D2M8K2.u7501 (nat_lit 15972462) (nat_lit 3705515176) (nat_lit 0) D2M8K2.u7502 from rfl, totK_node, atot7501, atot7502]
  decide +kernel

theorem arows7507 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7507 = true := by
  rw [show D2M8K2.u7507 = KTree.node D2M8K2.u7505 (nat_lit 15975227) (nat_lit 2867881231) (nat_lit 0) D2M8K2.u7506 from rfl, allE_node, arows7505, irow7507, arows7506]
  all_goals rfl

theorem atot7507 : totK PD2M8K2 D2M8K2.u7507 = [0, 374039308549, 1438838261057, 1465903072205, 330812914914, 13036865798, 0, 0] := by
  rw [show D2M8K2.u7507 = KTree.node D2M8K2.u7505 (nat_lit 15975227) (nat_lit 2867881231) (nat_lit 0) D2M8K2.u7506 from rfl, totK_node, atot7505, atot7506]
  decide +kernel

theorem arows7510 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7510 = true := by
  rw [show D2M8K2.u7510 = KTree.node D2M8K2.u7508 (nat_lit 15979190) (nat_lit 3996906111) (nat_lit 0) D2M8K2.u7509 from rfl, allE_node, arows7508, irow7510, arows7509]
  all_goals rfl

theorem atot7510 : totK PD2M8K2 D2M8K2.u7510 = [0, 485016689883, 1560823359490, 1345054276731, 263583735129, 7024963918, 0, 0] := by
  rw [show D2M8K2.u7510 = KTree.node D2M8K2.u7508 (nat_lit 15979190) (nat_lit 3996906111) (nat_lit 0) D2M8K2.u7509 from rfl, totK_node, atot7508, atot7509]
  decide +kernel

theorem arows7516 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7516 = true := by
  rw [show D2M8K2.u7516 = KTree.node D2M8K2.u7514 (nat_lit 15982684) (nat_lit 3732173613) (nat_lit 0) D2M8K2.u7515 from rfl, allE_node, arows7514, irow7516, arows7515]
  all_goals rfl

theorem atot7516 : totK PD2M8K2 D2M8K2.u7516 = [0, 456272782657, 1542997843102, 1384671823017, 241496326986, 4976872846, 0, 0] := by
  rw [show D2M8K2.u7516 = KTree.node D2M8K2.u7514 (nat_lit 15982684) (nat_lit 3732173613) (nat_lit 0) D2M8K2.u7515 from rfl, totK_node, atot7514, atot7515]
  decide +kernel

theorem arows7519 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7519 = true := by
  rw [show D2M8K2.u7519 = KTree.node D2M8K2.u7517 (nat_lit 15986333) (nat_lit 2309705924) (nat_lit 0) D2M8K2.u7518 from rfl, allE_node, arows7517, irow7519, arows7518]
  all_goals rfl

theorem atot7519 : totK PD2M8K2 D2M8K2.u7519 = [0, 216127886953, 1154856413153, 1614178719713, 595198629555, 42593664180, 0, 0] := by
  rw [show D2M8K2.u7519 = KTree.node D2M8K2.u7517 (nat_lit 15986333) (nat_lit 2309705924) (nat_lit 0) D2M8K2.u7518 from rfl, totK_node, atot7517, atot7518]
  decide +kernel

theorem arows7523 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7523 = true := by
  rw [show D2M8K2.u7523 = KTree.node D2M8K2.u7521 (nat_lit 15993049) (nat_lit 885813989) (nat_lit 0) D2M8K2.u7522 from rfl, allE_node, arows7521, irow7523, arows7522]
  all_goals rfl

theorem atot7523 : totK PD2M8K2 D2M8K2.u7523 = [0, 0, 370778939015, 1357678194882, 1427216706149, 437359114613, 24281722747, 0] := by
  rw [show D2M8K2.u7523 = KTree.node D2M8K2.u7521 (nat_lit 15993049) (nat_lit 885813989) (nat_lit 0) D2M8K2.u7522 from rfl, totK_node, atot7521, atot7522]
  decide +kernel

theorem arows7526 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7526 = true := by
  rw [show D2M8K2.u7526 = KTree.node D2M8K2.u7524 (nat_lit 15995981) (nat_lit 2188079480) (nat_lit 0) D2M8K2.u7525 from rfl, allE_node, arows7524, irow7526, arows7525]
  all_goals rfl

theorem atot7526 : totK PD2M8K2 D2M8K2.u7526 = [0, 0, 448811298808, 1554211365925, 1379316535667, 241361927691, 5159868635, 0] := by
  rw [show D2M8K2.u7526 = KTree.node D2M8K2.u7524 (nat_lit 15995981) (nat_lit 2188079480) (nat_lit 0) D2M8K2.u7525 from rfl, totK_node, atot7524, atot7525]
  decide +kernel

theorem arows7531 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7531 = true := by
  rw [show D2M8K2.u7531 = KTree.node D2M8K2.u7529 (nat_lit 16001630) (nat_lit 3923990087) (nat_lit 0) D2M8K2.u7530 from rfl, allE_node, arows7529, irow7531, arows7530]
  all_goals rfl

theorem atot7531 : totK PD2M8K2 D2M8K2.u7531 = [0, 0, 648665675685, 1811480833428, 1063556489434, 82765353838, 0, 0] := by
  rw [show D2M8K2.u7531 = KTree.node D2M8K2.u7529 (nat_lit 16001630) (nat_lit 3923990087) (nat_lit 0) D2M8K2.u7530 from rfl, totK_node, atot7529, atot7530]
  decide +kernel

theorem arows7534 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7534 = true := by
  rw [show D2M8K2.u7534 = KTree.node D2M8K2.u7532 (nat_lit 16005304) (nat_lit 3548390679) (nat_lit 0) D2M8K2.u7533 from rfl, allE_node, arows7532, irow7534, arows7533]
  all_goals rfl

theorem atot7534 : totK PD2M8K2 D2M8K2.u7534 = [0, 0, 415957739872, 1612357710940, 1416491315470, 198513137045, 1415142070, 0] := by
  rw [show D2M8K2.u7534 = KTree.node D2M8K2.u7532 (nat_lit 16005304) (nat_lit 3548390679) (nat_lit 0) D2M8K2.u7533 from rfl, totK_node, atot7532, atot7533]
  decide +kernel

theorem arows7538 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7538 = true := by
  rw [show D2M8K2.u7538 = KTree.node D2M8K2.u7536 (nat_lit 16009172) (nat_lit 3631422479) (nat_lit 0) D2M8K2.u7537 from rfl, allE_node, arows7536, irow7538, arows7537]
  all_goals rfl

theorem atot7538 : totK PD2M8K2 D2M8K2.u7538 = [0, 416782174181, 1273818691596, 1126061183149, 577881423406, 168601485161, 5510671013, 0] := by
  rw [show D2M8K2.u7538 = KTree.node D2M8K2.u7536 (nat_lit 16009172) (nat_lit 3631422479) (nat_lit 0) D2M8K2.u7537 from rfl, totK_node, atot7536, atot7537]
  decide +kernel

theorem arows7541 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7541 = true := by
  rw [show D2M8K2.u7541 = KTree.node D2M8K2.u7539 (nat_lit 16012768) (nat_lit 1800868737) (nat_lit 0) D2M8K2.u7540 from rfl, allE_node, arows7539, irow7541, arows7540]
  all_goals rfl

theorem atot7541 : totK PD2M8K2 D2M8K2.u7541 = [0, 426411486583, 1480583805147, 1380240841375, 345790954158, 24987864049, 0, 0] := by
  rw [show D2M8K2.u7541 = KTree.node D2M8K2.u7539 (nat_lit 16012768) (nat_lit 1800868737) (nat_lit 0) D2M8K2.u7540 from rfl, totK_node, atot7539, atot7540]
  decide +kernel

theorem arows7549 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7549 = true := by
  rw [show D2M8K2.u7549 = KTree.node D2M8K2.u7547 (nat_lit 16015529) (nat_lit 1610459422) (nat_lit 0) D2M8K2.u7548 from rfl, allE_node, arows7547, irow7549, arows7548]
  all_goals rfl

theorem atot7549 : totK PD2M8K2 D2M8K2.u7549 = [0, 446578672583, 1471554636708, 1369456285210, 355902566357, 10154928807, 0, 0] := by
  rw [show D2M8K2.u7549 = KTree.node D2M8K2.u7547 (nat_lit 16015529) (nat_lit 1610459422) (nat_lit 0) D2M8K2.u7548 from rfl, totK_node, atot7547, atot7548]
  decide +kernel

theorem arows7552 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7552 = true := by
  rw [show D2M8K2.u7552 = KTree.node D2M8K2.u7550 (nat_lit 16022258) (nat_lit 3252316073) (nat_lit 0) D2M8K2.u7551 from rfl, allE_node, arows7550, irow7552, arows7551]
  all_goals rfl

theorem atot7552 : totK PD2M8K2 D2M8K2.u7552 = [0, 419484214538, 1455888032648, 1397765775331, 320976272706, 13049727234, 0, 0] := by
  rw [show D2M8K2.u7552 = KTree.node D2M8K2.u7550 (nat_lit 16022258) (nat_lit 3252316073) (nat_lit 0) D2M8K2.u7551 from rfl, totK_node, atot7550, atot7551]
  decide +kernel

theorem arows7556 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7556 = true := by
  rw [show D2M8K2.u7556 = KTree.node D2M8K2.u7554 (nat_lit 16025804) (nat_lit 3554347748) (nat_lit 0) D2M8K2.u7555 from rfl, allE_node, arows7554, irow7556, arows7555]
  all_goals rfl

theorem atot7556 : totK PD2M8K2 D2M8K2.u7556 = [0, 423750883410, 1520108864407, 1427264935356, 249618537088, 4980514959, 0, 0] := by
  rw [show D2M8K2.u7556 = KTree.node D2M8K2.u7554 (nat_lit 16025804) (nat_lit 3554347748) (nat_lit 0) D2M8K2.u7555 from rfl, totK_node, atot7554, atot7555]
  decide +kernel

theorem arows7559 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7559 = true := by
  rw [show D2M8K2.u7559 = KTree.node D2M8K2.u7557 (nat_lit 16028993) (nat_lit 2219989199) (nat_lit 0) D2M8K2.u7558 from rfl, allE_node, arows7557, irow7559, arows7558]
  all_goals rfl

theorem atot7559 : totK PD2M8K2 D2M8K2.u7559 = [0, 0, 783341103733, 1924939154955, 792615178853, 36138568117, 0, 0] := by
  rw [show D2M8K2.u7559 = KTree.node D2M8K2.u7557 (nat_lit 16028993) (nat_lit 2219989199) (nat_lit 0) D2M8K2.u7558 from rfl, totK_node, atot7557, atot7558]
  decide +kernel

theorem arows7564 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7564 = true := by
  rw [show D2M8K2.u7564 = KTree.node D2M8K2.u7562 (nat_lit 16032982) (nat_lit 3325926743) (nat_lit 0) D2M8K2.u7563 from rfl, allE_node, arows7562, irow7564, arows7563]
  all_goals rfl

theorem atot7564 : totK PD2M8K2 D2M8K2.u7564 = [0, 0, 511043517391, 1664346414137, 1249885366782, 148182419407, 1206465782, 0] := by
  rw [show D2M8K2.u7564 = KTree.node D2M8K2.u7562 (nat_lit 16032982) (nat_lit 3325926743) (nat_lit 0) D2M8K2.u7563 from rfl, totK_node, atot7562, atot7563]
  decide +kernel

theorem arows7567 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7567 = true := by
  rw [show D2M8K2.u7567 = KTree.node D2M8K2.u7565 (nat_lit 16037482) (nat_lit 3989793527) (nat_lit 0) D2M8K2.u7566 from rfl, allE_node, arows7565, irow7567, arows7566]
  all_goals rfl

theorem atot7567 : totK PD2M8K2 D2M8K2.u7567 = [0, 0, 394383217864, 1459991685405, 1385501189204, 308357471966, 13016197374, 0] := by
  rw [show D2M8K2.u7567 = KTree.node D2M8K2.u7565 (nat_lit 16037482) (nat_lit 3989793527) (nat_lit 0) D2M8K2.u7566 from rfl, totK_node, atot7565, atot7566]
  decide +kernel

theorem arows7571 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7571 = true := by
  rw [show D2M8K2.u7571 = KTree.node D2M8K2.u7569 (nat_lit 16044070) (nat_lit 1125536370) (nat_lit 0) D2M8K2.u7570 from rfl, allE_node, arows7569, irow7571, arows7570]
  all_goals rfl

theorem atot7571 : totK PD2M8K2 D2M8K2.u7571 = [0, 0, 465430523141, 1611694149867, 1224204848455, 177039489383, 4574395652, 0] := by
  rw [show D2M8K2.u7571 = KTree.node D2M8K2.u7569 (nat_lit 16044070) (nat_lit 1125536370) (nat_lit 0) D2M8K2.u7570 from rfl, totK_node, atot7569, atot7570]
  decide +kernel

theorem arows7574 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7574 = true := by
  rw [show D2M8K2.u7574 = KTree.node D2M8K2.u7572 (nat_lit 16091198) (nat_lit 2965544140) (nat_lit 0) D2M8K2.u7573 from rfl, allE_node, arows7572, irow7574, arows7573]
  all_goals rfl

theorem atot7574 : totK PD2M8K2 D2M8K2.u7574 = [0, 406174846124, 1319671232151, 1322607576623, 512523098687, 39517771004, 0, 0] := by
  rw [show D2M8K2.u7574 = KTree.node D2M8K2.u7572 (nat_lit 16091198) (nat_lit 2965544140) (nat_lit 0) D2M8K2.u7573 from rfl, totK_node, atot7572, atot7573]
  decide +kernel

theorem arows7580 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7580 = true := by
  rw [show D2M8K2.u7580 = KTree.node D2M8K2.u7578 (nat_lit 16095122) (nat_lit 4106108950) (nat_lit 0) D2M8K2.u7579 from rfl, allE_node, arows7578, irow7580, arows7579]
  all_goals rfl

theorem atot7580 : totK PD2M8K2 D2M8K2.u7580 = [0, 417464162019, 1562594606526, 1434332006423, 209601305673, 1369150432, 0, 0] := by
  rw [show D2M8K2.u7580 = KTree.node D2M8K2.u7578 (nat_lit 16095122) (nat_lit 4106108950) (nat_lit 0) D2M8K2.u7579 from rfl, totK_node, atot7578, atot7579]
  decide +kernel

theorem arows7583 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7583 = true := by
  rw [show D2M8K2.u7583 = KTree.node D2M8K2.u7581 (nat_lit 16097938) (nat_lit 4038603163) (nat_lit 0) D2M8K2.u7582 from rfl, allE_node, arows7581, irow7583, arows7582]
  all_goals rfl

theorem atot7583 : totK PD2M8K2 D2M8K2.u7583 = [0, 353870518770, 1246916488341, 1429764051181, 562155677696, 35901660392, 0, 0] := by
  rw [show D2M8K2.u7583 = KTree.node D2M8K2.u7581 (nat_lit 16097938) (nat_lit 4038603163) (nat_lit 0) D2M8K2.u7582 from rfl, totK_node, atot7581, atot7582]
  decide +kernel

theorem arows7587 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7587 = true := by
  rw [show D2M8K2.u7587 = KTree.node D2M8K2.u7585 (nat_lit 16101120) (nat_lit 3231313796) (nat_lit 0) D2M8K2.u7586 from rfl, allE_node, arows7585, irow7587, arows7586]
  all_goals rfl

theorem atot7587 : totK PD2M8K2 D2M8K2.u7587 = [0, 396114801005, 1456119621037, 1402297544747, 320028020297, 13049727234, 0, 0] := by
  rw [show D2M8K2.u7587 = KTree.node D2M8K2.u7585 (nat_lit 16101120) (nat_lit 3231313796) (nat_lit 0) D2M8K2.u7586 from rfl, totK_node, atot7585, atot7586]
  decide +kernel

theorem arows7590 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7590 = true := by
  rw [show D2M8K2.u7590 = KTree.node D2M8K2.u7588 (nat_lit 16105371) (nat_lit 3679211164) (nat_lit 0) D2M8K2.u7589 from rfl, allE_node, arows7588, irow7590, arows7589]
  all_goals rfl

theorem atot7590 : totK PD2M8K2 D2M8K2.u7590 = [0, 437882838950, 1533348270678, 1384161804427, 235111976077, 4780023221, 0, 0] := by
  rw [show D2M8K2.u7590 = KTree.node D2M8K2.u7588 (nat_lit 16105371) (nat_lit 3679211164) (nat_lit 0) D2M8K2.u7589 from rfl, totK_node, atot7588, atot7589]
  decide +kernel

theorem arows7595 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7595 = true := by
  rw [show D2M8K2.u7595 = KTree.node D2M8K2.u7593 (nat_lit 16112558) (nat_lit 3447227996) (nat_lit 0) D2M8K2.u7594 from rfl, allE_node, arows7593, irow7595, arows7594]
  all_goals rfl

theorem atot7595 : totK PD2M8K2 D2M8K2.u7595 = [0, 0, 752840805910, 1845971758044, 838196226777, 73086381192, 1138244013, 0] := by
  rw [show D2M8K2.u7595 = KTree.node D2M8K2.u7593 (nat_lit 16112558) (nat_lit 3447227996) (nat_lit 0) D2M8K2.u7594 from rfl, totK_node, atot7593, atot7594]
  decide +kernel

theorem arows7598 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7598 = true := by
  rw [show D2M8K2.u7598 = KTree.node D2M8K2.u7596 (nat_lit 16116410) (nat_lit 4054986831) (nat_lit 0) D2M8K2.u7597 from rfl, allE_node, arows7596, irow7598, arows7597]
  all_goals rfl

theorem atot7598 : totK PD2M8K2 D2M8K2.u7598 = [0, 0, 644877628011, 1843595042248, 1042352331866, 75555247170, 0, 0] := by
  rw [show D2M8K2.u7598 = KTree.node D2M8K2.u7596 (nat_lit 16116410) (nat_lit 4054986831) (nat_lit 0) D2M8K2.u7597 from rfl, totK_node, atot7596, atot7597]
  decide +kernel

theorem arows7602 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7602 = true := by
  rw [show D2M8K2.u7602 = KTree.node D2M8K2.u7600 (nat_lit 16122780) (nat_lit 2036524681) (nat_lit 0) D2M8K2.u7601 from rfl, allE_node, arows7600, irow7602, arows7601]
  all_goals rfl

theorem atot7602 : totK PD2M8K2 D2M8K2.u7602 = [0, 0, 754548410870, 1904591164670, 876957208739, 43669982179, 0, 0] := by
  rw [show D2M8K2.u7602 = KTree.node D2M8K2.u7600 (nat_lit 16122780) (nat_lit 2036524681) (nat_lit 0) D2M8K2.u7601 from rfl, totK_node, atot7600, atot7601]
  decide +kernel

theorem arows7605 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7605 = true := by
  rw [show D2M8K2.u7605 = KTree.node D2M8K2.u7603 (nat_lit 16128068) (nat_lit 3369024564) (nat_lit 0) D2M8K2.u7604 from rfl, allE_node, arows7603, irow7605, arows7604]
  all_goals rfl

theorem atot7605 : totK PD2M8K2 D2M8K2.u7605 = [0, 252651705119, 804838405197, 1247347380892, 1008917434515, 182469147608, 4977114383, 0] := by
  rw [show D2M8K2.u7605 = KTree.node D2M8K2.u7603 (nat_lit 16128068) (nat_lit 3369024564) (nat_lit 0) D2M8K2.u7604 from rfl, totK_node, atot7603, atot7604]
  decide +kernel

theorem arows7612 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7612 = true := by
  rw [show D2M8K2.u7612 = KTree.node D2M8K2.u7610 (nat_lit 16135549) (nat_lit 1204013188) (nat_lit 0) D2M8K2.u7611 from rfl, allE_node, arows7610, irow7612, arows7611]
  all_goals rfl

theorem atot7612 : totK PD2M8K2 D2M8K2.u7612 = [0, 462968270860, 1574159797039, 1378680567922, 194802188834, 1369150432, 0, 0] := by
  rw [show D2M8K2.u7612 = KTree.node D2M8K2.u7610 (nat_lit 16135549) (nat_lit 1204013188) (nat_lit 0) D2M8K2.u7611 from rfl, totK_node, atot7610, atot7611]
  decide +kernel

theorem arows7615 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7615 = true := by
  rw [show D2M8K2.u7615 = KTree.node D2M8K2.u7613 (nat_lit 16138806) (nat_lit 3027582203) (nat_lit 0) D2M8K2.u7614 from rfl, allE_node, arows7613, irow7615, arows7614]
  all_goals rfl

theorem atot7615 : totK PD2M8K2 D2M8K2.u7615 = [0, 298822204159, 1224526722722, 1508039105499, 578244332835, 36008142572, 0, 0] := by
  rw [show D2M8K2.u7615 = KTree.node D2M8K2.u7613 (nat_lit 16138806) (nat_lit 3027582203) (nat_lit 0) D2M8K2.u7614 from rfl, totK_node, atot7613, atot7614]
  decide +kernel

theorem arows7619 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7619 = true := by
  rw [show D2M8K2.u7619 = KTree.node D2M8K2.u7617 (nat_lit 16141667) (nat_lit 2951687086) (nat_lit 0) D2M8K2.u7618 from rfl, allE_node, arows7617, irow7619, arows7618]
  all_goals rfl

theorem atot7619 : totK PD2M8K2 D2M8K2.u7619 = [0, 400885775741, 1447694649132, 1426600355828, 328176221829, 13043783340, 0, 0] := by
  rw [show D2M8K2.u7619 = KTree.node D2M8K2.u7617 (nat_lit 16141667) (nat_lit 2951687086) (nat_lit 0) D2M8K2.u7618 from rfl, totK_node, atot7617, atot7618]
  decide +kernel

theorem arows7622 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7622 = true := by
  rw [show D2M8K2.u7622 = KTree.node D2M8K2.u7620 (nat_lit 16145806) (nat_lit 2950153202) (nat_lit 0) D2M8K2.u7621 from rfl, allE_node, arows7620, irow7622, arows7621]
  all_goals rfl

theorem atot7622 : totK PD2M8K2 D2M8K2.u7622 = [0, 509969763462, 1570868080249, 1314310358461, 246224693963, 5455647540, 0, 0] := by
  rw [show D2M8K2.u7622 = KTree.node D2M8K2.u7620 (nat_lit 16145806) (nat_lit 2950153202) (nat_lit 0) D2M8K2.u7621 from rfl, totK_node, atot7620, atot7621]
  decide +kernel

theorem arows7627 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7627 = true := by
  rw [show D2M8K2.u7627 = KTree.node D2M8K2.u7625 (nat_lit 16152527) (nat_lit 2129976506) (nat_lit 0) D2M8K2.u7626 from rfl, allE_node, arows7625, irow7627, arows7626]
  all_goals rfl

theorem atot7627 : totK PD2M8K2 D2M8K2.u7627 = [0, 93763323609, 1021608371439, 1821517879575, 624855399890, 27384849158, 0, 0] := by
  rw [show D2M8K2.u7627 = KTree.node D2M8K2.u7625 (nat_lit 16152527) (nat_lit 2129976506) (nat_lit 0) D2M8K2.u7626 from rfl, totK_node, atot7625, atot7626]
  decide +kernel

theorem arows7630 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7630 = true := by
  rw [show D2M8K2.u7630 = KTree.node D2M8K2.u7628 (nat_lit 16156320) (nat_lit 3462188811) (nat_lit 0) D2M8K2.u7629 from rfl, allE_node, arows7628, irow7630, arows7629]
  all_goals rfl

theorem atot7630 : totK PD2M8K2 D2M8K2.u7630 = [0, 0, 482632794860, 1645866791328, 1302169986852, 140291304715, 1310285577, 0] := by
  rw [show D2M8K2.u7630 = KTree.node D2M8K2.u7628 (nat_lit 16156320) (nat_lit 3462188811) (nat_lit 0) D2M8K2.u7629 from rfl, totK_node, atot7628, atot7629]
  decide +kernel

theorem arows7634 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7634 = true := by
  rw [show D2M8K2.u7634 = KTree.node D2M8K2.u7632 (nat_lit 16161045) (nat_lit 1458309550) (nat_lit 0) D2M8K2.u7633 from rfl, allE_node, arows7632, irow7634, arows7633]
  all_goals rfl

theorem atot7634 : totK PD2M8K2 D2M8K2.u7634 = [0, 0, 514606689027, 1623814145350, 1252382828444, 191274267605, 4879840392, 0] := by
  rw [show D2M8K2.u7634 = KTree.node D2M8K2.u7632 (nat_lit 16161045) (nat_lit 1458309550) (nat_lit 0) D2M8K2.u7633 from rfl, totK_node, atot7632, atot7633]
  decide +kernel

theorem arows7637 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7637 = true := by
  rw [show D2M8K2.u7637 = KTree.node D2M8K2.u7635 (nat_lit 16165274) (nat_lit 4067424481) (nat_lit 0) D2M8K2.u7636 from rfl, allE_node, arows7635, irow7637, arows7636]
  all_goals rfl

theorem atot7637 : totK PD2M8K2 D2M8K2.u7637 = [0, 0, 672313020637, 1799767978878, 1060088068322, 95958073052, 0, 0] := by
  rw [show D2M8K2.u7637 = KTree.node D2M8K2.u7635 (nat_lit 16165274) (nat_lit 4067424481) (nat_lit 0) D2M8K2.u7636 from rfl, totK_node, atot7635, atot7636]
  decide +kernel

theorem arows7643 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7643 = true := by
  rw [show D2M8K2.u7643 = KTree.node D2M8K2.u7641 (nat_lit 16173792) (nat_lit 3684805063) (nat_lit 0) D2M8K2.u7642 from rfl, allE_node, arows7641, irow7643, arows7642]
  all_goals rfl

theorem atot7643 : totK PD2M8K2 D2M8K2.u7643 = [0, 0, 397670093173, 1462530472793, 1377853569046, 308759885922, 13786494048, 0] := by
  rw [show D2M8K2.u7643 = KTree.node D2M8K2.u7641 (nat_lit 16173792) (nat_lit 3684805063) (nat_lit 0) D2M8K2.u7642 from rfl, totK_node, atot7641, atot7642]
  decide +kernel

theorem arows7646 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7646 = true := by
  rw [show D2M8K2.u7646 = KTree.node D2M8K2.u7644 (nat_lit 16177069) (nat_lit 1126510899) (nat_lit 0) D2M8K2.u7645 from rfl, allE_node, arows7644, irow7646, arows7645]
  all_goals rfl

theorem atot7646 : totK PD2M8K2 D2M8K2.u7646 = [0, 0, 463610510679, 1625368767043, 1338546054602, 165331860871, 1369150432, 0] := by
  rw [show D2M8K2.u7646 = KTree.node D2M8K2.u7644 (nat_lit 16177069) (nat_lit 1126510899) (nat_lit 0) D2M8K2.u7645 from rfl, totK_node, atot7644, atot7645]
  decide +kernel

theorem arows7650 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7650 = true := by
  rw [show D2M8K2.u7650 = KTree.node D2M8K2.u7648 (nat_lit 16184023) (nat_lit 1033355179) (nat_lit 0) D2M8K2.u7649 from rfl, allE_node, arows7648, irow7650, arows7649]
  all_goals rfl

theorem atot7650 : totK PD2M8K2 D2M8K2.u7650 = [0, 0, 406676775698, 1464450164295, 1353191406011, 303236005347, 13049727234, 0] := by
  rw [show D2M8K2.u7650 = KTree.node D2M8K2.u7648 (nat_lit 16184023) (nat_lit 1033355179) (nat_lit 0) D2M8K2.u7649 from rfl, totK_node, atot7648, atot7649]
  decide +kernel

theorem arows7653 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7653 = true := by
  rw [show D2M8K2.u7653 = KTree.node D2M8K2.u7651 (nat_lit 16188526) (nat_lit 2953117414) (nat_lit 0) D2M8K2.u7652 from rfl, allE_node, arows7651, irow7653, arows7652]
  all_goals rfl

theorem atot7653 : totK PD2M8K2 D2M8K2.u7653 = [0, 0, 406860742631, 1569913684928, 1360867261264, 168196689270, 2294578496, 0] := by
  rw [show D2M8K2.u7653 = KTree.node D2M8K2.u7651 (nat_lit 16188526) (nat_lit 2953117414) (nat_lit 0) D2M8K2.u7652 from rfl, totK_node, atot7651, atot7652]
  decide +kernel

theorem arows7658 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7658 = true := by
  rw [show D2M8K2.u7658 = KTree.node D2M8K2.u7656 (nat_lit 16192176) (nat_lit 3289899456) (nat_lit 0) D2M8K2.u7657 from rfl, allE_node, arows7656, irow7658, arows7657]
  all_goals rfl

theorem atot7658 : totK PD2M8K2 D2M8K2.u7658 = [0, 0, 411769882097, 1469118675639, 1412310434476, 281246669071, 8788760260, 0] := by
  rw [show D2M8K2.u7658 = KTree.node D2M8K2.u7656 (nat_lit 16192176) (nat_lit 3289899456) (nat_lit 0) D2M8K2.u7657 from rfl, totK_node, atot7656, atot7657]
  decide +kernel

theorem arows7661 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7661 = true := by
  rw [show D2M8K2.u7661 = KTree.node D2M8K2.u7659 (nat_lit 16195974) (nat_lit 3743316732) (nat_lit 0) D2M8K2.u7660 from rfl, allE_node, arows7659, irow7661, arows7660]
  all_goals rfl

theorem atot7661 : totK PD2M8K2 D2M8K2.u7661 = [0, 0, 0, 593540344472, 1721260077800, 1010209615585, 117235672807, 1275377855] := by
  rw [show D2M8K2.u7661 = KTree.node D2M8K2.u7659 (nat_lit 16195974) (nat_lit 3743316732) (nat_lit 0) D2M8K2.u7660 from rfl, totK_node, atot7659, atot7660]
  decide +kernel

theorem arows7665 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7665 = true := by
  rw [show D2M8K2.u7665 = KTree.node D2M8K2.u7663 (nat_lit 16203197) (nat_lit 2268823387) (nat_lit 0) D2M8K2.u7664 from rfl, allE_node, arows7663, irow7665, arows7664]
  all_goals rfl

theorem atot7665 : totK PD2M8K2 D2M8K2.u7665 = [0, 0, 0, 822431965260, 1913797131183, 726416525729, 37864223692, 0] := by
  rw [show D2M8K2.u7665 = KTree.node D2M8K2.u7663 (nat_lit 16203197) (nat_lit 2268823387) (nat_lit 0) D2M8K2.u7664 from rfl, totK_node, atot7663, atot7664]
  decide +kernel

theorem arows7668 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7668 = true := by
  rw [show D2M8K2.u7668 = KTree.node D2M8K2.u7666 (nat_lit 16212247) (nat_lit 1678621552) (nat_lit 128) D2M8K2.u7667 from rfl, allE_node, arows7666, irow7668, arows7667]
  all_goals rfl

theorem atot7668 : totK PD2M8K2 D2M8K2.u7668 = [0, 0, 94308027437, 962687869615, 1833831783297, 629123235566, 28715729375, 0] := by
  rw [show D2M8K2.u7668 = KTree.node D2M8K2.u7666 (nat_lit 16212247) (nat_lit 1678621552) (nat_lit 128) D2M8K2.u7667 from rfl, totK_node, atot7666, atot7667]
  decide +kernel

theorem arows7678 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7678 = true := by
  rw [show D2M8K2.u7678 = KTree.node D2M8K2.u7676 (nat_lit 16221080) (nat_lit 3711642244) (nat_lit 0) D2M8K2.u7677 from rfl, allE_node, arows7676, irow7678, arows7677]
  all_goals rfl

theorem atot7678 : totK PD2M8K2 D2M8K2.u7678 = [0, 0, 377374154447, 1369377992202, 1460033100876, 431845477551, 24683636622, 0] := by
  rw [show D2M8K2.u7678 = KTree.node D2M8K2.u7676 (nat_lit 16221080) (nat_lit 3711642244) (nat_lit 0) D2M8K2.u7677 from rfl, totK_node, atot7676, atot7677]
  decide +kernel

theorem arows7681 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7681 = true := by
  rw [show D2M8K2.u7681 = KTree.node D2M8K2.u7679 (nat_lit 16224026) (nat_lit 4067263936) (nat_lit 0) D2M8K2.u7680 from rfl, allE_node, arows7679, irow7681, arows7680]
  all_goals rfl

theorem atot7681 : totK PD2M8K2 D2M8K2.u7681 = [0, 0, 428457744952, 1531193327907, 1412909150814, 253659571850, 9751947372, 0] := by
  rw [show D2M8K2.u7681 = KTree.node D2M8K2.u7679 (nat_lit 16224026) (nat_lit 4067263936) (nat_lit 0) D2M8K2.u7680 from rfl, totK_node, atot7679, atot7680]
  decide +kernel

theorem arows7685 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7685 = true := by
  rw [show D2M8K2.u7685 = KTree.node D2M8K2.u7683 (nat_lit 16229773) (nat_lit 1023679829) (nat_lit 0) D2M8K2.u7684 from rfl, allE_node, arows7683, irow7685, arows7684]
  all_goals rfl

theorem atot7685 : totK PD2M8K2 D2M8K2.u7685 = [0, 0, 702416889809, 1862664769837, 999424131016, 89909405734, 0, 0] := by
  rw [show D2M8K2.u7685 = KTree.node D2M8K2.u7683 (nat_lit 16229773) (nat_lit 1023679829) (nat_lit 0) D2M8K2.u7684 from rfl, totK_node, atot7683, atot7684]
  decide +kernel

theorem arows7688 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7688 = true := by
  rw [show D2M8K2.u7688 = KTree.node D2M8K2.u7686 (nat_lit 16233476) (nat_lit 3208704329) (nat_lit 0) D2M8K2.u7687 from rfl, allE_node, arows7686, irow7688, arows7687]
  all_goals rfl

theorem atot7688 : totK PD2M8K2 D2M8K2.u7688 = [0, 0, 415320423887, 1573837540324, 1445956737268, 222174349255, 3845941866, 0] := by
  rw [show D2M8K2.u7688 = KTree.node D2M8K2.u7686 (nat_lit 16233476) (nat_lit 3208704329) (nat_lit 0) D2M8K2.u7687 from rfl, totK_node, atot7686, atot7687]
  decide +kernel

theorem arows7693 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7693 = true := by
  rw [show D2M8K2.u7693 = KTree.node D2M8K2.u7691 (nat_lit 16258148) (nat_lit 3224070534) (nat_lit 0) D2M8K2.u7692 from rfl, allE_node, arows7691, irow7693, arows7692]
  all_goals rfl

theorem atot7693 : totK PD2M8K2 D2M8K2.u7693 = [0, 0, 414104253094, 1501338655620, 1340821010171, 274065640509, 12903263167, 0] := by
  rw [show D2M8K2.u7693 = KTree.node D2M8K2.u7691 (nat_lit 16258148) (nat_lit 3224070534) (nat_lit 0) D2M8K2.u7692 from rfl, totK_node, atot7691, atot7692]
  decide +kernel

theorem arows7696 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7696 = true := by
  rw [show D2M8K2.u7696 = KTree.node D2M8K2.u7694 (nat_lit 16261742) (nat_lit 3854375359) (nat_lit 0) D2M8K2.u7695 from rfl, allE_node, arows7694, irow7696, arows7695]
  all_goals rfl

theorem atot7696 : totK PD2M8K2 D2M8K2.u7696 = [0, 0, 423441418056, 1488042241920, 1391864045157, 323962446495, 18567029682, 0] := by
  rw [show D2M8K2.u7696 = KTree.node D2M8K2.u7694 (nat_lit 16261742) (nat_lit 3854375359) (nat_lit 0) D2M8K2.u7695 from rfl, totK_node, atot7694, atot7695]
  decide +kernel

theorem arows7700 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7700 = true := by
  rw [show D2M8K2.u7700 = KTree.node D2M8K2.u7698 (nat_lit 16264665) (nat_lit 1729926509) (nat_lit 0) D2M8K2.u7699 from rfl, allE_node, arows7698, irow7700, arows7699]
  all_goals rfl

theorem atot7700 : totK PD2M8K2 D2M8K2.u7700 = [0, 0, 445194187690, 1489691882782, 1397854841557, 296578952728, 6686214215, 0] := by
  rw [show D2M8K2.u7700 = KTree.node D2M8K2.u7698 (nat_lit 16264665) (nat_lit 1729926509) (nat_lit 0) D2M8K2.u7699 from rfl, totK_node, atot7698, atot7699]
  decide +kernel

theorem arows7703 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7703 = true := by
  rw [show D2M8K2.u7703 = KTree.node D2M8K2.u7701 (nat_lit 16271429) (nat_lit 2337965196) (nat_lit 0) D2M8K2.u7702 from rfl, allE_node, arows7701, irow7703, arows7702]
  all_goals rfl

theorem atot7703 : totK PD2M8K2 D2M8K2.u7703 = [0, 0, 416699897338, 1452281966909, 1367860308088, 296887708413, 12948334120, 0] := by
  rw [show D2M8K2.u7703 = KTree.node D2M8K2.u7701 (nat_lit 16271429) (nat_lit 2337965196) (nat_lit 0) D2M8K2.u7702 from rfl, totK_node, atot7701, atot7702]
  decide +kernel

theorem arows7709 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7709 = true := by
  rw [show D2M8K2.u7709 = KTree.node D2M8K2.u7707 (nat_lit 16274948) (nat_lit 3256000356) (nat_lit 0) D2M8K2.u7708 from rfl, allE_node, arows7707, irow7709, arows7708]
  all_goals rfl

theorem atot7709 : totK PD2M8K2 D2M8K2.u7709 = [0, 0, 420582282504, 1511177152666, 1411669406577, 246592096815, 5024003845, 0] := by
  rw [show D2M8K2.u7709 = KTree.node D2M8K2.u7707 (nat_lit 16274948) (nat_lit 3256000356) (nat_lit 0) D2M8K2.u7708 from rfl, totK_node, atot7707, atot7708]
  decide +kernel

theorem arows7712 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7712 = true := by
  rw [show D2M8K2.u7712 = KTree.node D2M8K2.u7710 (nat_lit 16278723) (nat_lit 2292528588) (nat_lit 0) D2M8K2.u7711 from rfl, allE_node, arows7710, irow7712, arows7711]
  all_goals rfl

theorem atot7712 : totK PD2M8K2 D2M8K2.u7712 = [0, 0, 0, 601849786115, 1729092789949, 1008047935612, 113266742739, 1206465782] := by
  rw [show D2M8K2.u7712 = KTree.node D2M8K2.u7710 (nat_lit 16278723) (nat_lit 2292528588) (nat_lit 0) D2M8K2.u7711 from rfl, totK_node, atot7710, atot7711]
  decide +kernel

theorem arows7716 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7716 = true := by
  rw [show D2M8K2.u7716 = KTree.node D2M8K2.u7714 (nat_lit 16282656) (nat_lit 3388150610) (nat_lit 0) D2M8K2.u7715 from rfl, allE_node, arows7714, irow7716, arows7715]
  all_goals rfl

theorem atot7716 : totK PD2M8K2 D2M8K2.u7716 = [0, 0, 0, 728962141114, 1853085693018, 950173711783, 69670618909, 0] := by
  rw [show D2M8K2.u7716 = KTree.node D2M8K2.u7714 (nat_lit 16282656) (nat_lit 3388150610) (nat_lit 0) D2M8K2.u7715 from rfl, totK_node, atot7714, atot7715]
  decide +kernel

theorem arows7719 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7719 = true := by
  rw [show D2M8K2.u7719 = KTree.node D2M8K2.u7717 (nat_lit 16287581) (nat_lit 2293364964) (nat_lit 0) D2M8K2.u7718 from rfl, allE_node, arows7717, irow7719, arows7718]
  all_goals rfl

theorem atot7719 : totK PD2M8K2 D2M8K2.u7719 = [0, 0, 0, 389383880117, 1450615667744, 1334134828851, 302093770036, 13016197374] := by
  rw [show D2M8K2.u7719 = KTree.node D2M8K2.u7717 (nat_lit 16287581) (nat_lit 2293364964) (nat_lit 0) D2M8K2.u7718 from rfl, totK_node, atot7717, atot7718]
  decide +kernel

theorem arows7724 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7724 = true := by
  rw [show D2M8K2.u7724 = KTree.node D2M8K2.u7722 (nat_lit 16294549) (nat_lit 1059263710) (nat_lit 0) D2M8K2.u7723 from rfl, allE_node, arows7722, irow7724, arows7723]
  all_goals rfl

theorem atot7724 : totK PD2M8K2 D2M8K2.u7724 = [0, 0, 0, 553708898020, 1610614362502, 1098738907870, 170238161672, 4574395652] := by
  rw [show D2M8K2.u7724 = KTree.node D2M8K2.u7722 (nat_lit 16294549) (nat_lit 1059263710) (nat_lit 0) D2M8K2.u7723 from rfl, totK_node, atot7722, atot7723]
  decide +kernel

theorem arows7727 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7727 = true := by
  rw [show D2M8K2.u7727 = KTree.node D2M8K2.u7725 (nat_lit 16341344) (nat_lit 3757505374) (nat_lit 0) D2M8K2.u7726 from rfl, allE_node, arows7725, irow7727, arows7726]
  all_goals rfl

theorem atot7727 : totK PD2M8K2 D2M8K2.u7727 = [0, 0, 471718321235, 1526067368558, 1281696013971, 235491263362, 10245552087, 0] := by
  rw [show D2M8K2.u7727 = KTree.node D2M8K2.u7725 (nat_lit 16341344) (nat_lit 3757505374) (nat_lit 0) D2M8K2.u7726 from rfl, totK_node, atot7725, atot7726]
  decide +kernel

theorem arows7731 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7731 = true := by
  rw [show D2M8K2.u7731 = KTree.node D2M8K2.u7729 (nat_lit 16345144) (nat_lit 3292377767) (nat_lit 0) D2M8K2.u7730 from rfl, allE_node, arows7729, irow7731, arows7730]
  all_goals rfl

theorem atot7731 : totK PD2M8K2 D2M8K2.u7731 = [0, 0, 432577445015, 1490558575853, 1371230345192, 338642119733, 15013989272, 0] := by
  rw [show D2M8K2.u7731 = KTree.node D2M8K2.u7729 (nat_lit 16345144) (nat_lit 3292377767) (nat_lit 0) D2M8K2.u7730 from rfl, totK_node, atot7729, atot7730]
  decide +kernel

theorem arows7734 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7734 = true := by
  rw [show D2M8K2.u7734 = KTree.node D2M8K2.u7732 (nat_lit 16348532) (nat_lit 1881636149) (nat_lit 0) D2M8K2.u7733 from rfl, allE_node, arows7732, irow7734, arows7733]
  all_goals rfl

theorem atot7734 : totK PD2M8K2 D2M8K2.u7734 = [0, 0, 385042215828, 1418722215222, 1439584338851, 323482205017, 13049727234, 0] := by
  rw [show D2M8K2.u7734 = KTree.node D2M8K2.u7732 (nat_lit 16348532) (nat_lit 1881636149) (nat_lit 0) D2M8K2.u7733 from rfl, totK_node, atot7732, atot7733]
  decide +kernel

theorem arows7741 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7741 = true := by
  rw [show D2M8K2.u7741 = KTree.node D2M8K2.u7739 (nat_lit 16352411) (nat_lit 1865207371) (nat_lit 128) D2M8K2.u7740 from rfl, allE_node, arows7739, irow7741, arows7740]
  all_goals rfl

theorem atot7741 : totK PD2M8K2 D2M8K2.u7741 = [0, 0, 535661213944, 1685375271876, 1180665052054, 148123690517, 4686148432, 0] := by
  rw [show D2M8K2.u7741 = KTree.node D2M8K2.u7739 (nat_lit 16352411) (nat_lit 1865207371) (nat_lit 128) D2M8K2.u7740 from rfl, totK_node, atot7739, atot7740]
  decide +kernel

theorem arows7744 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7744 = true := by
  rw [show D2M8K2.u7744 = KTree.node D2M8K2.u7742 (nat_lit 16356391) (nat_lit 2380302534) (nat_lit 0) D2M8K2.u7743 from rfl, allE_node, arows7742, irow7744, arows7743]
  all_goals rfl

theorem atot7744 : totK PD2M8K2 D2M8K2.u7744 = [0, 0, 174985890020, 1188565766469, 1707625632982, 425009735300, 15814693075, 0] := by
  rw [show D2M8K2.u7744 = KTree.node D2M8K2.u7742 (nat_lit 16356391) (nat_lit 2380302534) (nat_lit 0) D2M8K2.u7743 from rfl, totK_node, atot7742, atot7743]
  decide +kernel

theorem arows7748 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7748 = true := by
  rw [show D2M8K2.u7748 = KTree.node D2M8K2.u7746 (nat_lit 16364518) (nat_lit 3700022734) (nat_lit 0) D2M8K2.u7747 from rfl, allE_node, arows7746, irow7748, arows7747]
  all_goals rfl

theorem atot7748 : totK PD2M8K2 D2M8K2.u7748 = [0, 0, 0, 625154507367, 1754971703937, 994523730868, 90488781639, 1103454931] := by
  rw [show D2M8K2.u7748 = KTree.node D2M8K2.u7746 (nat_lit 16364518) (nat_lit 3700022734) (nat_lit 0) D2M8K2.u7747 from rfl, totK_node, atot7746, atot7747]
  decide +kernel

theorem arows7751 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7751 = true := by
  rw [show D2M8K2.u7751 = KTree.node D2M8K2.u7749 (nat_lit 16371186) (nat_lit 3407810300) (nat_lit 0) D2M8K2.u7750 from rfl, allE_node, arows7749, irow7751, arows7750]
  all_goals rfl

theorem atot7751 : totK PD2M8K2 D2M8K2.u7751 = [0, 0, 0, 867274853165, 1874433847734, 718653648036, 41582908021, 0] := by
  rw [show D2M8K2.u7751 = KTree.node D2M8K2.u7749 (nat_lit 16371186) (nat_lit 3407810300) (nat_lit 0) D2M8K2.u7750 from rfl, totK_node, atot7749, atot7750]
  decide +kernel

theorem arows7756 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7756 = true := by
  rw [show D2M8K2.u7756 = KTree.node D2M8K2.u7754 (nat_lit 16376937) (nat_lit 1906910786) (nat_lit 0) D2M8K2.u7755 from rfl, allE_node, arows7754, irow7756, arows7755]
  all_goals rfl

theorem atot7756 : totK PD2M8K2 D2M8K2.u7756 = [0, 0, 269505428543, 850306996829, 1237187888577, 894611706413, 162709336989, 4779662215] := by
  rw [show D2M8K2.u7756 = KTree.node D2M8K2.u7754 (nat_lit 16376937) (nat_lit 1906910786) (nat_lit 0) D2M8K2.u7755 from rfl, totK_node, atot7754, atot7755]
  decide +kernel

theorem arows7759 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7759 = true := by
  rw [show D2M8K2.u7759 = KTree.node D2M8K2.u7757 (nat_lit 16384658) (nat_lit 3721940262) (nat_lit 0) D2M8K2.u7758 from rfl, allE_node, arows7757, irow7759, arows7758]
  all_goals rfl

theorem atot7759 : totK PD2M8K2 D2M8K2.u7759 = [0, 0, 509941750095, 1653171703705, 1294769589038, 158515093990, 1369150432, 0] := by
  rw [show D2M8K2.u7759 = KTree.node D2M8K2.u7757 (nat_lit 16384658) (nat_lit 3721940262) (nat_lit 0) D2M8K2.u7758 from rfl, totK_node, atot7757, atot7758]
  decide +kernel

theorem arows7763 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7763 = true := by
  rw [show D2M8K2.u7763 = KTree.node D2M8K2.u7761 (nat_lit 16388278) (nat_lit 3390271686) (nat_lit 0) D2M8K2.u7762 from rfl, allE_node, arows7761, irow7763, arows7762]
  all_goals rfl

theorem atot7763 : totK PD2M8K2 D2M8K2.u7763 = [0, 0, 405532119762, 1468362047232, 1394768600220, 352292187302, 16311238869, 0] := by
  rw [show D2M8K2.u7763 = KTree.node D2M8K2.u7761 (nat_lit 16388278) (nat_lit 3390271686) (nat_lit 0) D2M8K2.u7762 from rfl, totK_node, atot7761, atot7762]
  decide +kernel

theorem arows7766 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7766 = true := by
  rw [show D2M8K2.u7766 = KTree.node D2M8K2.u7764 (nat_lit 16391645) (nat_lit 2232995411) (nat_lit 0) D2M8K2.u7765 from rfl, allE_node, arows7764, irow7766, arows7765]
  all_goals rfl

theorem atot7766 : totK PD2M8K2 D2M8K2.u7766 = [0, 0, 471624682892, 1552492046712, 1374015782265, 253935328769, 7165314891, 0] := by
  rw [show D2M8K2.u7766 = KTree.node D2M8K2.u7764 (nat_lit 16391645) (nat_lit 2232995411) (nat_lit 0) D2M8K2.u7765 from rfl, totK_node, atot7764, atot7765]
  decide +kernel

theorem arows7772 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7772 = true := by
  rw [show D2M8K2.u7772 = KTree.node D2M8K2.u7770 (nat_lit 16400425) (nat_lit 1451707094) (nat_lit 0) D2M8K2.u7771 from rfl, allE_node, arows7770, irow7772, arows7771]
  all_goals rfl

theorem atot7772 : totK PD2M8K2 D2M8K2.u7772 = [0, 55649345463, 422622012534, 1385785558582, 1434125030002, 332403403249, 13949453364, 0] := by
  rw [show D2M8K2.u7772 = KTree.node D2M8K2.u7770 (nat_lit 16400425) (nat_lit 1451707094) (nat_lit 0) D2M8K2.u7771 from rfl, totK_node, atot7770, atot7771]
  decide +kernel

theorem arows7775 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7775 = true := by
  rw [show D2M8K2.u7775 = KTree.node D2M8K2.u7773 (nat_lit 16922166) (nat_lit 3750743100) (nat_lit 0) D2M8K2.u7774 from rfl, allE_node, arows7773, irow7775, arows7774]
  all_goals rfl

theorem atot7775 : totK PD2M8K2 D2M8K2.u7775 = [0, 464456400355, 1614305544432, 1329413573237, 178967320118, 1369150432, 0, 0] := by
  rw [show D2M8K2.u7775 = KTree.node D2M8K2.u7773 (nat_lit 16922166) (nat_lit 3750743100) (nat_lit 0) D2M8K2.u7774 from rfl, totK_node, atot7773, atot7774]
  decide +kernel

theorem arows7779 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7779 = true := by
  rw [show D2M8K2.u7779 = KTree.node D2M8K2.u7777 (nat_lit 16929234) (nat_lit 3060639375) (nat_lit 0) D2M8K2.u7778 from rfl, allE_node, arows7777, irow7779, arows7778]
  all_goals rfl

theorem atot7779 : totK PD2M8K2 D2M8K2.u7779 = [0, 412606470323, 1429251393536, 1401084108809, 326849654471, 13049727234, 0, 0] := by
  rw [show D2M8K2.u7779 = KTree.node D2M8K2.u7777 (nat_lit 16929234) (nat_lit 3060639375) (nat_lit 0) D2M8K2.u7778 from rfl, totK_node, atot7777, atot7778]
  decide +kernel

theorem arows7782 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7782 = true := by
  rw [show D2M8K2.u7782 = KTree.node D2M8K2.u7780 (nat_lit 16932774) (nat_lit 3749681023) (nat_lit 0) D2M8K2.u7781 from rfl, allE_node, arows7780, irow7782, arows7781]
  all_goals rfl

theorem atot7782 : totK PD2M8K2 D2M8K2.u7782 = [0, 400339336004, 1461323624874, 1386007851079, 302435206729, 13250685261, 0, 0] := by
  rw [show D2M8K2.u7782 = KTree.node D2M8K2.u7780 (nat_lit 16932774) (nat_lit 3749681023) (nat_lit 0) D2M8K2.u7781 from rfl, totK_node, atot7780, atot7781]
  decide +kernel

theorem arows7787 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7787 = true := by
  rw [show D2M8K2.u7787 = KTree.node D2M8K2.u7785 (nat_lit 16936222) (nat_lit 2989019154) (nat_lit 0) D2M8K2.u7786 from rfl, allE_node, arows7785, irow7787, arows7786]
  all_goals rfl

theorem atot7787 : totK PD2M8K2 D2M8K2.u7787 = [0, 452524078100, 1527202187672, 1358254159374, 240408114281, 4980514959, 0, 0] := by
  rw [show D2M8K2.u7787 = KTree.node D2M8K2.u7785 (nat_lit 16936222) (nat_lit 2989019154) (nat_lit 0) D2M8K2.u7786 from rfl, totK_node, atot7785, atot7786]
  decide +kernel

theorem arows7790 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7790 = true := by
  rw [show D2M8K2.u7790 = KTree.node D2M8K2.u7788 (nat_lit 16940429) (nat_lit 1930111016) (nat_lit 0) D2M8K2.u7789 from rfl, allE_node, arows7788, irow7790, arows7789]
  all_goals rfl

theorem atot7790 : totK PD2M8K2 D2M8K2.u7790 = [0, 188279367166, 1137116139023, 1662272553240, 547130725743, 24746474272, 0, 0] := by
  rw [show D2M8K2.u7790 = KTree.node D2M8K2.u7788 (nat_lit 16940429) (nat_lit 1930111016) (nat_lit 0) D2M8K2.u7789 from rfl, totK_node, atot7788, atot7789]
  decide +kernel

theorem arows7794 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7794 = true := by
  rw [show D2M8K2.u7794 = KTree.node D2M8K2.u7792 (nat_lit 16944248) (nat_lit 3785500377) (nat_lit 0) D2M8K2.u7793 from rfl, allE_node, arows7792, irow7794, arows7793]
  all_goals rfl

theorem atot7794 : totK PD2M8K2 D2M8K2.u7794 = [0, 0, 502121904945, 1665537063577, 1177640221335, 147959879205, 1369150432, 0] := by
  rw [show D2M8K2.u7794 = KTree.node D2M8K2.u7792 (nat_lit 16944248) (nat_lit 3785500377) (nat_lit 0) D2M8K2.u7793 from rfl, totK_node, atot7792, atot7793]
  decide +kernel

theorem arows7797 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7797 = true := by
  rw [show D2M8K2.u7797 = KTree.node D2M8K2.u7795 (nat_lit 16952929) (nat_lit 1487711996) (nat_lit 0) D2M8K2.u7796 from rfl, allE_node, arows7795, irow7797, arows7796]
  all_goals rfl

theorem atot7797 : totK PD2M8K2 D2M8K2.u7797 = [0, 0, 755968345247, 1906361843675, 834663143705, 38820410947, 0, 0] := by
  rw [show D2M8K2.u7797 = KTree.node D2M8K2.u7795 (nat_lit 16952929) (nat_lit 1487711996) (nat_lit 0) D2M8K2.u7796 from rfl, totK_node, atot7795, atot7796]
  decide +kernel

theorem arows7805 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7805 = true := by
  rw [show D2M8K2.u7805 = KTree.node D2M8K2.u7803 (nat_lit 16959723) (nat_lit 2189212183) (nat_lit 8) D2M8K2.u7804 from rfl, allE_node, arows7803, irow7805, arows7804]
  all_goals rfl

theorem atot7805 : totK PD2M8K2 D2M8K2.u7805 = [0, 269133968381, 1124854012946, 1592825634215, 589930324447, 27867484192, 0, 0] := by
  rw [show D2M8K2.u7805 = KTree.node D2M8K2.u7803 (nat_lit 16959723) (nat_lit 2189212183) (nat_lit 8) D2M8K2.u7804 from rfl, totK_node, atot7803, atot7804]
  decide +kernel

theorem arows7808 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7808 = true := by
  rw [show D2M8K2.u7808 = KTree.node D2M8K2.u7806 (nat_lit 16968105) (nat_lit 1700721688) (nat_lit 0) D2M8K2.u7807 from rfl, allE_node, arows7806, irow7808, arows7807]
  all_goals rfl

theorem atot7808 : totK PD2M8K2 D2M8K2.u7808 = [0, 330877232183, 1235533452728, 1475412512614, 578499943080, 37609398105, 0, 0] := by
  rw [show D2M8K2.u7808 = KTree.node D2M8K2.u7806 (nat_lit 16968105) (nat_lit 1700721688) (nat_lit 0) D2M8K2.u7807 from rfl, totK_node, atot7806, atot7807]
  decide +kernel

theorem arows7812 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7812 = true := by
  rw [show D2M8K2.u7812 = KTree.node D2M8K2.u7810 (nat_lit 16971011) (nat_lit 2838166080) (nat_lit 0) D2M8K2.u7811 from rfl, allE_node, arows7810, irow7812, arows7811]
  all_goals rfl

theorem atot7812 : totK PD2M8K2 D2M8K2.u7812 = [0, 400145224633, 1441185756635, 1433579573452, 330448975621, 13036865798, 0, 0] := by
  rw [show D2M8K2.u7812 = KTree.node D2M8K2.u7810 (nat_lit 16971011) (nat_lit 2838166080) (nat_lit 0) D2M8K2.u7811 from rfl, totK_node, atot7810, atot7811]
  decide +kernel

theorem arows7815 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7815 = true := by
  rw [show D2M8K2.u7815 = KTree.node D2M8K2.u7813 (nat_lit 16975013) (nat_lit 998140074) (nat_lit 0) D2M8K2.u7814 from rfl, allE_node, arows7813, irow7815, arows7814]
  all_goals rfl

theorem atot7815 : totK PD2M8K2 D2M8K2.u7815 = [0, 402468220750, 1485891928135, 1426202904687, 298687149108, 12040273252, 0, 0] := by
  rw [show D2M8K2.u7815 = KTree.node D2M8K2.u7813 (nat_lit 16975013) (nat_lit 998140074) (nat_lit 0) D2M8K2.u7814 from rfl, totK_node, atot7813, atot7814]
  decide +kernel

theorem arows7820 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7820 = true := by
  rw [show D2M8K2.u7820 = KTree.node D2M8K2.u7818 (nat_lit 16977996) (nat_lit 2618681704) (nat_lit 0) D2M8K2.u7819 from rfl, allE_node, arows7818, irow7820, arows7819]
  all_goals rfl

theorem atot7820 : totK PD2M8K2 D2M8K2.u7820 = [0, 437228429310, 1526170492280, 1403084262519, 254991113827, 4976872846, 0, 0] := by
  rw [show D2M8K2.u7820 = KTree.node D2M8K2.u7818 (nat_lit 16977996) (nat_lit 2618681704) (nat_lit 0) D2M8K2.u7819 from rfl, totK_node, atot7818, atot7819]
  decide +kernel

theorem arows7823 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7823 = true := by
  rw [show D2M8K2.u7823 = KTree.node D2M8K2.u7821 (nat_lit 16982528) (nat_lit 3090264992) (nat_lit 0) D2M8K2.u7822 from rfl, allE_node, arows7821, irow7823, arows7822]
  all_goals rfl

theorem atot7823 : totK PD2M8K2 D2M8K2.u7823 = [0, 158212545565, 1042668017369, 1699537680389, 711325566303, 50900649472, 0, 0] := by
  rw [show D2M8K2.u7823 = KTree.node D2M8K2.u7821 (nat_lit 16982528) (nat_lit 3090264992) (nat_lit 0) D2M8K2.u7822 from rfl, totK_node, atot7821, atot7822]
  decide +kernel

theorem arows7827 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7827 = true := by
  rw [show D2M8K2.u7827 = KTree.node D2M8K2.u7825 (nat_lit 16988942) (nat_lit 3810800606) (nat_lit 0) D2M8K2.u7826 from rfl, allE_node, arows7825, irow7827, arows7826]
  all_goals rfl

theorem atot7827 : totK PD2M8K2 D2M8K2.u7827 = [0, 0, 403576332747, 1461632667393, 1408750419981, 364636781271, 15089109266, 0] := by
  rw [show D2M8K2.u7827 = KTree.node D2M8K2.u7825 (nat_lit 16988942) (nat_lit 3810800606) (nat_lit 0) D2M8K2.u7826 from rfl, totK_node, atot7825, atot7826]
  decide +kernel

theorem arows7830 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7830 = true := by
  rw [show D2M8K2.u7830 = KTree.node D2M8K2.u7828 (nat_lit 16992638) (nat_lit 3697042353) (nat_lit 0) D2M8K2.u7829 from rfl, allE_node, arows7828, irow7830, arows7829]
  all_goals rfl

theorem atot7830 : totK PD2M8K2 D2M8K2.u7830 = [0, 0, 463548579930, 1545105077587, 1352275167904, 237124560669, 5159868635, 0] := by
  rw [show D2M8K2.u7830 = KTree.node D2M8K2.u7828 (nat_lit 16992638) (nat_lit 3697042353) (nat_lit 0) D2M8K2.u7829 from rfl, totK_node, atot7828, atot7829]
  decide +kernel

theorem arows7836 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7836 = true := by
  rw [show D2M8K2.u7836 = KTree.node D2M8K2.u7834 (nat_lit 16997472) (nat_lit 3606781488) (nat_lit 0) D2M8K2.u7835 from rfl, allE_node, arows7834, irow7836, arows7835]
  all_goals rfl

theorem atot7836 : totK PD2M8K2 D2M8K2.u7836 = [0, 0, 507169958438, 1720096766235, 1266902349355, 114862044917, 0, 0] := by
  rw [show D2M8K2.u7836 = KTree.node D2M8K2.u7834 (nat_lit 16997472) (nat_lit 3606781488) (nat_lit 0) D2M8K2.u7835 from rfl, totK_node, atot7834, atot7835]
  decide +kernel

theorem arows7839 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7839 = true := by
  rw [show D2M8K2.u7839 = KTree.node D2M8K2.u7837 (nat_lit 17001675) (nat_lit 3734332021) (nat_lit 0) D2M8K2.u7838 from rfl, allE_node, arows7837, irow7839, arows7838]
  all_goals rfl

theorem atot7839 : totK PD2M8K2 D2M8K2.u7839 = [0, 346255259307, 1180079837353, 1302478405954, 683168472354, 113248374898, 1415142070, 0] := by
  rw [show D2M8K2.u7839 = KTree.node D2M8K2.u7837 (nat_lit 17001675) (nat_lit 3734332021) (nat_lit 0) D2M8K2.u7838 from rfl, totK_node, atot7837, atot7838]
  decide +kernel

theorem arows7843 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7843 = true := by
  rw [show D2M8K2.u7843 = KTree.node D2M8K2.u7841 (nat_lit 17007362) (nat_lit 4134394906) (nat_lit 0) D2M8K2.u7842 from rfl, allE_node, arows7841, irow7843, arows7842]
  all_goals rfl

theorem atot7843 : totK PD2M8K2 D2M8K2.u7843 = [0, 479475574173, 1613885832227, 1354452640756, 186979003591, 1369150432, 0, 0] := by
  rw [show D2M8K2.u7843 = KTree.node D2M8K2.u7841 (nat_lit 17007362) (nat_lit 4134394906) (nat_lit 0) D2M8K2.u7842 from rfl, totK_node, atot7841, atot7842]
  decide +kernel

theorem arows7846 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7846 = true := by
  rw [show D2M8K2.u7846 = KTree.node D2M8K2.u7844 (nat_lit 17010154) (nat_lit 3843694039) (nat_lit 0) D2M8K2.u7845 from rfl, allE_node, arows7844, irow7846, arows7845]
  all_goals rfl

theorem atot7846 : totK PD2M8K2 D2M8K2.u7846 = [0, 304606632667, 1208691338473, 1515318960543, 585321638308, 35899802745, 0, 0] := by
  rw [show D2M8K2.u7846 = KTree.node D2M8K2.u7844 (nat_lit 17010154) (nat_lit 3843694039) (nat_lit 0) D2M8K2.u7845 from rfl, totK_node, atot7844, atot7845]
  decide +kernel

theorem arows7851 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7851 = true := by
  rw [show D2M8K2.u7851 = KTree.node D2M8K2.u7849 (nat_lit 17013010) (nat_lit 4039915514) (nat_lit 0) D2M8K2.u7850 from rfl, allE_node, arows7849, irow7851, arows7850]
  all_goals rfl

theorem atot7851 : totK PD2M8K2 D2M8K2.u7851 = [0, 397829743387, 1431734325575, 1444860339792, 331571791737, 13049727234, 0, 0] := by
  rw [show D2M8K2.u7851 = KTree.node D2M8K2.u7849 (nat_lit 17013010) (nat_lit 4039915514) (nat_lit 0) D2M8K2.u7850 from rfl, totK_node, atot7849, atot7850]
  decide +kernel

theorem arows7854 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7854 = true := by
  rw [show D2M8K2.u7854 = KTree.node D2M8K2.u7852 (nat_lit 17019954) (nat_lit 3375091217) (nat_lit 0) D2M8K2.u7853 from rfl, allE_node, arows7852, irow7854, arows7853]
  all_goals rfl

theorem atot7854 : totK PD2M8K2 D2M8K2.u7854 = [0, 419050389589, 1533550791153, 1407816795527, 247030150652, 4980514959, 0, 0] := by
  rw [show D2M8K2.u7854 = KTree.node D2M8K2.u7852 (nat_lit 17019954) (nat_lit 3375091217) (nat_lit 0) D2M8K2.u7853 from rfl, totK_node, atot7852, atot7853]
  decide +kernel

theorem arows7858 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7858 = true := by
  rw [show D2M8K2.u7858 = KTree.node D2M8K2.u7856 (nat_lit 17024170) (nat_lit 3968985432) (nat_lit 0) D2M8K2.u7857 from rfl, allE_node, arows7856, irow7858, arows7857]
  all_goals rfl

theorem atot7858 : totK PD2M8K2 D2M8K2.u7858 = [0, 89240473698, 970920868705, 1817716399947, 657475692454, 28769439323, 0, 0] := by
  rw [show D2M8K2.u7858 = KTree.node D2M8K2.u7856 (nat_lit 17024170) (nat_lit 3968985432) (nat_lit 0) D2M8K2.u7857 from rfl, totK_node, atot7856, atot7857]
  decide +kernel

theorem arows7861 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7861 = true := by
  rw [show D2M8K2.u7861 = KTree.node D2M8K2.u7859 (nat_lit 17028235) (nat_lit 1681412710) (nat_lit 0) D2M8K2.u7860 from rfl, allE_node, arows7859, irow7861, arows7860]
  all_goals rfl

theorem atot7861 : totK PD2M8K2 D2M8K2.u7861 = [0, 0, 503522407212, 1668835292402, 1252044463723, 147221099902, 1206465782, 0] := by
  rw [show D2M8K2.u7861 = KTree.node D2M8K2.u7859 (nat_lit 17028235) (nat_lit 1681412710) (nat_lit 0) D2M8K2.u7860 from rfl, totK_node, atot7859, atot7860]
  decide +kernel

theorem arows7868 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7868 = true := by
  rw [show D2M8K2.u7868 = KTree.node D2M8K2.u7866 (nat_lit 17032762) (nat_lit 3917838348) (nat_lit 0) D2M8K2.u7867 from rfl, allE_node, arows7866, irow7868, arows7867]
  all_goals rfl

theorem atot7868 : totK PD2M8K2 D2M8K2.u7868 = [0, 0, 378666566686, 1457613663301, 1389706365992, 308357471966, 13016197374, 0] := by
  rw [show D2M8K2.u7868 = KTree.node D2M8K2.u7866 (nat_lit 17032762) (nat_lit 3917838348) (nat_lit 0) D2M8K2.u7867 from rfl, totK_node, atot7866, atot7867]
  decide +kernel

theorem arows7871 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7871 = true := by
  rw [show D2M8K2.u7871 = KTree.node D2M8K2.u7869 (nat_lit 17039331) (nat_lit 3679374307) (nat_lit 0) D2M8K2.u7870 from rfl, allE_node, arows7869, irow7871, arows7870]
  all_goals rfl

theorem atot7871 : totK PD2M8K2 D2M8K2.u7871 = [0, 0, 495067400771, 1611936897567, 1216740485133, 177039489383, 4574395652, 0] := by
  rw [show D2M8K2.u7871 = KTree.node D2M8K2.u7869 (nat_lit 17039331) (nat_lit 3679374307) (nat_lit 0) D2M8K2.u7870 from rfl, totK_node, atot7869, atot7870]
  decide +kernel

theorem arows7875 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7875 = true := by
  rw [show D2M8K2.u7875 = KTree.node D2M8K2.u7873 (nat_lit 17045568) (nat_lit 3719395728) (nat_lit 0) D2M8K2.u7874 from rfl, allE_node, arows7873, irow7875, arows7874]
  all_goals rfl

theorem atot7875 : totK PD2M8K2 D2M8K2.u7875 = [0, 395471379465, 1355271047687, 1364810599146, 455060573924, 30227327220, 0, 0] := by
  rw [show D2M8K2.u7875 = KTree.node D2M8K2.u7873 (nat_lit 17045568) (nat_lit 3719395728) (nat_lit 0) D2M8K2.u7874 from rfl, totK_node, atot7873, atot7874]
  decide +kernel

theorem arows7878 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7878 = true := by
  rw [show D2M8K2.u7878 = KTree.node D2M8K2.u7876 (nat_lit 17049318) (nat_lit 3868185851) (nat_lit 0) D2M8K2.u7877 from rfl, allE_node, arows7876, irow7878, arows7877]
  all_goals rfl

theorem atot7878 : totK PD2M8K2 D2M8K2.u7878 = [0, 407209572491, 1500793211111, 1450513633959, 289972204902, 11346202446, 0, 0] := by
  rw [show D2M8K2.u7878 = KTree.node D2M8K2.u7876 (nat_lit 17049318) (nat_lit 3868185851) (nat_lit 0) D2M8K2.u7877 from rfl, totK_node, atot7876, atot7877]
  decide +kernel

theorem arows7883 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7883 = true := by
  rw [show D2M8K2.u7883 = KTree.node D2M8K2.u7881 (nat_lit 17055878) (nat_lit 3909376176) (nat_lit 0) D2M8K2.u7882 from rfl, allE_node, arows7881, irow7883, arows7882]
  all_goals rfl

theorem atot7883 : totK PD2M8K2 D2M8K2.u7883 = [0, 425945519996, 1463452226700, 1401903588764, 327145913398, 6628738483, 0, 0] := by
  rw [show D2M8K2.u7883 = KTree.node D2M8K2.u7881 (nat_lit 17055878) (nat_lit 3909376176) (nat_lit 0) D2M8K2.u7882 from rfl, totK_node, atot7881, atot7882]
  decide +kernel

theorem arows7886 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7886 = true := by
  rw [show D2M8K2.u7886 = KTree.node D2M8K2.u7884 (nat_lit 17059220) (nat_lit 3684646199) (nat_lit 0) D2M8K2.u7885 from rfl, allE_node, arows7884, irow7886, arows7885]
  all_goals rfl

theorem atot7886 : totK PD2M8K2 D2M8K2.u7886 = [0, 423317413309, 1469275434824, 1369763975780, 305641909427, 13149116973, 0, 0] := by
  rw [show D2M8K2.u7886 = KTree.node D2M8K2.u7884 (nat_lit 17059220) (nat_lit 3684646199) (nat_lit 0) D2M8K2.u7885 from rfl, totK_node, atot7884, atot7885]
  decide +kernel

theorem arows7890 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7890 = true := by
  rw [show D2M8K2.u7890 = KTree.node D2M8K2.u7888 (nat_lit 17066506) (nat_lit 3600821819) (nat_lit 0) D2M8K2.u7889 from rfl, allE_node, arows7888, irow7890, arows7889]
  all_goals rfl

theorem atot7890 : totK PD2M8K2 D2M8K2.u7890 = [0, 0, 729257097861, 1842178915385, 877304947668, 72191446704, 1239866073, 0] := by
  rw [show D2M8K2.u7890 = KTree.node D2M8K2.u7888 (nat_lit 17066506) (nat_lit 3600821819) (nat_lit 0) D2M8K2.u7889 from rfl, totK_node, atot7888, atot7889]
  decide +kernel

theorem arows7893 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7893 = true := by
  rw [show D2M8K2.u7893 = KTree.node D2M8K2.u7891 (nat_lit 17070384) (nat_lit 2431182402) (nat_lit 0) D2M8K2.u7892 from rfl, allE_node, arows7891, irow7893, arows7892]
  all_goals rfl

theorem atot7893 : totK PD2M8K2 D2M8K2.u7893 = [0, 0, 669862794130, 1845892311317, 1035922586837, 76462841279, 0, 0] := by
  rw [show D2M8K2.u7893 = KTree.node D2M8K2.u7891 (nat_lit 17070384) (nat_lit 2431182402) (nat_lit 0) D2M8K2.u7892 from rfl, totK_node, atot7891, atot7892]
  decide +kernel

theorem arows7899 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7899 = true := by
  rw [show D2M8K2.u7899 = KTree.node D2M8K2.u7897 (nat_lit 17080170) (nat_lit 3202283356) (nat_lit 0) D2M8K2.u7898 from rfl, allE_node, arows7897, irow7899, arows7898]
  all_goals rfl

theorem atot7899 : totK PD2M8K2 D2M8K2.u7899 = [0, 0, 580663613838, 1765583726907, 1080500371193, 103183648085, 1053411165, 0] := by
  rw [show D2M8K2.u7899 = KTree.node D2M8K2.u7897 (nat_lit 17080170) (nat_lit 3202283356) (nat_lit 0) D2M8K2.u7898 from rfl, totK_node, atot7897, atot7898]
  decide +kernel

theorem arows7902 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7902 = true := by
  rw [show D2M8K2.u7902 = KTree.node D2M8K2.u7900 (nat_lit 17087552) (nat_lit 3610118551) (nat_lit 0) D2M8K2.u7901 from rfl, allE_node, arows7900, irow7902, arows7901]
  all_goals rfl

theorem atot7902 : totK PD2M8K2 D2M8K2.u7902 = [0, 412428170261, 1330631615770, 1203614351647, 472356009998, 93568442076, 3667207281, 0] := by
  rw [show D2M8K2.u7902 = KTree.node D2M8K2.u7900 (nat_lit 17087552) (nat_lit 3610118551) (nat_lit 0) D2M8K2.u7901 from rfl, totK_node, atot7900, atot7901]
  decide +kernel

theorem arows7906 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7906 = true := by
  rw [show D2M8K2.u7906 = KTree.node D2M8K2.u7904 (nat_lit 17091113) (nat_lit 1803274704) (nat_lit 0) D2M8K2.u7905 from rfl, allE_node, arows7904, irow7906, arows7905]
  all_goals rfl

theorem atot7906 : totK PD2M8K2 D2M8K2.u7906 = [0, 422721023562, 1458531026294, 1373371963638, 358308494178, 25127349078, 0, 0] := by
  rw [show D2M8K2.u7906 = KTree.node D2M8K2.u7904 (nat_lit 17091113) (nat_lit 1803274704) (nat_lit 0) D2M8K2.u7905 from rfl, totK_node, atot7904, atot7905]
  decide +kernel

theorem arows7909 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7909 = true := by
  rw [show D2M8K2.u7909 = KTree.node D2M8K2.u7907 (nat_lit 17093932) (nat_lit 3811927988) (nat_lit 0) D2M8K2.u7908 from rfl, allE_node, arows7907, irow7909, arows7908]
  all_goals rfl

theorem atot7909 : totK PD2M8K2 D2M8K2.u7909 = [0, 421735944401, 1405522233418, 1378614118598, 386167942903, 12007340912, 0, 0] := by
  rw [show D2M8K2.u7909 = KTree.node D2M8K2.u7907 (nat_lit 17093932) (nat_lit 3811927988) (nat_lit 0) D2M8K2.u7908 from rfl, totK_node, atot7907, atot7908]
  decide +kernel

theorem arows7914 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7914 = true := by
  rw [show D2M8K2.u7914 = KTree.node D2M8K2.u7912 (nat_lit 17097322) (nat_lit 3208249705) (nat_lit 0) D2M8K2.u7913 from rfl, allE_node, arows7912, irow7914, arows7913]
  all_goals rfl

theorem atot7914 : totK PD2M8K2 D2M8K2.u7914 = [0, 401120482411, 1425044976962, 1402475933345, 323240083842, 13083481006, 0, 0] := by
  rw [show D2M8K2.u7914 = KTree.node D2M8K2.u7912 (nat_lit 17097322) (nat_lit 3208249705) (nat_lit 0) D2M8K2.u7913 from rfl, totK_node, atot7912, atot7913]
  decide +kernel

theorem arows7917 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7917 = true := by
  rw [show D2M8K2.u7917 = KTree.node D2M8K2.u7915 (nat_lit 17100777) (nat_lit 1815847795) (nat_lit 0) D2M8K2.u7916 from rfl, allE_node, arows7915, irow7917, arows7916]
  all_goals rfl

theorem atot7917 : totK PD2M8K2 D2M8K2.u7917 = [0, 444327868927, 1482534615860, 1354724044701, 300406377492, 13149116973, 0, 0] := by
  rw [show D2M8K2.u7917 = KTree.node D2M8K2.u7915 (nat_lit 17100777) (nat_lit 1815847795) (nat_lit 0) D2M8K2.u7916 from rfl, totK_node, atot7915, atot7916]
  decide +kernel

theorem arows7921 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7921 = true := by
  rw [show D2M8K2.u7921 = KTree.node D2M8K2.u7919 (nat_lit 17107930) (nat_lit 3567605960) (nat_lit 0) D2M8K2.u7920 from rfl, allE_node, arows7919, irow7921, arows7920]
  all_goals rfl

theorem atot7921 : totK PD2M8K2 D2M8K2.u7921 = [0, 0, 764305764325, 1821383628684, 849703444876, 86990231696, 1138244013, 0] := by
  rw [show D2M8K2.u7921 = KTree.node D2M8K2.u7919 (nat_lit 17107930) (nat_lit 3567605960) (nat_lit 0) D2M8K2.u7920 from rfl, totK_node, atot7919, atot7920]
  decide +kernel

theorem arows7924 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7924 = true := by
  rw [show D2M8K2.u7924 = KTree.node D2M8K2.u7922 (nat_lit 17111674) (nat_lit 1959927352) (nat_lit 0) D2M8K2.u7923 from rfl, allE_node, arows7922, irow7924, arows7923]
  all_goals rfl

theorem atot7924 : totK PD2M8K2 D2M8K2.u7924 = [0, 0, 630201670099, 1834647889189, 1046705217722, 79430736059, 0, 0] := by
  rw [show D2M8K2.u7924 = KTree.node D2M8K2.u7922 (nat_lit 17111674) (nat_lit 1959927352) (nat_lit 0) D2M8K2.u7923 from rfl, totK_node, atot7922, atot7923]
  decide +kernel

theorem arows7933 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7933 = true := by
  rw [show D2M8K2.u7933 = KTree.node D2M8K2.u7931 (nat_lit 17118059) (nat_lit 1328344382) (nat_lit 2176) D2M8K2.u7932 from rfl, allE_node, arows7931, irow7933, arows7932]
  all_goals rfl

theorem atot7933 : totK PD2M8K2 D2M8K2.u7933 = [0, 0, 766800583523, 1904550065106, 847848963411, 42081618632, 0, 0] := by
  rw [show D2M8K2.u7933 = KTree.node D2M8K2.u7931 (nat_lit 17118059) (nat_lit 1328344382) (nat_lit 2176) D2M8K2.u7932 from rfl, totK_node, atot7931, atot7932]
  decide +kernel

theorem arows7936 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7936 = true := by
  rw [show D2M8K2.u7936 = KTree.node D2M8K2.u7934 (nat_lit 17122890) (nat_lit 2241698787) (nat_lit 0) D2M8K2.u7935 from rfl, allE_node, arows7934, irow7936, arows7935]
  all_goals rfl

theorem atot7936 : totK PD2M8K2 D2M8K2.u7936 = [0, 0, 449767047686, 1579014444687, 1292050652321, 224840266308, 4977114383, 0] := by
  rw [show D2M8K2.u7936 = KTree.node D2M8K2.u7934 (nat_lit 17122890) (nat_lit 2241698787) (nat_lit 0) D2M8K2.u7935 from rfl, totK_node, atot7934, atot7935]
  decide +kernel

theorem arows7940 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7940 = true := by
  rw [show D2M8K2.u7940 = KTree.node D2M8K2.u7938 (nat_lit 17171302) (nat_lit 2788831180) (nat_lit 0) D2M8K2.u7939 from rfl, allE_node, arows7938, irow7940, arows7939]
  all_goals rfl

theorem atot7940 : totK PD2M8K2 D2M8K2.u7940 = [0, 0, 432846236834, 1594248899013, 1349556652622, 167963219324, 1369150432, 0] := by
  rw [show D2M8K2.u7940 = KTree.node D2M8K2.u7938 (nat_lit 17171302) (nat_lit 2788831180) (nat_lit 0) D2M8K2.u7939 from rfl, totK_node, atot7938, atot7939]
  decide +kernel

theorem arows7943 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7943 = true := by
  rw [show D2M8K2.u7943 = KTree.node D2M8K2.u7941 (nat_lit 17178635) (nat_lit 2759145808) (nat_lit 0) D2M8K2.u7942 from rfl, allE_node, arows7941, irow7943, arows7942]
  all_goals rfl

theorem atot7943 : totK PD2M8K2 D2M8K2.u7943 = [0, 0, 457589404661, 1462007115337, 1328881749423, 285079481290, 12983449796, 0] := by
  rw [show D2M8K2.u7943 = KTree.node D2M8K2.u7941 (nat_lit 17178635) (nat_lit 2759145808) (nat_lit 0) D2M8K2.u7942 from rfl, totK_node, atot7941, atot7942]
  decide +kernel

theorem arows7948 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7948 = true := by
  rw [show D2M8K2.u7948 = KTree.node D2M8K2.u7946 (nat_lit 17182948) (nat_lit 3174265098) (nat_lit 0) D2M8K2.u7947 from rfl, allE_node, arows7946, irow7948, arows7947]
  all_goals rfl

theorem atot7948 : totK PD2M8K2 D2M8K2.u7948 = [0, 0, 494288890775, 1695749479679, 1200967380856, 117920452746, 1198073392, 0] := by
  rw [show D2M8K2.u7948 = KTree.node D2M8K2.u7946 (nat_lit 17182948) (nat_lit 3174265098) (nat_lit 0) D2M8K2.u7947 from rfl, totK_node, atot7946, atot7947]
  decide +kernel

theorem arows7951 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7951 = true := by
  rw [show D2M8K2.u7951 = KTree.node D2M8K2.u7949 (nat_lit 17186689) (nat_lit 1573165124) (nat_lit 0) D2M8K2.u7950 from rfl, allE_node, arows7949, irow7951, arows7950]
  all_goals rfl

theorem atot7951 : totK PD2M8K2 D2M8K2.u7951 = [0, 0, 398235441239, 1528256834870, 1391289378574, 233394228167, 6249254262, 0] := by
  rw [show D2M8K2.u7951 = KTree.node D2M8K2.u7949 (nat_lit 17186689) (nat_lit 1573165124) (nat_lit 0) D2M8K2.u7950 from rfl, totK_node, atot7949, atot7950]
  decide +kernel

theorem arows7955 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7955 = true := by
  rw [show D2M8K2.u7955 = KTree.node D2M8K2.u7953 (nat_lit 17191283) (nat_lit 1510237767) (nat_lit 2176) D2M8K2.u7954 from rfl, allE_node, arows7953, irow7955, arows7954]
  all_goals rfl

theorem atot7955 : totK PD2M8K2 D2M8K2.u7955 = [0, 0, 0, 661015316032, 1783347243646, 903243140351, 84726108146, 1209030869] := by
  rw [show D2M8K2.u7955 = KTree.node D2M8K2.u7953 (nat_lit 17191283) (nat_lit 1510237767) (nat_lit 2176) D2M8K2.u7954 from rfl, totK_node, atot7953, atot7954]
  decide +kernel

theorem arows7958 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7958 = true := by
  rw [show D2M8K2.u7958 = KTree.node D2M8K2.u7956 (nat_lit 17200633) (nat_lit 1519040599) (nat_lit 0) D2M8K2.u7957 from rfl, allE_node, arows7956, irow7958, arows7957]
  all_goals rfl

theorem atot7958 : totK PD2M8K2 D2M8K2.u7958 = [0, 0, 0, 956821343154, 1960680455521, 578536639862, 18766565647, 0] := by
  rw [show D2M8K2.u7958 = KTree.node D2M8K2.u7956 (nat_lit 17200633) (nat_lit 1519040599) (nat_lit 0) D2M8K2.u7957 from rfl, totK_node, atot7956, atot7957]
  decide +kernel

theorem arows7964 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7964 = true := by
  rw [show D2M8K2.u7964 = KTree.node D2M8K2.u7962 (nat_lit 17208384) (nat_lit 3430850179) (nat_lit 0) D2M8K2.u7963 from rfl, allE_node, arows7962, irow7964, arows7963]
  all_goals rfl

theorem atot7964 : totK PD2M8K2 D2M8K2.u7964 = [0, 0, 333771904467, 1315693178289, 1553958559785, 378320257323, 14662721225, 0] := by
  rw [show D2M8K2.u7964 = KTree.node D2M8K2.u7962 (nat_lit 17208384) (nat_lit 3430850179) (nat_lit 0) D2M8K2.u7963 from rfl, totK_node, atot7962, atot7963]
  decide +kernel

theorem arows7967 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7967 = true := by
  rw [show D2M8K2.u7967 = KTree.node D2M8K2.u7965 (nat_lit 17217277) (nat_lit 1130067175) (nat_lit 0) D2M8K2.u7966 from rfl, allE_node, arows7965, irow7967, arows7966]
  all_goals rfl

theorem atot7967 : totK PD2M8K2 D2M8K2.u7967 = [0, 0, 408009114820, 1484639865788, 1429491473002, 351127237514, 15318296608, 0] := by
  rw [show D2M8K2.u7967 = KTree.node D2M8K2.u7965 (nat_lit 17217277) (nat_lit 1130067175) (nat_lit 0) D2M8K2.u7966 from rfl, totK_node, atot7965, atot7966]
  decide +kernel

theorem arows7971 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7971 = true := by
  rw [show D2M8K2.u7971 = KTree.node D2M8K2.u7969 (nat_lit 17220869) (nat_lit 2343373989) (nat_lit 0) D2M8K2.u7970 from rfl, allE_node, arows7969, irow7971, arows7970]
  all_goals rfl

theorem atot7971 : totK PD2M8K2 D2M8K2.u7971 = [0, 0, 477176209426, 1564212132443, 1346237803415, 245655884709, 9751947372, 0] := by
  rw [show D2M8K2.u7971 = KTree.node D2M8K2.u7969 (nat_lit 17220869) (nat_lit 2343373989) (nat_lit 0) D2M8K2.u7970 from rfl, totK_node, atot7969, atot7970]
  decide +kernel

theorem arows7974 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7974 = true := by
  rw [show D2M8K2.u7974 = KTree.node D2M8K2.u7972 (nat_lit 17225906) (nat_lit 4020524323) (nat_lit 0) D2M8K2.u7973 from rfl, allE_node, arows7972, irow7974, arows7973]
  all_goals rfl

theorem atot7974 : totK PD2M8K2 D2M8K2.u7974 = [0, 0, 527275111388, 1642363156248, 1273566263004, 181117257084, 2813333534, 0] := by
  rw [show D2M8K2.u7974 = KTree.node D2M8K2.u7972 (nat_lit 17225906) (nat_lit 4020524323) (nat_lit 0) D2M8K2.u7973 from rfl, totK_node, atot7972, atot7973]
  decide +kernel

theorem arows7979 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7979 = true := by
  rw [show D2M8K2.u7979 = KTree.node D2M8K2.u7977 (nat_lit 17253045) (nat_lit 1733384879) (nat_lit 0) D2M8K2.u7978 from rfl, allE_node, arows7977, irow7979, arows7978]
  all_goals rfl

theorem atot7979 : totK PD2M8K2 D2M8K2.u7979 = [0, 0, 646430382024, 1762155552572, 1064966318710, 125118943946, 1310166938, 0] := by
  rw [show D2M8K2.u7979 = KTree.node D2M8K2.u7977 (nat_lit 17253045) (nat_lit 1733384879) (nat_lit 0) D2M8K2.u7978 from rfl, totK_node, atot7977, atot7978]
  decide +kernel

theorem arows7982 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7982 = true := by
  rw [show D2M8K2.u7982 = KTree.node D2M8K2.u7980 (nat_lit 17256754) (nat_lit 3002724300) (nat_lit 32) D2M8K2.u7981 from rfl, allE_node, arows7980, irow7982, arows7981]
  all_goals rfl

theorem atot7982 : totK PD2M8K2 D2M8K2.u7982 = [0, 0, 414348102434, 1502188720138, 1424547274579, 287911056750, 13604428459, 0] := by
  rw [show D2M8K2.u7982 = KTree.node D2M8K2.u7980 (nat_lit 17256754) (nat_lit 3002724300) (nat_lit 32) D2M8K2.u7981 from rfl, totK_node, atot7980, atot7981]
  decide +kernel

theorem arows7986 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7986 = true := by
  rw [show D2M8K2.u7986 = KTree.node D2M8K2.u7984 (nat_lit 17259964) (nat_lit 3961990416) (nat_lit 0) D2M8K2.u7985 from rfl, allE_node, arows7984, irow7986, arows7985]
  all_goals rfl

theorem atot7986 : totK PD2M8K2 D2M8K2.u7986 = [0, 0, 439388529686, 1571661089400, 1391669210949, 235248822409, 2573880433, 0] := by
  rw [show D2M8K2.u7986 = KTree.node D2M8K2.u7984 (nat_lit 17259964) (nat_lit 3961990416) (nat_lit 0) D2M8K2.u7985 from rfl, totK_node, atot7984, atot7985]
  decide +kernel

theorem arows7989 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7989 = true := by
  rw [show D2M8K2.u7989 = KTree.node D2M8K2.u7987 (nat_lit 17266744) (nat_lit 3530258422) (nat_lit 0) D2M8K2.u7988 from rfl, allE_node, arows7987, irow7989, arows7988]
  all_goals rfl

theorem atot7989 : totK PD2M8K2 D2M8K2.u7989 = [0, 0, 418705335490, 1442868316867, 1375851068013, 296454185184, 12981912718, 0] := by
  rw [show D2M8K2.u7989 = KTree.node D2M8K2.u7987 (nat_lit 17266744) (nat_lit 3530258422) (nat_lit 0) D2M8K2.u7988 from rfl, totK_node, atot7987, atot7988]
  decide +kernel

theorem arows7996 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7996 = true := by
  rw [show D2M8K2.u7996 = KTree.node D2M8K2.u7994 (nat_lit 17270305) (nat_lit 1431161237) (nat_lit 0) D2M8K2.u7995 from rfl, allE_node, arows7994, irow7996, arows7995]
  all_goals rfl

theorem atot7996 : totK PD2M8K2 D2M8K2.u7996 = [0, 0, 343248808889, 1424837903895, 1520371645754, 309365862783, 8764905022, 0] := by
  rw [show D2M8K2.u7996 = KTree.node D2M8K2.u7994 (nat_lit 17270305) (nat_lit 1431161237) (nat_lit 0) D2M8K2.u7995 from rfl, totK_node, atot7994, atot7995]
  decide +kernel

theorem arows7999 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u7999 = true := by
  rw [show D2M8K2.u7999 = KTree.node D2M8K2.u7997 (nat_lit 17295406) (nat_lit 4050112848) (nat_lit 0) D2M8K2.u7998 from rfl, allE_node, arows7997, irow7999, arows7998]
  all_goals rfl

theorem atot7999 : totK PD2M8K2 D2M8K2.u7999 = [0, 0, 523198524657, 1705828034345, 1218894262537, 123044605751, 1310517177, 0] := by
  rw [show D2M8K2.u7999 = KTree.node D2M8K2.u7997 (nat_lit 17295406) (nat_lit 4050112848) (nat_lit 0) D2M8K2.u7998 from rfl, totK_node, atot7997, atot7998]
  decide +kernel

theorem arows8003 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8003 = true := by
  rw [show D2M8K2.u8003 = KTree.node D2M8K2.u8001 (nat_lit 17304728) (nat_lit 3875261842) (nat_lit 0) D2M8K2.u8002 from rfl, allE_node, arows8001, irow8003, arows8002]
  all_goals rfl

theorem atot8003 : totK PD2M8K2 D2M8K2.u8003 = [0, 0, 832553603385, 1928078430571, 838796396463, 45852174401, 0, 0] := by
  rw [show D2M8K2.u8003 = KTree.node D2M8K2.u8001 (nat_lit 17304728) (nat_lit 3875261842) (nat_lit 0) D2M8K2.u8002 from rfl, totK_node, atot8001, atot8002]
  decide +kernel

theorem arows8006 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8006 = true := by
  rw [show D2M8K2.u8006 = KTree.node D2M8K2.u8004 (nat_lit 17309542) (nat_lit 1259339707) (nat_lit 0) D2M8K2.u8005 from rfl, allE_node, arows8004, irow8006, arows8005]
  all_goals rfl

theorem atot8006 : totK PD2M8K2 D2M8K2.u8006 = [0, 0, 460835518935, 1608728608378, 1292285977532, 196964119518, 4980514959, 0] := by
  rw [show D2M8K2.u8006 = KTree.node D2M8K2.u8004 (nat_lit 17309542) (nat_lit 1259339707) (nat_lit 0) D2M8K2.u8005 from rfl, totK_node, atot8004, atot8005]
  decide +kernel

theorem arows8011 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8011 = true := by
  rw [show D2M8K2.u8011 = KTree.node D2M8K2.u8009 (nat_lit 17337710) (nat_lit 3086535083) (nat_lit 0) D2M8K2.u8010 from rfl, allE_node, arows8009, irow8011, arows8010]
  all_goals rfl

theorem atot8011 : totK PD2M8K2 D2M8K2.u8011 = [0, 0, 478067909328, 1565964279007, 1298093560757, 159825004741, 1326647619, 0] := by
  rw [show D2M8K2.u8011 = KTree.node D2M8K2.u8009 (nat_lit 17337710) (nat_lit 3086535083) (nat_lit 0) D2M8K2.u8010 from rfl, totK_node, atot8009, atot8010]
  decide +kernel

theorem arows8014 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8014 = true := by
  rw [show D2M8K2.u8014 = KTree.node D2M8K2.u8012 (nat_lit 17341389) (nat_lit 1468804400) (nat_lit 0) D2M8K2.u8013 from rfl, allE_node, arows8012, irow8014, arows8013]
  all_goals rfl

theorem atot8014 : totK PD2M8K2 D2M8K2.u8014 = [0, 0, 431639036464, 1483988235954, 1356435178807, 330738599609, 15035393367, 0] := by
  rw [show D2M8K2.u8014 = KTree.node D2M8K2.u8012 (nat_lit 17341389) (nat_lit 1468804400) (nat_lit 0) D2M8K2.u8013 from rfl, totK_node, atot8012, atot8013]
  decide +kernel

theorem arows8018 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8018 = true := by
  rw [show D2M8K2.u8018 = KTree.node D2M8K2.u8016 (nat_lit 17344678) (nat_lit 1811576242) (nat_lit 0) D2M8K2.u8017 from rfl, allE_node, arows8016, irow8018, arows8017]
  all_goals rfl

theorem atot8018 : totK PD2M8K2 D2M8K2.u8018 = [0, 0, 411628940410, 1449603568054, 1381061730479, 289160455350, 12909266092, 0] := by
  rw [show D2M8K2.u8018 = KTree.node D2M8K2.u8016 (nat_lit 17344678) (nat_lit 1811576242) (nat_lit 0) D2M8K2.u8017 from rfl, totK_node, atot8016, atot8017]
  decide +kernel

theorem arows8021 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u8021 = true := by
  rw [show D2M8K2.u8021 = KTree.node D2M8K2.u8019 (nat_lit 17348695) (nat_lit 2213781112) (nat_lit 0) D2M8K2.u8020 from rfl, allE_node, arows8019, irow8021, arows8020]
  all_goals rfl

theorem atot8021 : totK PD2M8K2 D2M8K2.u8021 = [0, 0, 487526042585, 1597027354123, 1275920765487, 199271086663, 4744690043, 0] := by
  rw [show D2M8K2.u8021 = KTree.node D2M8K2.u8019 (nat_lit 17348695) (nat_lit 2213781112) (nat_lit 0) D2M8K2.u8020 from rfl, totK_node, atot8019, atot8020]
  decide +kernel

end QECKChecks.D2M8K2
