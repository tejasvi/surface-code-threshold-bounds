import QEC.Count.ChunksK3
import QEC.KChecks.D2M8K2.A3

namespace QECKChecks.D2M8K2

open QEC QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem arows4796 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4796 = true := by
  rw [show D2M8K2.u4796 = KTree.node D2M8K2.t4800 (nat_lit 10671339) (nat_lit 3644227898) (nat_lit 0) D2M8K2.t4801 from rfl, allE_node, rows4800, irow4796, rows4801]
  all_goals rfl

theorem atot4796 : totK PD2M8K2 D2M8K2.u4796 = [0, 0, 492729006014, 973617524506, 301748826128, 13243784863, 0, 0] := by
  rw [show D2M8K2.u4796 = KTree.node D2M8K2.t4800 (nat_lit 10671339) (nat_lit 3644227898) (nat_lit 0) D2M8K2.t4801 from rfl, totK_node, tot4800, tot4801]
  decide +kernel

theorem arows4797 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4797 = true := by
  rw [show D2M8K2.u4797 = KTree.node D2M8K2.t4802 (nat_lit 10676165) (nat_lit 2339102798) (nat_lit 0) D2M8K2.t4803 from rfl, allE_node, rows4802, irow4797, rows4803]
  all_goals rfl

theorem atot4797 : totK PD2M8K2 D2M8K2.u4797 = [0, 376406383960, 924686102983, 482066019761, 44021277993, 0, 0, 0] := by
  rw [show D2M8K2.u4797 = KTree.node D2M8K2.t4802 (nat_lit 10676165) (nat_lit 2339102798) (nat_lit 0) D2M8K2.t4803 from rfl, totK_node, tot4802, tot4803]
  decide +kernel

theorem arows4799 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4799 = true := by
  rw [show D2M8K2.u4799 = KTree.node D2M8K2.t4804 (nat_lit 10677672) (nat_lit 2761635319) (nat_lit 0) D2M8K2.t4805 from rfl, allE_node, rows4804, irow4799, rows4805]
  all_goals rfl

theorem atot4799 : totK PD2M8K2 D2M8K2.u4799 = [0, 60772201050, 549554189996, 900699048805, 270372832188, 8710740030, 0, 0] := by
  rw [show D2M8K2.u4799 = KTree.node D2M8K2.t4804 (nat_lit 10677672) (nat_lit 2761635319) (nat_lit 0) D2M8K2.t4805 from rfl, totK_node, tot4804, tot4805]
  decide +kernel

theorem arows4800 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4800 = true := by
  rw [show D2M8K2.u4800 = KTree.node D2M8K2.t4806 (nat_lit 10679311) (nat_lit 1858120047) (nat_lit 0) D2M8K2.t4807 from rfl, allE_node, rows4806, irow4800, rows4807]
  all_goals rfl

theorem atot4800 : totK PD2M8K2 D2M8K2.u4800 = [0, 0, 382589870223, 956316012019, 418263762600, 22692591333, 0, 0] := by
  rw [show D2M8K2.u4800 = KTree.node D2M8K2.t4806 (nat_lit 10679311) (nat_lit 1858120047) (nat_lit 0) D2M8K2.t4807 from rfl, totK_node, tot4806, tot4807]
  decide +kernel

theorem arows4803 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4803 = true := by
  rw [show D2M8K2.u4803 = KTree.node D2M8K2.t4808 (nat_lit 10681042) (nat_lit 3972028027) (nat_lit 0) D2M8K2.t4809 from rfl, allE_node, rows4808, irow4803, rows4809]
  all_goals rfl

theorem atot4803 : totK PD2M8K2 D2M8K2.u4803 = [0, 0, 141020145533, 702252872362, 817894780362, 115627775815, 1310285577, 0] := by
  rw [show D2M8K2.u4803 = KTree.node D2M8K2.t4808 (nat_lit 10681042) (nat_lit 3972028027) (nat_lit 0) D2M8K2.t4809 from rfl, totK_node, tot4808, tot4809]
  decide +kernel

theorem arows4804 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4804 = true := by
  rw [show D2M8K2.u4804 = KTree.node D2M8K2.t4810 (nat_lit 10683452) (nat_lit 3275019677) (nat_lit 0) D2M8K2.t4811 from rfl, allE_node, rows4810, irow4804, rows4811]
  all_goals rfl

theorem atot4804 : totK PD2M8K2 D2M8K2.u4804 = [0, 0, 363343121777, 946059947641, 503383392256, 36498022409, 0, 0] := by
  rw [show D2M8K2.u4804 = KTree.node D2M8K2.t4810 (nat_lit 10683452) (nat_lit 3275019677) (nat_lit 0) D2M8K2.t4811 from rfl, totK_node, tot4810, tot4811]
  decide +kernel

theorem arows4806 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4806 = true := by
  rw [show D2M8K2.u4806 = KTree.node D2M8K2.t4812 (nat_lit 10686514) (nat_lit 4121252693) (nat_lit 0) D2M8K2.t4813 from rfl, allE_node, rows4812, irow4806, rows4813]
  all_goals rfl

theorem atot4806 : totK PD2M8K2 D2M8K2.u4806 = [0, 0, 329289148201, 907434637566, 550926024019, 47656629364, 0, 0] := by
  rw [show D2M8K2.u4806 = KTree.node D2M8K2.t4812 (nat_lit 10686514) (nat_lit 4121252693) (nat_lit 0) D2M8K2.t4813 from rfl, totK_node, tot4812, tot4813]
  decide +kernel

theorem arows4807 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4807 = true := by
  rw [show D2M8K2.u4807 = KTree.node D2M8K2.t4814 (nat_lit 10689242) (nat_lit 4010599527) (nat_lit 0) D2M8K2.t4815 from rfl, allE_node, rows4814, irow4807, rows4815]
  all_goals rfl

theorem atot4807 : totK PD2M8K2 D2M8K2.u4807 = [0, 0, 170769880466, 757387803954, 754441624319, 119412772340, 1435164049, 0] := by
  rw [show D2M8K2.u4807 = KTree.node D2M8K2.t4814 (nat_lit 10689242) (nat_lit 4010599527) (nat_lit 0) D2M8K2.t4815 from rfl, totK_node, tot4814, tot4815]
  decide +kernel

theorem arows4811 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4811 = true := by
  rw [show D2M8K2.u4811 = KTree.node D2M8K2.t4816 (nat_lit 10690895) (nat_lit 2155777725) (nat_lit 0) D2M8K2.t4817 from rfl, allE_node, rows4816, irow4811, rows4817]
  all_goals rfl

theorem atot4811 : totK PD2M8K2 D2M8K2.u4811 = [0, 0, 251914524262, 808688158010, 637649644832, 88983788813, 1107157161, 0] := by
  rw [show D2M8K2.u4811 = KTree.node D2M8K2.t4816 (nat_lit 10690895) (nat_lit 2155777725) (nat_lit 0) D2M8K2.t4817 from rfl, totK_node, tot4816, tot4817]
  decide +kernel

theorem arows4812 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4812 = true := by
  rw [show D2M8K2.u4812 = KTree.node D2M8K2.t4818 (nat_lit 10696401) (nat_lit 1654805407) (nat_lit 0) D2M8K2.t4819 from rfl, allE_node, rows4818, irow4812, rows4819]
  all_goals rfl

theorem atot4812 : totK PD2M8K2 D2M8K2.u4812 = [0, 0, 227840288610, 762689377155, 662135419040, 126680175120, 3824247485, 0] := by
  rw [show D2M8K2.u4812 = KTree.node D2M8K2.t4818 (nat_lit 10696401) (nat_lit 1654805407) (nat_lit 0) D2M8K2.t4819 from rfl, totK_node, tot4818, tot4819]
  decide +kernel

theorem arows4814 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4814 = true := by
  rw [show D2M8K2.u4814 = KTree.node D2M8K2.t4820 (nat_lit 10697884) (nat_lit 3920975462) (nat_lit 0) D2M8K2.t4821 from rfl, allE_node, rows4820, irow4814, rows4821]
  all_goals rfl

theorem atot4814 : totK PD2M8K2 D2M8K2.u4814 = [0, 0, 210879195335, 791604162009, 696362697129, 106903238620, 1242138600, 0] := by
  rw [show D2M8K2.u4814 = KTree.node D2M8K2.t4820 (nat_lit 10697884) (nat_lit 3920975462) (nat_lit 0) D2M8K2.t4821 from rfl, totK_node, tot4820, tot4821]
  decide +kernel

theorem arows4815 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4815 = true := by
  rw [show D2M8K2.u4815 = KTree.node D2M8K2.t4822 (nat_lit 10699613) (nat_lit 2264020349) (nat_lit 0) D2M8K2.t4823 from rfl, allE_node, rows4822, irow4815, rows4823]
  all_goals rfl

theorem atot4815 : totK PD2M8K2 D2M8K2.u4815 = [0, 0, 161913507163, 591586619897, 720015644903, 269733997552, 16842185461, 0] := by
  rw [show D2M8K2.u4815 = KTree.node D2M8K2.t4822 (nat_lit 10699613) (nat_lit 2264020349) (nat_lit 0) D2M8K2.t4823 from rfl, totK_node, tot4822, tot4823]
  decide +kernel

theorem arows4818 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4818 = true := by
  rw [show D2M8K2.u4818 = KTree.node D2M8K2.t4824 (nat_lit 10701153) (nat_lit 1838053868) (nat_lit 0) D2M8K2.t4825 from rfl, allE_node, rows4824, irow4818, rows4825]
  all_goals rfl

theorem atot4818 : totK PD2M8K2 D2M8K2.u4818 = [0, 0, 257094038275, 799431084470, 615616657616, 93343101114, 1369150432, 0] := by
  rw [show D2M8K2.u4818 = KTree.node D2M8K2.t4824 (nat_lit 10701153) (nat_lit 1838053868) (nat_lit 0) D2M8K2.t4825 from rfl, totK_node, tot4824, tot4825]
  decide +kernel

theorem arows4819 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4819 = true := by
  rw [show D2M8K2.u4819 = KTree.node D2M8K2.t4826 (nat_lit 10710208) (nat_lit 2797098011) (nat_lit 0) D2M8K2.t4827 from rfl, allE_node, rows4826, irow4819, rows4827]
  all_goals rfl

theorem atot4819 : totK PD2M8K2 D2M8K2.u4819 = [0, 0, 233636852470, 833411750966, 683732912449, 58190232981, 0, 0] := by
  rw [show D2M8K2.u4819 = KTree.node D2M8K2.t4826 (nat_lit 10710208) (nat_lit 2797098011) (nat_lit 0) D2M8K2.t4827 from rfl, totK_node, tot4826, tot4827]
  decide +kernel

theorem arows4821 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4821 = true := by
  rw [show D2M8K2.u4821 = KTree.node D2M8K2.t4828 (nat_lit 10711728) (nat_lit 3678685636) (nat_lit 0) D2M8K2.t4829 from rfl, allE_node, rows4828, irow4821, rows4829]
  all_goals rfl

theorem atot4821 : totK PD2M8K2 D2M8K2.u4821 = [0, 0, 343204091483, 936199788322, 480723672435, 28075779384, 0, 0] := by
  rw [show D2M8K2.u4821 = KTree.node D2M8K2.t4828 (nat_lit 10711728) (nat_lit 3678685636) (nat_lit 0) D2M8K2.t4829 from rfl, totK_node, tot4828, tot4829]
  decide +kernel

theorem arows4822 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4822 = true := by
  rw [show D2M8K2.u4822 = KTree.node D2M8K2.t4830 (nat_lit 10714796) (nat_lit 3791391080) (nat_lit 0) D2M8K2.t4831 from rfl, allE_node, rows4830, irow4822, rows4831]
  all_goals rfl

theorem atot4822 : totK PD2M8K2 D2M8K2.u4822 = [0, 0, 243456143367, 802264094376, 626419075363, 76986367356, 1096505104, 0] := by
  rw [show D2M8K2.u4822 = KTree.node D2M8K2.t4830 (nat_lit 10714796) (nat_lit 3791391080) (nat_lit 0) D2M8K2.t4831 from rfl, totK_node, tot4830, tot4831]
  decide +kernel

theorem arows4827 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4827 = true := by
  rw [show D2M8K2.u4827 = KTree.node D2M8K2.t4832 (nat_lit 10717325) (nat_lit 1839223810) (nat_lit 0) D2M8K2.t4833 from rfl, allE_node, rows4832, irow4827, rows4833]
  all_goals rfl

theorem atot4827 : totK PD2M8K2 D2M8K2.u4827 = [0, 0, 310933171078, 887788320903, 576395078948, 48087211544, 0, 0] := by
  rw [show D2M8K2.u4827 = KTree.node D2M8K2.t4832 (nat_lit 10717325) (nat_lit 1839223810) (nat_lit 0) D2M8K2.t4833 from rfl, totK_node, tot4832, tot4833]
  decide +kernel

theorem arows4828 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4828 = true := by
  rw [show D2M8K2.u4828 = KTree.node D2M8K2.t4834 (nat_lit 10745200) (nat_lit 3707287913) (nat_lit 0) D2M8K2.t4835 from rfl, allE_node, rows4834, irow4828, rows4835]
  all_goals rfl

theorem atot4828 : totK PD2M8K2 D2M8K2.u4828 = [0, 0, 359611160895, 917522960778, 531100057191, 45950520635, 0, 0] := by
  rw [show D2M8K2.u4828 = KTree.node D2M8K2.t4834 (nat_lit 10745200) (nat_lit 3707287913) (nat_lit 0) D2M8K2.t4835 from rfl, totK_node, tot4834, tot4835]
  decide +kernel

theorem arows4830 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4830 = true := by
  rw [show D2M8K2.u4830 = KTree.node D2M8K2.t4836 (nat_lit 10746374) (nat_lit 2610837769) (nat_lit 0) D2M8K2.t4837 from rfl, allE_node, rows4836, irow4830, rows4837]
  all_goals rfl

theorem atot4830 : totK PD2M8K2 D2M8K2.u4830 = [0, 0, 176425804272, 666591753768, 709389518817, 250314514706, 24216995793, 0] := by
  rw [show D2M8K2.u4830 = KTree.node D2M8K2.t4836 (nat_lit 10746374) (nat_lit 2610837769) (nat_lit 0) D2M8K2.t4837 from rfl, totK_node, tot4836, tot4837]
  decide +kernel

theorem arows4831 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4831 = true := by
  rw [show D2M8K2.u4831 = KTree.node D2M8K2.t4838 (nat_lit 10747894) (nat_lit 3521728706) (nat_lit 0) D2M8K2.t4839 from rfl, allE_node, rows4838, irow4831, rows4839]
  all_goals rfl

theorem atot4831 : totK PD2M8K2 D2M8K2.u4831 = [0, 0, 104370356987, 503947760399, 857215049048, 344639618228, 13283011847, 0] := by
  rw [show D2M8K2.u4831 = KTree.node D2M8K2.t4838 (nat_lit 10747894) (nat_lit 3521728706) (nat_lit 0) D2M8K2.t4839 from rfl, totK_node, tot4838, tot4839]
  decide +kernel

theorem arows4834 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4834 = true := by
  rw [show D2M8K2.u4834 = KTree.node D2M8K2.t4840 (nat_lit 10749670) (nat_lit 3841895814) (nat_lit 0) D2M8K2.t4841 from rfl, allE_node, rows4840, irow4834, rows4841]
  all_goals rfl

theorem atot4834 : totK PD2M8K2 D2M8K2.u4834 = [0, 0, 241604462773, 822465235257, 650739451175, 119858297721, 4143089693, 0] := by
  rw [show D2M8K2.u4834 = KTree.node D2M8K2.t4840 (nat_lit 10749670) (nat_lit 3841895814) (nat_lit 0) D2M8K2.t4841 from rfl, totK_node, tot4840, tot4841]
  decide +kernel

theorem arows4835 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4835 = true := by
  rw [show D2M8K2.u4835 = KTree.node D2M8K2.t4842 (nat_lit 10751883) (nat_lit 2013026174) (nat_lit 0) D2M8K2.t4843 from rfl, allE_node, rows4842, irow4835, rows4843]
  all_goals rfl

theorem atot4835 : totK PD2M8K2 D2M8K2.u4835 = [0, 0, 252658311222, 789812336927, 668453798165, 114292118769, 1227322468, 0] := by
  rw [show D2M8K2.u4835 = KTree.node D2M8K2.t4842 (nat_lit 10751883) (nat_lit 2013026174) (nat_lit 0) D2M8K2.t4843 from rfl, totK_node, tot4842, tot4843]
  decide +kernel

theorem arows4837 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4837 = true := by
  rw [show D2M8K2.u4837 = KTree.node D2M8K2.t4844 (nat_lit 10753333) (nat_lit 1294906579) (nat_lit 0) D2M8K2.t4845 from rfl, allE_node, rows4844, irow4837, rows4845]
  all_goals rfl

theorem atot4837 : totK PD2M8K2 D2M8K2.u4837 = [0, 0, 173154768708, 717118236847, 764692851018, 150309697433, 0, 0] := by
  rw [show D2M8K2.u4837 = KTree.node D2M8K2.t4844 (nat_lit 10753333) (nat_lit 1294906579) (nat_lit 0) D2M8K2.t4845 from rfl, totK_node, tot4844, tot4845]
  decide +kernel

theorem arows4838 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4838 = true := by
  rw [show D2M8K2.u4838 = KTree.node D2M8K2.t4846 (nat_lit 10755181) (nat_lit 1130067124) (nat_lit 0) D2M8K2.t4847 from rfl, allE_node, rows4846, irow4838, rows4847]
  all_goals rfl

theorem atot4838 : totK PD2M8K2 D2M8K2.u4838 = [0, 0, 232917690251, 740414413621, 640767693985, 169691155998, 9190730223, 0] := by
  rw [show D2M8K2.u4838 = KTree.node D2M8K2.t4846 (nat_lit 10755181) (nat_lit 1130067124) (nat_lit 0) D2M8K2.t4847 from rfl, totK_node, tot4846, tot4847]
  decide +kernel

theorem arows4842 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4842 = true := by
  rw [show D2M8K2.u4842 = KTree.node D2M8K2.t4848 (nat_lit 10756467) (nat_lit 2994238677) (nat_lit 0) D2M8K2.t4849 from rfl, allE_node, rows4848, irow4842, rows4849]
  all_goals rfl

theorem atot4842 : totK PD2M8K2 D2M8K2.u4842 = [0, 0, 177550997700, 803024183007, 753614245775, 84089077337, 0, 0] := by
  rw [show D2M8K2.u4842 = KTree.node D2M8K2.t4848 (nat_lit 10756467) (nat_lit 2994238677) (nat_lit 0) D2M8K2.t4849 from rfl, totK_node, tot4848, tot4849]
  decide +kernel

theorem arows4843 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4843 = true := by
  rw [show D2M8K2.u4843 = KTree.node D2M8K2.t4850 (nat_lit 10758940) (nat_lit 3879671332) (nat_lit 0) D2M8K2.t4851 from rfl, allE_node, rows4850, irow4843, rows4851]
  all_goals rfl

theorem atot4843 : totK PD2M8K2 D2M8K2.u4843 = [0, 0, 323257504658, 820488765968, 567045483370, 115458504764, 2585032425, 0] := by
  rw [show D2M8K2.u4843 = KTree.node D2M8K2.t4850 (nat_lit 10758940) (nat_lit 3879671332) (nat_lit 0) D2M8K2.t4851 from rfl, totK_node, tot4850, tot4851]
  decide +kernel

theorem arows4845 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4845 = true := by
  rw [show D2M8K2.u4845 = KTree.node D2M8K2.t4852 (nat_lit 10760478) (nat_lit 3923697767) (nat_lit 0) D2M8K2.t4853 from rfl, allE_node, rows4852, irow4845, rows4853]
  all_goals rfl

theorem atot4845 : totK PD2M8K2 D2M8K2.u4845 = [0, 0, 92353366773, 649097987507, 880631483637, 182627845938, 1284661075, 0] := by
  rw [show D2M8K2.u4845 = KTree.node D2M8K2.t4852 (nat_lit 10760478) (nat_lit 3923697767) (nat_lit 0) D2M8K2.t4853 from rfl, totK_node, tot4852, tot4853]
  decide +kernel

theorem arows4846 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4846 = true := by
  rw [show D2M8K2.u4846 = KTree.node D2M8K2.t4854 (nat_lit 10824386) (nat_lit 885719981) (nat_lit 2048) D2M8K2.t4855 from rfl, allE_node, rows4854, irow4846, rows4855]
  all_goals rfl

theorem atot4846 : totK PD2M8K2 D2M8K2.u4846 = [0, 0, 309525436338, 740154998694, 522009534127, 192413832503, 12366239339, 0] := by
  rw [show D2M8K2.u4846 = KTree.node D2M8K2.t4854 (nat_lit 10824386) (nat_lit 885719981) (nat_lit 2048) D2M8K2.t4855 from rfl, totK_node, tot4854, tot4855]
  decide +kernel

theorem arows4849 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4849 = true := by
  rw [show D2M8K2.u4849 = KTree.node D2M8K2.t4856 (nat_lit 10826138) (nat_lit 2731293967) (nat_lit 0) D2M8K2.t4857 from rfl, allE_node, rows4856, irow4849, rows4857]
  all_goals rfl

theorem atot4849 : totK PD2M8K2 D2M8K2.u4849 = [0, 0, 104754912275, 689549747958, 850430579620, 127350770596, 1369150432, 0] := by
  rw [show D2M8K2.u4849 = KTree.node D2M8K2.t4856 (nat_lit 10826138) (nat_lit 2731293967) (nat_lit 0) D2M8K2.t4857 from rfl, totK_node, tot4856, tot4857]
  decide +kernel

theorem arows4850 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4850 = true := by
  rw [show D2M8K2.u4850 = KTree.node D2M8K2.t4858 (nat_lit 10828559) (nat_lit 2143130451) (nat_lit 0) D2M8K2.t4859 from rfl, allE_node, rows4858, irow4850, rows4859]
  all_goals rfl

theorem atot4850 : totK PD2M8K2 D2M8K2.u4850 = [0, 0, 371926535800, 931825948419, 489708845490, 38834220161, 0, 0] := by
  rw [show D2M8K2.u4850 = KTree.node D2M8K2.t4858 (nat_lit 10828559) (nat_lit 2143130451) (nat_lit 0) D2M8K2.t4859 from rfl, totK_node, tot4858, tot4859]
  decide +kernel

theorem arows4852 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4852 = true := by
  rw [show D2M8K2.u4852 = KTree.node D2M8K2.t4860 (nat_lit 10830017) (nat_lit 1808815432) (nat_lit 0) D2M8K2.t4861 from rfl, allE_node, rows4860, irow4852, rows4861]
  all_goals rfl

theorem atot4852 : totK PD2M8K2 D2M8K2.u4852 = [0, 0, 34461480336, 483165302840, 904267328035, 359123288166, 23593757536, 0] := by
  rw [show D2M8K2.u4852 = KTree.node D2M8K2.t4860 (nat_lit 10830017) (nat_lit 1808815432) (nat_lit 0) D2M8K2.t4861 from rfl, totK_node, tot4860, tot4861]
  decide +kernel

theorem arows4853 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4853 = true := by
  rw [show D2M8K2.u4853 = KTree.node D2M8K2.t4862 (nat_lit 10834808) (nat_lit 3831663796) (nat_lit 0) D2M8K2.t4863 from rfl, allE_node, rows4862, irow4853, rows4863]
  all_goals rfl

theorem atot4853 : totK PD2M8K2 D2M8K2.u4853 = [0, 0, 268729134760, 742303704325, 618288558646, 183867830047, 6557415438, 0] := by
  rw [show D2M8K2.u4853 = KTree.node D2M8K2.t4862 (nat_lit 10834808) (nat_lit 3831663796) (nat_lit 0) D2M8K2.t4863 from rfl, totK_node, tot4862, tot4863]
  decide +kernel

theorem arows4861 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4861 = true := by
  rw [show D2M8K2.u4861 = KTree.node D2M8K2.t4864 (nat_lit 10836270) (nat_lit 3844506042) (nat_lit 0) D2M8K2.t4865 from rfl, allE_node, rows4864, irow4861, rows4865]
  all_goals rfl

theorem atot4861 : totK PD2M8K2 D2M8K2.u4861 = [0, 0, 176374678362, 746793071468, 761118657289, 131791326229, 1198073392, 0] := by
  rw [show D2M8K2.u4861 = KTree.node D2M8K2.t4864 (nat_lit 10836270) (nat_lit 3844506042) (nat_lit 0) D2M8K2.t4865 from rfl, totK_node, tot4864, tot4865]
  decide +kernel

theorem arows4862 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4862 = true := by
  rw [show D2M8K2.u4862 = KTree.node D2M8K2.t4866 (nat_lit 10838074) (nat_lit 1036615435) (nat_lit 2176) D2M8K2.t4867 from rfl, allE_node, rows4866, irow4862, rows4867]
  all_goals rfl

theorem atot4862 : totK PD2M8K2 D2M8K2.u4862 = [0, 0, 210654284092, 658535984855, 673007734612, 211513919485, 12052611869, 0] := by
  rw [show D2M8K2.u4862 = KTree.node D2M8K2.t4866 (nat_lit 10838074) (nat_lit 1036615435) (nat_lit 2176) D2M8K2.t4867 from rfl, totK_node, tot4866, tot4867]
  decide +kernel

theorem arows4864 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4864 = true := by
  rw [show D2M8K2.u4864 = KTree.node D2M8K2.t4868 (nat_lit 10839319) (nat_lit 2224320227) (nat_lit 0) D2M8K2.t4869 from rfl, allE_node, rows4868, irow4864, rows4869]
  all_goals rfl

theorem atot4864 : totK PD2M8K2 D2M8K2.u4864 = [0, 0, 202177483556, 790548418409, 688985895692, 93110189863, 1096505104, 0] := by
  rw [show D2M8K2.u4864 = KTree.node D2M8K2.t4868 (nat_lit 10839319) (nat_lit 2224320227) (nat_lit 0) D2M8K2.t4869 from rfl, totK_node, tot4868, tot4869]
  decide +kernel

theorem arows4865 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4865 = true := by
  rw [show D2M8K2.u4865 = KTree.node D2M8K2.t4870 (nat_lit 10841617) (nat_lit 1561463014) (nat_lit 0) D2M8K2.t4871 from rfl, allE_node, rows4870, irow4865, rows4871]
  all_goals rfl

theorem atot4865 : totK PD2M8K2 D2M8K2.u4865 = [0, 0, 235821049377, 762538089403, 668994954300, 127769830995, 3884009855, 0] := by
  rw [show D2M8K2.u4865 = KTree.node D2M8K2.t4870 (nat_lit 10841617) (nat_lit 1561463014) (nat_lit 0) D2M8K2.t4871 from rfl, totK_node, tot4870, tot4871]
  decide +kernel

theorem arows4868 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4868 = true := by
  rw [show D2M8K2.u4868 = KTree.node D2M8K2.t4872 (nat_lit 10843179) (nat_lit 3491308454) (nat_lit 0) D2M8K2.t4873 from rfl, allE_node, rows4872, irow4868, rows4873]
  all_goals rfl

theorem atot4868 : totK PD2M8K2 D2M8K2.u4868 = [0, 0, 182137505762, 720729084600, 760157800275, 138977398237, 1268739303, 0] := by
  rw [show D2M8K2.u4868 = KTree.node D2M8K2.t4872 (nat_lit 10843179) (nat_lit 3491308454) (nat_lit 0) D2M8K2.t4873 from rfl, totK_node, tot4872, tot4873]
  decide +kernel

theorem arows4869 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4869 = true := by
  rw [show D2M8K2.u4869 = KTree.node D2M8K2.t4874 (nat_lit 10844933) (nat_lit 2306909143) (nat_lit 0) D2M8K2.t4875 from rfl, allE_node, rows4874, irow4869, rows4875]
  all_goals rfl

theorem atot4869 : totK PD2M8K2 D2M8K2.u4869 = [0, 0, 0, 405134080597, 953580277423, 381584063021, 17403805274, 0] := by
  rw [show D2M8K2.u4869 = KTree.node D2M8K2.t4874 (nat_lit 10844933) (nat_lit 2306909143) (nat_lit 0) D2M8K2.t4875 from rfl, totK_node, tot4874, tot4875]
  decide +kernel

theorem arows4871 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4871 = true := by
  rw [show D2M8K2.u4871 = KTree.node D2M8K2.t4876 (nat_lit 10848756) (nat_lit 2649545256) (nat_lit 0) D2M8K2.t4877 from rfl, allE_node, rows4876, irow4871, rows4877]
  all_goals rfl

theorem atot4871 : totK PD2M8K2 D2M8K2.u4871 = [0, 0, 0, 414694407069, 948405192364, 399543579348, 24485998251, 0] := by
  rw [show D2M8K2.u4871 = KTree.node D2M8K2.t4876 (nat_lit 10848756) (nat_lit 2649545256) (nat_lit 0) D2M8K2.t4877 from rfl, totK_node, tot4876, tot4877]
  decide +kernel

theorem arows4872 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4872 = true := by
  rw [show D2M8K2.u4872 = KTree.node D2M8K2.t4878 (nat_lit 10855370) (nat_lit 3420423975) (nat_lit 0) D2M8K2.t4879 from rfl, allE_node, rows4878, irow4872, rows4879]
  all_goals rfl

theorem atot4872 : totK PD2M8K2 D2M8K2.u4872 = [0, 0, 0, 399714618555, 960799229012, 412359064088, 25095106481, 0] := by
  rw [show D2M8K2.u4872 = KTree.node D2M8K2.t4878 (nat_lit 10855370) (nat_lit 3420423975) (nat_lit 0) D2M8K2.t4879 from rfl, totK_node, tot4878, tot4879]
  decide +kernel

theorem arows4876 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4876 = true := by
  rw [show D2M8K2.u4876 = KTree.node D2M8K2.t4880 (nat_lit 10856859) (nat_lit 3642326178) (nat_lit 0) D2M8K2.t4881 from rfl, allE_node, rows4880, irow4876, rows4881]
  all_goals rfl

theorem atot4876 : totK PD2M8K2 D2M8K2.u4876 = [0, 0, 0, 206794934204, 845096674028, 672217522098, 67492283397, 0] := by
  rw [show D2M8K2.u4876 = KTree.node D2M8K2.t4880 (nat_lit 10856859) (nat_lit 3642326178) (nat_lit 0) D2M8K2.t4881 from rfl, totK_node, tot4880, tot4881]
  decide +kernel

theorem arows4877 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4877 = true := by
  rw [show D2M8K2.u4877 = KTree.node D2M8K2.t4882 (nat_lit 10858850) (nat_lit 3266617108) (nat_lit 0) D2M8K2.t4883 from rfl, allE_node, rows4882, irow4877, rows4883]
  all_goals rfl

theorem atot4877 : totK PD2M8K2 D2M8K2.u4877 = [0, 0, 0, 228867978369, 729344743378, 597804525429, 156984974356, 5757108999] := by
  rw [show D2M8K2.u4877 = KTree.node D2M8K2.t4882 (nat_lit 10858850) (nat_lit 3266617108) (nat_lit 0) D2M8K2.t4883 from rfl, totK_node, tot4882, tot4883]
  decide +kernel

theorem arows4879 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4879 = true := by
  rw [show D2M8K2.u4879 = KTree.node D2M8K2.t4884 (nat_lit 10860487) (nat_lit 2343389743) (nat_lit 0) D2M8K2.t4885 from rfl, allE_node, rows4884, irow4879, rows4885]
  all_goals rfl

theorem atot4879 : totK PD2M8K2 D2M8K2.u4879 = [0, 0, 0, 178718781984, 839936364946, 661610910802, 62317266797, 0] := by
  rw [show D2M8K2.u4879 = KTree.node D2M8K2.t4884 (nat_lit 10860487) (nat_lit 2343389743) (nat_lit 0) D2M8K2.t4885 from rfl, totK_node, tot4884, tot4885]
  decide +kernel

theorem arows4880 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4880 = true := by
  rw [show D2M8K2.u4880 = KTree.node D2M8K2.t4886 (nat_lit 10862764) (nat_lit 3507352931) (nat_lit 0) D2M8K2.t4887 from rfl, allE_node, rows4886, irow4880, rows4887]
  all_goals rfl

theorem atot4880 : totK PD2M8K2 D2M8K2.u4880 = [0, 0, 0, 412480296070, 879345746400, 422383523029, 60824067490, 1348424121] := by
  rw [show D2M8K2.u4880 = KTree.node D2M8K2.t4886 (nat_lit 10862764) (nat_lit 3507352931) (nat_lit 0) D2M8K2.t4887 from rfl, totK_node, tot4886, tot4887]
  decide +kernel

theorem arows4883 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4883 = true := by
  rw [show D2M8K2.u4883 = KTree.node D2M8K2.t4888 (nat_lit 10866529) (nat_lit 1561875799) (nat_lit 0) D2M8K2.t4889 from rfl, allE_node, rows4888, irow4883, rows4889]
  all_goals rfl

theorem atot4883 : totK PD2M8K2 D2M8K2.u4883 = [0, 0, 353229126299, 851169314200, 449112072966, 106650844361, 9043051330, 0] := by
  rw [show D2M8K2.u4883 = KTree.node D2M8K2.t4888 (nat_lit 10866529) (nat_lit 1561875799) (nat_lit 0) D2M8K2.t4889 from rfl, totK_node, tot4888, tot4889]
  decide +kernel

theorem arows4884 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4884 = true := by
  rw [show D2M8K2.u4884 = KTree.node D2M8K2.t4890 (nat_lit 10868398) (nat_lit 3736437463) (nat_lit 0) D2M8K2.t4891 from rfl, allE_node, rows4890, irow4884, rows4891]
  all_goals rfl

theorem atot4884 : totK PD2M8K2 D2M8K2.u4884 = [0, 0, 139540226035, 709148820579, 824772132210, 126161162299, 1310517177, 0] := by
  rw [show D2M8K2.u4884 = KTree.node D2M8K2.t4890 (nat_lit 10868398) (nat_lit 3736437463) (nat_lit 0) D2M8K2.t4891 from rfl, totK_node, tot4890, tot4891]
  decide +kernel

theorem arows4886 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4886 = true := by
  rw [show D2M8K2.u4886 = KTree.node D2M8K2.t4892 (nat_lit 10870345) (nat_lit 1373015777) (nat_lit 0) D2M8K2.t4893 from rfl, allE_node, rows4892, irow4886, rows4893]
  all_goals rfl

theorem atot4886 : totK PD2M8K2 D2M8K2.u4886 = [0, 0, 297683051409, 897809721390, 576054393031, 62633571026, 0, 0] := by
  rw [show D2M8K2.u4886 = KTree.node D2M8K2.t4892 (nat_lit 10870345) (nat_lit 1373015777) (nat_lit 0) D2M8K2.t4893 from rfl, totK_node, tot4892, tot4893]
  decide +kernel

theorem arows4887 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4887 = true := by
  rw [show D2M8K2.u4887 = KTree.node D2M8K2.t4894 (nat_lit 10872051) (nat_lit 3650203772) (nat_lit 0) D2M8K2.t4895 from rfl, allE_node, rows4894, irow4887, rows4895]
  all_goals rfl

theorem atot4887 : totK PD2M8K2 D2M8K2.u4887 = [0, 0, 107297381188, 549497856224, 826123372092, 311679609847, 15066332673, 0] := by
  rw [show D2M8K2.u4887 = KTree.node D2M8K2.t4894 (nat_lit 10872051) (nat_lit 3650203772) (nat_lit 0) D2M8K2.t4895 from rfl, totK_node, tot4894, tot4895]
  decide +kernel

theorem arows4892 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4892 = true := by
  rw [show D2M8K2.u4892 = KTree.node D2M8K2.t4896 (nat_lit 10873801) (nat_lit 1431987931) (nat_lit 0) D2M8K2.t4897 from rfl, allE_node, rows4896, irow4892, rows4897]
  all_goals rfl

theorem atot4892 : totK PD2M8K2 D2M8K2.u4892 = [0, 0, 218682374303, 845927663314, 694929316339, 66432859745, 0, 0] := by
  rw [show D2M8K2.u4892 = KTree.node D2M8K2.t4896 (nat_lit 10873801) (nat_lit 1431987931) (nat_lit 0) D2M8K2.t4897 from rfl, totK_node, tot4896, tot4897]
  decide +kernel

theorem arows4893 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4893 = true := by
  rw [show D2M8K2.u4893 = KTree.node D2M8K2.t4898 (nat_lit 10876425) (nat_lit 1895681444) (nat_lit 0) D2M8K2.t4899 from rfl, allE_node, rows4898, irow4893, rows4899]
  all_goals rfl

theorem atot4893 : totK PD2M8K2 D2M8K2.u4893 = [0, 0, 312728727739, 821436591905, 575466384555, 92549394741, 1288481286, 0] := by
  rw [show D2M8K2.u4893 = KTree.node D2M8K2.t4898 (nat_lit 10876425) (nat_lit 1895681444) (nat_lit 0) D2M8K2.t4899 from rfl, totK_node, tot4898, tot4899]
  decide +kernel

theorem arows4895 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4895 = true := by
  rw [show D2M8K2.u4895 = KTree.node D2M8K2.t4900 (nat_lit 10877917) (nat_lit 1198073392) (nat_lit 0) D2M8K2.t4901 from rfl, allE_node, rows4900, irow4895, rows4901]
  all_goals rfl

theorem atot4895 : totK PD2M8K2 D2M8K2.u4895 = [0, 0, 108879669206, 632204682674, 811776952412, 217288921074, 9668735432, 0] := by
  rw [show D2M8K2.u4895 = KTree.node D2M8K2.t4900 (nat_lit 10877917) (nat_lit 1198073392) (nat_lit 0) D2M8K2.t4901 from rfl, totK_node, tot4900, tot4901]
  decide +kernel

theorem arows4896 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4896 = true := by
  rw [show D2M8K2.u4896 = KTree.node D2M8K2.t4902 (nat_lit 10879810) (nat_lit 3838885934) (nat_lit 0) D2M8K2.t4903 from rfl, allE_node, rows4902, irow4896, rows4903]
  all_goals rfl

theorem atot4896 : totK PD2M8K2 D2M8K2.u4896 = [0, 0, 267506480668, 768491672438, 612887396838, 123391061892, 3581949829, 0] := by
  rw [show D2M8K2.u4896 = KTree.node D2M8K2.t4902 (nat_lit 10879810) (nat_lit 3838885934) (nat_lit 0) D2M8K2.t4903 from rfl, totK_node, tot4902, tot4903]
  decide +kernel

theorem arows4899 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4899 = true := by
  rw [show D2M8K2.u4899 = KTree.node D2M8K2.t4904 (nat_lit 10881272) (nat_lit 3682233856) (nat_lit 0) D2M8K2.t4905 from rfl, allE_node, rows4904, irow4899, rows4905]
  all_goals rfl

theorem atot4899 : totK PD2M8K2 D2M8K2.u4899 = [0, 0, 167115188431, 762031717299, 768284243175, 115390564925, 1096505104, 0] := by
  rw [show D2M8K2.u4899 = KTree.node D2M8K2.t4904 (nat_lit 10881272) (nat_lit 3682233856) (nat_lit 0) D2M8K2.t4905 from rfl, totK_node, tot4904, tot4905]
  decide +kernel

theorem arows4900 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4900 = true := by
  rw [show D2M8K2.u4900 = KTree.node D2M8K2.t4906 (nat_lit 10886982) (nat_lit 2871084410) (nat_lit 0) D2M8K2.t4907 from rfl, allE_node, rows4906, irow4900, rows4907]
  all_goals rfl

theorem atot4900 : totK PD2M8K2 D2M8K2.u4900 = [0, 0, 0, 438672550462, 968452612524, 332773940232, 9724046876, 0] := by
  rw [show D2M8K2.u4900 = KTree.node D2M8K2.t4906 (nat_lit 10886982) (nat_lit 2871084410) (nat_lit 0) D2M8K2.t4907 from rfl, totK_node, tot4906, tot4907]
  decide +kernel

theorem arows4902 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4902 = true := by
  rw [show D2M8K2.u4902 = KTree.node D2M8K2.t4908 (nat_lit 10890802) (nat_lit 3862193498) (nat_lit 0) D2M8K2.t4909 from rfl, allE_node, rows4908, irow4902, rows4909]
  all_goals rfl

theorem atot4902 : totK PD2M8K2 D2M8K2.u4902 = [0, 0, 0, 484709149686, 949607249398, 369408121693, 17746706651, 0] := by
  rw [show D2M8K2.u4902 = KTree.node D2M8K2.t4908 (nat_lit 10890802) (nat_lit 3862193498) (nat_lit 0) D2M8K2.t4909 from rfl, totK_node, tot4908, tot4909]
  decide +kernel

theorem arows4903 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4903 = true := by
  rw [show D2M8K2.u4903 = KTree.node D2M8K2.t4910 (nat_lit 10894576) (nat_lit 3431384913) (nat_lit 0) D2M8K2.t4911 from rfl, allE_node, rows4910, irow4903, rows4911]
  all_goals rfl

theorem atot4903 : totK PD2M8K2 D2M8K2.u4903 = [0, 0, 0, 468281934789, 971716087590, 314383287559, 12241177687, 0] := by
  rw [show D2M8K2.u4903 = KTree.node D2M8K2.t4910 (nat_lit 10894576) (nat_lit 3431384913) (nat_lit 0) D2M8K2.t4911 from rfl, totK_node, tot4910, tot4911]
  decide +kernel

theorem arows4907 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4907 = true := by
  rw [show D2M8K2.u4907 = KTree.node D2M8K2.t4912 (nat_lit 10898208) (nat_lit 3667768859) (nat_lit 0) D2M8K2.t4913 from rfl, allE_node, rows4912, irow4907, rows4913]
  all_goals rfl

theorem atot4907 : totK PD2M8K2 D2M8K2.u4907 = [0, 0, 0, 405716175503, 958603538927, 387367395402, 16412058820, 0] := by
  rw [show D2M8K2.u4907 = KTree.node D2M8K2.t4912 (nat_lit 10898208) (nat_lit 3667768859) (nat_lit 0) D2M8K2.t4913 from rfl, totK_node, tot4912, tot4913]
  decide +kernel

theorem arows4908 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4908 = true := by
  rw [show D2M8K2.u4908 = KTree.node D2M8K2.t4914 (nat_lit 10901313) (nat_lit 1782433198) (nat_lit 0) D2M8K2.t4915 from rfl, allE_node, rows4914, irow4908, rows4915]
  all_goals rfl

theorem atot4908 : totK PD2M8K2 D2M8K2.u4908 = [0, 0, 0, 266749256576, 907783044020, 536250954779, 41913554019, 0] := by
  rw [show D2M8K2.u4908 = KTree.node D2M8K2.t4914 (nat_lit 10901313) (nat_lit 1782433198) (nat_lit 0) D2M8K2.t4915 from rfl, totK_node, tot4914, tot4915]
  decide +kernel

theorem arows4910 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4910 = true := by
  rw [show D2M8K2.u4910 = KTree.node D2M8K2.t4916 (nat_lit 10907246) (nat_lit 860520552) (nat_lit 128) D2M8K2.t4917 from rfl, allE_node, rows4916, irow4910, rows4917]
  all_goals rfl

theorem atot4910 : totK PD2M8K2 D2M8K2.u4910 = [0, 0, 289355704546, 579446868314, 438739893460, 377712586373, 76525408679, 1430229726] := by
  rw [show D2M8K2.u4910 = KTree.node D2M8K2.t4916 (nat_lit 10907246) (nat_lit 860520552) (nat_lit 128) D2M8K2.t4917 from rfl, totK_node, tot4916, tot4917]
  decide +kernel

theorem arows4911 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4911 = true := by
  rw [show D2M8K2.u4911 = KTree.node D2M8K2.t4918 (nat_lit 10909469) (nat_lit 1969968198) (nat_lit 0) D2M8K2.t4919 from rfl, allE_node, rows4918, irow4911, rows4919]
  all_goals rfl

theorem atot4911 : totK PD2M8K2 D2M8K2.u4911 = [0, 0, 164880150593, 730107834001, 784700124178, 121692314835, 1369150432, 0] := by
  rw [show D2M8K2.u4911 = KTree.node D2M8K2.t4918 (nat_lit 10909469) (nat_lit 1969968198) (nat_lit 0) D2M8K2.t4919 from rfl, totK_node, tot4918, tot4919]
  decide +kernel

theorem arows4914 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4914 = true := by
  rw [show D2M8K2.u4914 = KTree.node D2M8K2.t4920 (nat_lit 10911590) (nat_lit 3992174847) (nat_lit 0) D2M8K2.t4921 from rfl, allE_node, rows4920, irow4914, rows4921]
  all_goals rfl

theorem atot4914 : totK PD2M8K2 D2M8K2.u4914 = [0, 0, 339326678219, 937239408860, 533251549277, 40844851467, 0, 0] := by
  rw [show D2M8K2.u4914 = KTree.node D2M8K2.t4920 (nat_lit 10911590) (nat_lit 3992174847) (nat_lit 0) D2M8K2.t4921 from rfl, totK_node, tot4920, tot4921]
  decide +kernel

theorem arows4915 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4915 = true := by
  rw [show D2M8K2.u4915 = KTree.node D2M8K2.t4922 (nat_lit 10913143) (nat_lit 966151424) (nat_lit 0) D2M8K2.t4923 from rfl, allE_node, rows4922, irow4915, rows4923]
  all_goals rfl

theorem atot4915 : totK PD2M8K2 D2M8K2.u4915 = [0, 0, 0, 404632270996, 954768174133, 419754756624, 26020096574, 0] := by
  rw [show D2M8K2.u4915 = KTree.node D2M8K2.t4922 (nat_lit 10913143) (nat_lit 966151424) (nat_lit 0) D2M8K2.t4923 from rfl, totK_node, tot4922, tot4923]
  decide +kernel

theorem arows4917 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4917 = true := by
  rw [show D2M8K2.u4917 = KTree.node D2M8K2.t4924 (nat_lit 10914619) (nat_lit 1131961140) (nat_lit 0) D2M8K2.t4925 from rfl, allE_node, rows4924, irow4917, rows4925]
  all_goals rfl

theorem atot4917 : totK PD2M8K2 D2M8K2.u4917 = [0, 0, 328582183324, 814478577634, 562630259611, 136707770101, 6784511402, 0] := by
  rw [show D2M8K2.u4917 = KTree.node D2M8K2.t4924 (nat_lit 10914619) (nat_lit 1131961140) (nat_lit 0) D2M8K2.t4925 from rfl, totK_node, tot4924, tot4925]
  decide +kernel

theorem arows4918 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4918 = true := by
  rw [show D2M8K2.u4918 = KTree.node D2M8K2.t4926 (nat_lit 10917352) (nat_lit 3762376533) (nat_lit 0) D2M8K2.t4927 from rfl, allE_node, rows4926, irow4918, rows4927]
  all_goals rfl

theorem atot4918 : totK PD2M8K2 D2M8K2.u4918 = [0, 0, 187681199742, 753933708340, 753433247070, 136118948522, 1501162176, 0] := by
  rw [show D2M8K2.u4918 = KTree.node D2M8K2.t4926 (nat_lit 10917352) (nat_lit 3762376533) (nat_lit 0) D2M8K2.t4927 from rfl, totK_node, tot4926, tot4927]
  decide +kernel

theorem arows4924 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4924 = true := by
  rw [show D2M8K2.u4924 = KTree.node D2M8K2.t4928 (nat_lit 10919016) (nat_lit 3534038886) (nat_lit 0) D2M8K2.t4929 from rfl, allE_node, rows4928, irow4924, rows4929]
  all_goals rfl

theorem atot4924 : totK PD2M8K2 D2M8K2.u4924 = [0, 0, 234684918082, 800114766853, 667972675395, 104750020202, 1198073392, 0] := by
  rw [show D2M8K2.u4924 = KTree.node D2M8K2.t4928 (nat_lit 10919016) (nat_lit 3534038886) (nat_lit 0) D2M8K2.t4929 from rfl, totK_node, tot4928, tot4929]
  decide +kernel

theorem arows4925 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4925 = true := by
  rw [show D2M8K2.u4925 = KTree.node D2M8K2.t4930 (nat_lit 10920734) (nat_lit 3752357851) (nat_lit 0) D2M8K2.t4931 from rfl, allE_node, rows4930, irow4925, rows4931]
  all_goals rfl

theorem atot4925 : totK PD2M8K2 D2M8K2.u4925 = [0, 0, 172430498672, 668309668533, 741483172296, 215662245452, 8376437251, 0] := by
  rw [show D2M8K2.u4925 = KTree.node D2M8K2.t4930 (nat_lit 10920734) (nat_lit 3752357851) (nat_lit 0) D2M8K2.t4931 from rfl, totK_node, tot4930, tot4931]
  decide +kernel

theorem arows4927 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4927 = true := by
  rw [show D2M8K2.u4927 = KTree.node D2M8K2.t4932 (nat_lit 10925856) (nat_lit 3708958841) (nat_lit 0) D2M8K2.t4933 from rfl, allE_node, rows4932, irow4927, rows4933]
  all_goals rfl

theorem atot4927 : totK PD2M8K2 D2M8K2.u4927 = [0, 0, 264794537936, 801448106413, 642626521374, 107809955512, 1268739303, 0] := by
  rw [show D2M8K2.u4927 = KTree.node D2M8K2.t4932 (nat_lit 10925856) (nat_lit 3708958841) (nat_lit 0) D2M8K2.t4933 from rfl, totK_node, tot4932, tot4933]
  decide +kernel

theorem arows4928 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4928 = true := by
  rw [show D2M8K2.u4928 = KTree.node D2M8K2.t4934 (nat_lit 10927246) (nat_lit 2960917829) (nat_lit 0) D2M8K2.t4935 from rfl, allE_node, rows4934, irow4928, rows4935]
  all_goals rfl

theorem atot4928 : totK PD2M8K2 D2M8K2.u4928 = [0, 91454885225, 217174660516, 405935492821, 758739249119, 301771945549, 17009521594, 0] := by
  rw [show D2M8K2.u4928 = KTree.node D2M8K2.t4934 (nat_lit 10927246) (nat_lit 2960917829) (nat_lit 0) D2M8K2.t4935 from rfl, totK_node, tot4934, tot4935]
  decide +kernel

theorem arows4931 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4931 = true := by
  rw [show D2M8K2.u4931 = KTree.node D2M8K2.t4936 (nat_lit 10949766) (nat_lit 3743316732) (nat_lit 0) D2M8K2.t4937 from rfl, allE_node, rows4936, irow4931, rows4937]
  all_goals rfl

theorem atot4931 : totK PD2M8K2 D2M8K2.u4931 = [0, 330107378720, 900436136173, 515589317301, 40794606127, 0, 0, 0] := by
  rw [show D2M8K2.u4931 = KTree.node D2M8K2.t4936 (nat_lit 10949766) (nat_lit 3743316732) (nat_lit 0) D2M8K2.t4937 from rfl, totK_node, tot4936, tot4937]
  decide +kernel

theorem arows4932 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4932 = true := by
  rw [show D2M8K2.u4932 = KTree.node D2M8K2.t4938 (nat_lit 10951569) (nat_lit 1855832370) (nat_lit 0) D2M8K2.t4939 from rfl, allE_node, rows4938, irow4932, rows4939]
  all_goals rfl

theorem atot4932 : totK PD2M8K2 D2M8K2.u4932 = [0, 154546952829, 716367644613, 792893797681, 139094675233, 1369150432, 0, 0] := by
  rw [show D2M8K2.u4932 = KTree.node D2M8K2.t4938 (nat_lit 10951569) (nat_lit 1855832370) (nat_lit 0) D2M8K2.t4939 from rfl, totK_node, tot4938, tot4939]
  decide +kernel

theorem arows4934 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4934 = true := by
  rw [show D2M8K2.u4934 = KTree.node D2M8K2.t4940 (nat_lit 10956849) (nat_lit 1606484339) (nat_lit 0) D2M8K2.t4941 from rfl, allE_node, rows4940, irow4934, rows4941]
  all_goals rfl

theorem atot4934 : totK PD2M8K2 D2M8K2.u4934 = [0, 245458425826, 794260932837, 649610623852, 99092875787, 1164319620, 0, 0] := by
  rw [show D2M8K2.u4934 = KTree.node D2M8K2.t4940 (nat_lit 10956849) (nat_lit 1606484339) (nat_lit 0) D2M8K2.t4941 from rfl, totK_node, tot4940, tot4941]
  decide +kernel

theorem arows4935 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4935 = true := by
  rw [show D2M8K2.u4935 = KTree.node D2M8K2.t4942 (nat_lit 10958645) (nat_lit 2201255366) (nat_lit 0) D2M8K2.t4943 from rfl, allE_node, rows4942, irow4935, rows4943]
  all_goals rfl

theorem atot4935 : totK PD2M8K2 D2M8K2.u4935 = [0, 154627715334, 639753774915, 770056892795, 208277377323, 11885407614, 0, 0] := by
  rw [show D2M8K2.u4935 = KTree.node D2M8K2.t4942 (nat_lit 10958645) (nat_lit 2201255366) (nat_lit 0) D2M8K2.t4943 from rfl, totK_node, tot4942, tot4943]
  decide +kernel

theorem arows4939 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4939 = true := by
  rw [show D2M8K2.u4939 = KTree.node D2M8K2.t4944 (nat_lit 10960355) (nat_lit 1633371839) (nat_lit 0) D2M8K2.t4945 from rfl, allE_node, rows4944, irow4939, rows4945]
  all_goals rfl

theorem atot4939 : totK PD2M8K2 D2M8K2.u4939 = [0, 245613408280, 798881803216, 653589381866, 99108513534, 1198073392, 0, 0] := by
  rw [show D2M8K2.u4939 = KTree.node D2M8K2.t4944 (nat_lit 10960355) (nat_lit 1633371839) (nat_lit 0) D2M8K2.t4945 from rfl, totK_node, tot4944, tot4945]
  decide +kernel

theorem arows4940 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4940 = true := by
  rw [show D2M8K2.u4940 = KTree.node D2M8K2.t4946 (nat_lit 10962152) (nat_lit 2442289437) (nat_lit 0) D2M8K2.t4947 from rfl, allE_node, rows4946, irow4940, rows4947]
  all_goals rfl

theorem atot4940 : totK PD2M8K2 D2M8K2.u4940 = [0, 159457644122, 646778733250, 762949761116, 210221397759, 12052611869, 0, 0] := by
  rw [show D2M8K2.u4940 = KTree.node D2M8K2.t4946 (nat_lit 10962152) (nat_lit 2442289437) (nat_lit 0) D2M8K2.t4947 from rfl, totK_node, tot4946, tot4947]
  decide +kernel

theorem arows4942 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4942 = true := by
  rw [show D2M8K2.u4942 = KTree.node D2M8K2.t4948 (nat_lit 10963560) (nat_lit 3336500029) (nat_lit 0) D2M8K2.t4949 from rfl, allE_node, rows4948, irow4942, rows4949]
  all_goals rfl

theorem atot4942 : totK PD2M8K2 D2M8K2.u4942 = [0, 263060155692, 810519273852, 626561924142, 87595957778, 1096505104, 0, 0] := by
  rw [show D2M8K2.u4942 = KTree.node D2M8K2.t4948 (nat_lit 10963560) (nat_lit 3336500029) (nat_lit 0) D2M8K2.t4949 from rfl, totK_node, tot4948, tot4949]
  decide +kernel

theorem arows4943 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4943 = true := by
  rw [show D2M8K2.u4943 = KTree.node D2M8K2.t4950 (nat_lit 10965509) (nat_lit 2207344610) (nat_lit 0) D2M8K2.t4951 from rfl, allE_node, rows4950, irow4943, rows4951]
  all_goals rfl

theorem atot4943 : totK PD2M8K2 D2M8K2.u4943 = [0, 0, 471605748283, 984382129766, 310548143888, 13494923418, 0, 0] := by
  rw [show D2M8K2.u4943 = KTree.node D2M8K2.t4950 (nat_lit 10965509) (nat_lit 2207344610) (nat_lit 0) D2M8K2.t4951 from rfl, totK_node, tot4950, tot4951]
  decide +kernel

theorem arows4946 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4946 = true := by
  rw [show D2M8K2.u4946 = KTree.node D2M8K2.t4952 (nat_lit 10970806) (nat_lit 3576224356) (nat_lit 0) D2M8K2.t4953 from rfl, allE_node, rows4952, irow4946, rows4953]
  all_goals rfl

theorem atot4946 : totK PD2M8K2 D2M8K2.u4946 = [0, 0, 243770625891, 822427165855, 589897659495, 79228689908, 1369150432, 0] := by
  rw [show D2M8K2.u4946 = KTree.node D2M8K2.t4952 (nat_lit 10970806) (nat_lit 3576224356) (nat_lit 0) D2M8K2.t4953 from rfl, totK_node, tot4952, tot4953]
  decide +kernel

theorem arows4947 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4947 = true := by
  rw [show D2M8K2.u4947 = KTree.node D2M8K2.t4954 (nat_lit 10976588) (nat_lit 3684046867) (nat_lit 0) D2M8K2.t4955 from rfl, allE_node, rows4954, irow4947, rows4955]
  all_goals rfl

theorem atot4947 : totK PD2M8K2 D2M8K2.u4947 = [0, 0, 304706406284, 915793843754, 511442135769, 36274795692, 0, 0] := by
  rw [show D2M8K2.u4947 = KTree.node D2M8K2.t4954 (nat_lit 10976588) (nat_lit 3684046867) (nat_lit 0) D2M8K2.t4955 from rfl, totK_node, tot4954, tot4955]
  decide +kernel

theorem arows4949 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4949 = true := by
  rw [show D2M8K2.u4949 = KTree.node D2M8K2.t4956 (nat_lit 10979937) (nat_lit 1740740290) (nat_lit 0) D2M8K2.t4957 from rfl, allE_node, rows4956, irow4949, rows4957]
  all_goals rfl

theorem atot4949 : totK PD2M8K2 D2M8K2.u4949 = [0, 0, 364168392421, 961351563364, 440990502464, 21678882268, 0, 0] := by
  rw [show D2M8K2.u4949 = KTree.node D2M8K2.t4956 (nat_lit 10979937) (nat_lit 1740740290) (nat_lit 0) D2M8K2.t4957 from rfl, totK_node, tot4956, tot4957]
  decide +kernel

theorem arows4950 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4950 = true := by
  rw [show D2M8K2.u4950 = KTree.node D2M8K2.t4958 (nat_lit 10983299) (nat_lit 1342911193) (nat_lit 2208) D2M8K2.t4959 from rfl, allE_node, rows4958, irow4950, rows4959]
  all_goals rfl

theorem atot4950 : totK PD2M8K2 D2M8K2.u4950 = [0, 0, 374342419285, 967711171030, 414135023021, 16312195497, 0, 0] := by
  rw [show D2M8K2.u4950 = KTree.node D2M8K2.t4958 (nat_lit 10983299) (nat_lit 1342911193) (nat_lit 2208) D2M8K2.t4959 from rfl, totK_node, tot4958, tot4959]
  decide +kernel

theorem arows4955 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4955 = true := by
  rw [show D2M8K2.u4955 = KTree.node D2M8K2.t4960 (nat_lit 10993851) (nat_lit 3792201853) (nat_lit 0) D2M8K2.t4961 from rfl, allE_node, rows4960, irow4955, rows4961]
  all_goals rfl

theorem atot4955 : totK PD2M8K2 D2M8K2.u4955 = [0, 182516275838, 628821256615, 735695398135, 252732292477, 13874764603, 0, 0] := by
  rw [show D2M8K2.u4955 = KTree.node D2M8K2.t4960 (nat_lit 10993851) (nat_lit 3792201853) (nat_lit 0) D2M8K2.t4961 from rfl, totK_node, tot4960, tot4961]
  decide +kernel

theorem arows4956 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4956 = true := by
  rw [show D2M8K2.u4956 = KTree.node D2M8K2.t4962 (nat_lit 10994994) (nat_lit 3177022111) (nat_lit 0) D2M8K2.t4963 from rfl, allE_node, rows4962, irow4956, rows4963]
  all_goals rfl

theorem atot4956 : totK PD2M8K2 D2M8K2.u4956 = [0, 262384214721, 785764230157, 605787875383, 174870664521, 17186218589, 0, 0] := by
  rw [show D2M8K2.u4956 = KTree.node D2M8K2.t4962 (nat_lit 10994994) (nat_lit 3177022111) (nat_lit 0) D2M8K2.t4963 from rfl, totK_node, tot4962, tot4963]
  decide +kernel

theorem arows4958 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4958 = true := by
  rw [show D2M8K2.u4958 = KTree.node D2M8K2.t4964 (nat_lit 10996450) (nat_lit 3471276410) (nat_lit 0) D2M8K2.t4965 from rfl, allE_node, rows4964, irow4958, rows4965]
  all_goals rfl

theorem atot4958 : totK PD2M8K2 D2M8K2.u4958 = [0, 57711587728, 432979394002, 890664573052, 408461378685, 20423179516, 0, 0] := by
  rw [show D2M8K2.u4958 = KTree.node D2M8K2.t4964 (nat_lit 10996450) (nat_lit 3471276410) (nat_lit 0) D2M8K2.t4965 from rfl, totK_node, tot4964, tot4965]
  decide +kernel

theorem arows4959 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4959 = true := by
  rw [show D2M8K2.u4959 = KTree.node D2M8K2.t4966 (nat_lit 10997717) (nat_lit 2307134053) (nat_lit 0) D2M8K2.t4967 from rfl, allE_node, rows4966, irow4959, rows4967]
  all_goals rfl

theorem atot4959 : totK PD2M8K2 D2M8K2.u4959 = [0, 352399251094, 943895588317, 501091586164, 35735801637, 0, 0, 0] := by
  rw [show D2M8K2.u4959 = KTree.node D2M8K2.t4966 (nat_lit 10997717) (nat_lit 2307134053) (nat_lit 0) D2M8K2.t4967 from rfl, totK_node, tot4966, tot4967]
  decide +kernel

theorem arows4962 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4962 = true := by
  rw [show D2M8K2.u4962 = KTree.node D2M8K2.t4968 (nat_lit 10999444) (nat_lit 3746584604) (nat_lit 0) D2M8K2.t4969 from rfl, allE_node, rows4968, irow4962, rows4969]
  all_goals rfl

theorem atot4962 : totK PD2M8K2 D2M8K2.u4962 = [0, 38068349305, 503052982224, 943318834013, 289246835346, 13036865798, 0, 0] := by
  rw [show D2M8K2.u4962 = KTree.node D2M8K2.t4968 (nat_lit 10999444) (nat_lit 3746584604) (nat_lit 0) D2M8K2.t4969 from rfl, totK_node, tot4968, tot4969]
  decide +kernel

theorem arows4963 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4963 = true := by
  rw [show D2M8K2.u4963 = KTree.node D2M8K2.t4970 (nat_lit 11001435) (nat_lit 3620461571) (nat_lit 0) D2M8K2.t4971 from rfl, allE_node, rows4970, irow4963, rows4971]
  all_goals rfl

theorem atot4963 : totK PD2M8K2 D2M8K2.u4963 = [0, 372977529137, 944522368417, 478549127136, 35871209166, 0, 0, 0] := by
  rw [show D2M8K2.u4963 = KTree.node D2M8K2.t4970 (nat_lit 11001435) (nat_lit 3620461571) (nat_lit 0) D2M8K2.t4971 from rfl, totK_node, tot4970, tot4971]
  decide +kernel

theorem arows4965 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4965 = true := by
  rw [show D2M8K2.u4965 = KTree.node D2M8K2.t4972 (nat_lit 11003157) (nat_lit 1677640347) (nat_lit 0) D2M8K2.t4973 from rfl, allE_node, rows4972, irow4965, rows4973]
  all_goals rfl

theorem atot4965 : totK PD2M8K2 D2M8K2.u4965 = [0, 16886721403, 492161667776, 969224408839, 300108901307, 13237669976, 0, 0] := by
  rw [show D2M8K2.u4965 = KTree.node D2M8K2.t4972 (nat_lit 11003157) (nat_lit 1677640347) (nat_lit 0) D2M8K2.t4973 from rfl, totK_node, tot4972, tot4973]
  decide +kernel

theorem arows4966 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4966 = true := by
  rw [show D2M8K2.u4966 = KTree.node D2M8K2.t4974 (nat_lit 11004539) (nat_lit 2645292172) (nat_lit 0) D2M8K2.t4975 from rfl, allE_node, rows4974, irow4966, rows4975]
  all_goals rfl

theorem atot4966 : totK PD2M8K2 D2M8K2.u4966 = [0, 373444033916, 923708098217, 484772103675, 40473753375, 0, 0, 0] := by
  rw [show D2M8K2.u4966 = KTree.node D2M8K2.t4974 (nat_lit 11004539) (nat_lit 2645292172) (nat_lit 0) D2M8K2.t4975 from rfl, totK_node, tot4974, tot4975]
  decide +kernel

theorem arows4970 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4970 = true := by
  rw [show D2M8K2.u4970 = KTree.node D2M8K2.t4976 (nat_lit 11006252) (nat_lit 3712914743) (nat_lit 0) D2M8K2.t4977 from rfl, allE_node, rows4976, irow4970, rows4977]
  all_goals rfl

theorem atot4970 : totK PD2M8K2 D2M8K2.u4970 = [0, 68135786554, 628857327446, 907425311363, 204022727907, 4976872846, 0, 0] := by
  rw [show D2M8K2.u4970 = KTree.node D2M8K2.t4976 (nat_lit 11006252) (nat_lit 3712914743) (nat_lit 0) D2M8K2.t4977 from rfl, totK_node, tot4976, tot4977]
  decide +kernel

theorem arows4971 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4971 = true := by
  rw [show D2M8K2.u4971 = KTree.node D2M8K2.t4978 (nat_lit 11008305) (nat_lit 1757069487) (nat_lit 0) D2M8K2.t4979 from rfl, allE_node, rows4978, irow4971, rows4979]
  all_goals rfl

theorem atot4971 : totK PD2M8K2 D2M8K2.u4971 = [0, 307723209222, 894569887997, 595811516721, 63040729664, 0, 0, 0] := by
  rw [show D2M8K2.u4971 = KTree.node D2M8K2.t4978 (nat_lit 11008305) (nat_lit 1757069487) (nat_lit 0) D2M8K2.t4979 from rfl, totK_node, tot4978, tot4979]
  decide +kernel

theorem arows4973 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4973 = true := by
  rw [show D2M8K2.u4973 = KTree.node D2M8K2.t4980 (nat_lit 11010554) (nat_lit 4228345622) (nat_lit 0) D2M8K2.t4981 from rfl, allE_node, rows4980, irow4973, rows4981]
  all_goals rfl

theorem atot4973 : totK PD2M8K2 D2M8K2.u4973 = [0, 0, 385161183928, 947916526837, 461919704356, 33851730449, 0, 0] := by
  rw [show D2M8K2.u4973 = KTree.node D2M8K2.t4980 (nat_lit 11010554) (nat_lit 4228345622) (nat_lit 0) D2M8K2.t4981 from rfl, totK_node, tot4980, tot4981]
  decide +kernel

theorem arows4974 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4974 = true := by
  rw [show D2M8K2.u4974 = KTree.node D2M8K2.t4982 (nat_lit 11015433) (nat_lit 1842761263) (nat_lit 0) D2M8K2.t4983 from rfl, allE_node, rows4982, irow4974, rows4983]
  all_goals rfl

theorem atot4974 : totK PD2M8K2 D2M8K2.u4974 = [0, 0, 349688534522, 930266969669, 518914220240, 41525005733, 0, 0] := by
  rw [show D2M8K2.u4974 = KTree.node D2M8K2.t4982 (nat_lit 11015433) (nat_lit 1842761263) (nat_lit 0) D2M8K2.t4983 from rfl, totK_node, tot4982, tot4983]
  decide +kernel

theorem arows4977 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4977 = true := by
  rw [show D2M8K2.u4977 = KTree.node D2M8K2.t4984 (nat_lit 11016907) (nat_lit 1811174864) (nat_lit 0) D2M8K2.t4985 from rfl, allE_node, rows4984, irow4977, rows4985]
  all_goals rfl

theorem atot4977 : totK PD2M8K2 D2M8K2.u4977 = [0, 0, 0, 384321620367, 947399435530, 430692572382, 30397782892, 0] := by
  rw [show D2M8K2.u4977 = KTree.node D2M8K2.t4984 (nat_lit 11016907) (nat_lit 1811174864) (nat_lit 0) D2M8K2.t4985 from rfl, totK_node, tot4984, tot4985]
  decide +kernel

theorem arows4978 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4978 = true := by
  rw [show D2M8K2.u4978 = KTree.node D2M8K2.t4986 (nat_lit 11018243) (nat_lit 2519580469) (nat_lit 0) D2M8K2.t4987 from rfl, allE_node, rows4986, irow4978, rows4987]
  all_goals rfl

theorem atot4978 : totK PD2M8K2 D2M8K2.u4978 = [0, 0, 332530354145, 826503697771, 515842698217, 120689673783, 6524090962, 0] := by
  rw [show D2M8K2.u4978 = KTree.node D2M8K2.t4986 (nat_lit 11018243) (nat_lit 2519580469) (nat_lit 0) D2M8K2.t4987 from rfl, totK_node, tot4986, tot4987]
  decide +kernel

theorem arows4980 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4980 = true := by
  rw [show D2M8K2.u4980 = KTree.node D2M8K2.t4988 (nat_lit 11020040) (nat_lit 3395493713) (nat_lit 0) D2M8K2.t4989 from rfl, allE_node, rows4988, irow4980, rows4989]
  all_goals rfl

theorem atot4980 : totK PD2M8K2 D2M8K2.u4980 = [0, 0, 80458130419, 624373908179, 889505670169, 200261004279, 5159868635, 0] := by
  rw [show D2M8K2.u4980 = KTree.node D2M8K2.t4988 (nat_lit 11020040) (nat_lit 3395493713) (nat_lit 0) D2M8K2.t4989 from rfl, totK_node, tot4988, tot4989]
  decide +kernel

theorem arows4981 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4981 = true := by
  rw [show D2M8K2.u4981 = KTree.node D2M8K2.t4990 (nat_lit 11022066) (nat_lit 3450218191) (nat_lit 0) D2M8K2.t4991 from rfl, allE_node, rows4990, irow4981, rows4991]
  all_goals rfl

theorem atot4981 : totK PD2M8K2 D2M8K2.u4981 = [0, 0, 364125603864, 918023702568, 495118518936, 43189544994, 0, 0] := by
  rw [show D2M8K2.u4981 = KTree.node D2M8K2.t4990 (nat_lit 11022066) (nat_lit 3450218191) (nat_lit 0) D2M8K2.t4991 from rfl, totK_node, tot4990, tot4991]
  decide +kernel

theorem arows4988 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4988 = true := by
  rw [show D2M8K2.u4988 = KTree.node D2M8K2.t4992 (nat_lit 11023888) (nat_lit 2300519945) (nat_lit 0) D2M8K2.t4993 from rfl, allE_node, rows4992, irow4988, rows4993]
  all_goals rfl

theorem atot4988 : totK PD2M8K2 D2M8K2.u4988 = [0, 0, 83078613629, 617187592927, 882697555938, 210968039294, 5218872685, 0] := by
  rw [show D2M8K2.u4988 = KTree.node D2M8K2.t4992 (nat_lit 11023888) (nat_lit 2300519945) (nat_lit 0) D2M8K2.t4993 from rfl, totK_node, tot4992, tot4993]
  decide +kernel

theorem arows4989 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4989 = true := by
  rw [show D2M8K2.u4989 = KTree.node D2M8K2.t4994 (nat_lit 11025324) (nat_lit 3074618212) (nat_lit 0) D2M8K2.t4995 from rfl, allE_node, rows4994, irow4989, rows4995]
  all_goals rfl

theorem atot4989 : totK PD2M8K2 D2M8K2.u4989 = [0, 0, 377423340741, 912674222694, 478475423673, 40015528970, 0, 0] := by
  rw [show D2M8K2.u4989 = KTree.node D2M8K2.t4994 (nat_lit 11025324) (nat_lit 3074618212) (nat_lit 0) D2M8K2.t4995 from rfl, totK_node, tot4994, tot4995]
  decide +kernel

theorem arows4991 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4991 = true := by
  rw [show D2M8K2.u4991 = KTree.node D2M8K2.t4996 (nat_lit 11027252) (nat_lit 3192958036) (nat_lit 0) D2M8K2.t4997 from rfl, allE_node, rows4996, irow4991, rows4997]
  all_goals rfl

theorem atot4991 : totK PD2M8K2 D2M8K2.u4991 = [0, 0, 101934895774, 703552688791, 872036276944, 151071993943, 1415142070, 0] := by
  rw [show D2M8K2.u4991 = KTree.node D2M8K2.t4996 (nat_lit 11027252) (nat_lit 3192958036) (nat_lit 0) D2M8K2.t4997 from rfl, totK_node, tot4996, tot4997]
  decide +kernel

theorem arows4992 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4992 = true := by
  rw [show D2M8K2.u4992 = KTree.node D2M8K2.t4998 (nat_lit 11029190) (nat_lit 3100979891) (nat_lit 0) D2M8K2.t4999 from rfl, allE_node, rows4998, irow4992, rows4999]
  all_goals rfl

theorem atot4992 : totK PD2M8K2 D2M8K2.u4992 = [0, 0, 257134308654, 860171105501, 663886157543, 70596865769, 0, 0] := by
  rw [show D2M8K2.u4992 = KTree.node D2M8K2.t4998 (nat_lit 11029190) (nat_lit 3100979891) (nat_lit 0) D2M8K2.t4999 from rfl, totK_node, tot4998, tot4999]
  decide +kernel

theorem arows4995 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4995 = true := by
  rw [show D2M8K2.u4995 = KTree.node D2M8K2.t5000 (nat_lit 11031473) (nat_lit 1138614930) (nat_lit 0) D2M8K2.t5001 from rfl, allE_node, rows5000, irow4995, rows5001]
  all_goals rfl

theorem atot4995 : totK PD2M8K2 D2M8K2.u4995 = [0, 174993452374, 427731142439, 381911122817, 564931226470, 218926778482, 9302370699, 0] := by
  rw [show D2M8K2.u4995 = KTree.node D2M8K2.t5000 (nat_lit 11031473) (nat_lit 1138614930) (nat_lit 0) D2M8K2.t5001 from rfl, totK_node, tot5000, tot5001]
  decide +kernel

theorem arows4996 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4996 = true := by
  rw [show D2M8K2.u4996 = KTree.node D2M8K2.t5002 (nat_lit 11033129) (nat_lit 1624471130) (nat_lit 0) D2M8K2.t5003 from rfl, allE_node, rows5002, irow4996, rows5003]
  all_goals rfl

theorem atot4996 : totK PD2M8K2 D2M8K2.u4996 = [0, 202180892012, 749829732954, 699830289446, 114371713806, 1369150432, 0, 0] := by
  rw [show D2M8K2.u4996 = KTree.node D2M8K2.t5002 (nat_lit 11033129) (nat_lit 1624471130) (nat_lit 0) D2M8K2.t5003 from rfl, totK_node, tot5002, tot5003]
  decide +kernel

theorem arows4998 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4998 = true := by
  rw [show D2M8K2.u4998 = KTree.node D2M8K2.t5004 (nat_lit 11035566) (nat_lit 3648322546) (nat_lit 0) D2M8K2.t5005 from rfl, allE_node, rows5004, irow4998, rows5005]
  all_goals rfl

theorem atot4998 : totK PD2M8K2 D2M8K2.u4998 = [0, 284986735448, 851873912481, 645518934009, 66507833905, 0, 0, 0] := by
  rw [show D2M8K2.u4998 = KTree.node D2M8K2.t5004 (nat_lit 11035566) (nat_lit 3648322546) (nat_lit 0) D2M8K2.t5005 from rfl, totK_node, tot5004, tot5005]
  decide +kernel

theorem arows4999 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u4999 = true := by
  rw [show D2M8K2.u4999 = KTree.node D2M8K2.t5006 (nat_lit 11037122) (nat_lit 4134394906) (nat_lit 0) D2M8K2.t5007 from rfl, allE_node, rows5006, irow4999, rows5007]
  all_goals rfl

theorem atot4999 : totK PD2M8K2 D2M8K2.u4999 = [0, 135022454494, 616911006291, 756015278106, 293941430123, 25357676561, 0, 0] := by
  rw [show D2M8K2.u4999 = KTree.node D2M8K2.t5006 (nat_lit 11037122) (nat_lit 4134394906) (nat_lit 0) D2M8K2.t5007 from rfl, totK_node, tot5006, tot5007]
  decide +kernel

theorem arows5003 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5003 = true := by
  rw [show D2M8K2.u5003 = KTree.node D2M8K2.t5008 (nat_lit 11038400) (nat_lit 2251320070) (nat_lit 0) D2M8K2.t5009 from rfl, allE_node, rows5008, irow5003, rows5009]
  all_goals rfl

theorem atot5003 : totK PD2M8K2 D2M8K2.u5003 = [0, 173216670710, 608811394849, 739934135881, 285982002197, 12206862772, 0, 0] := by
  rw [show D2M8K2.u5003 = KTree.node D2M8K2.t5008 (nat_lit 11038400) (nat_lit 2251320070) (nat_lit 0) D2M8K2.t5009 from rfl, totK_node, tot5008, tot5009]
  decide +kernel

theorem arows5004 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5004 = true := by
  rw [show D2M8K2.u5004 = KTree.node D2M8K2.t5010 (nat_lit 11039870) (nat_lit 2974609724) (nat_lit 0) D2M8K2.t5011 from rfl, allE_node, rows5010, irow5004, rows5011]
  all_goals rfl

theorem atot5004 : totK PD2M8K2 D2M8K2.u5004 = [0, 264500299179, 812835839710, 623353443957, 100165604197, 1164319620, 0, 0] := by
  rw [show D2M8K2.u5004 = KTree.node D2M8K2.t5010 (nat_lit 11039870) (nat_lit 2974609724) (nat_lit 0) D2M8K2.t5011 from rfl, totK_node, tot5010, tot5011]
  decide +kernel

theorem arows5006 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5006 = true := by
  rw [show D2M8K2.u5006 = KTree.node D2M8K2.t5012 (nat_lit 11041537) (nat_lit 1358898502) (nat_lit 0) D2M8K2.t5013 from rfl, allE_node, rows5012, irow5006, rows5013]
  all_goals rfl

theorem atot5006 : totK PD2M8K2 D2M8K2.u5006 = [0, 155406381531, 622579524895, 770721142808, 220935701885, 11885407614, 0, 0] := by
  rw [show D2M8K2.u5006 = KTree.node D2M8K2.t5012 (nat_lit 11041537) (nat_lit 1358898502) (nat_lit 0) D2M8K2.t5013 from rfl, totK_node, tot5012, tot5013]
  decide +kernel

theorem arows5007 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5007 = true := by
  rw [show D2M8K2.u5007 = KTree.node D2M8K2.t5014 (nat_lit 11046343) (nat_lit 2383241052) (nat_lit 0) D2M8K2.t5015 from rfl, allE_node, rows5014, irow5007, rows5015]
  all_goals rfl

theorem atot5007 : totK PD2M8K2 D2M8K2.u5007 = [0, 266450484026, 844090290785, 604510779549, 77928310953, 1096505104, 0, 0] := by
  rw [show D2M8K2.u5007 = KTree.node D2M8K2.t5014 (nat_lit 11046343) (nat_lit 2383241052) (nat_lit 0) D2M8K2.t5015 from rfl, totK_node, tot5014, tot5015]
  decide +kernel

theorem arows5010 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5010 = true := by
  rw [show D2M8K2.u5010 = KTree.node D2M8K2.t5016 (nat_lit 11048329) (nat_lit 1435456249) (nat_lit 0) D2M8K2.t5017 from rfl, allE_node, rows5016, irow5010, rows5017]
  all_goals rfl

theorem atot5010 : totK PD2M8K2 D2M8K2.u5010 = [0, 153291077650, 682745738116, 807392140629, 178580250866, 3884009855, 0, 0] := by
  rw [show D2M8K2.u5010 = KTree.node D2M8K2.t5016 (nat_lit 11048329) (nat_lit 1435456249) (nat_lit 0) D2M8K2.t5017 from rfl, totK_node, tot5016, tot5017]
  decide +kernel

theorem arows5011 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5011 = true := by
  rw [show D2M8K2.u5011 = KTree.node D2M8K2.t5018 (nat_lit 11050468) (nat_lit 4008919388) (nat_lit 0) D2M8K2.t5019 from rfl, allE_node, rows5018, irow5011, rows5019]
  all_goals rfl

theorem atot5011 : totK PD2M8K2 D2M8K2.u5011 = [0, 176734205922, 742667188263, 773547657460, 131649380890, 1268739303, 0, 0] := by
  rw [show D2M8K2.u5011 = KTree.node D2M8K2.t5018 (nat_lit 11050468) (nat_lit 4008919388) (nat_lit 0) D2M8K2.t5019 from rfl, totK_node, tot5018, tot5019]
  decide +kernel

theorem arows5013 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5013 = true := by
  rw [show D2M8K2.u5013 = KTree.node D2M8K2.t5020 (nat_lit 11052450) (nat_lit 2354720587) (nat_lit 2048) D2M8K2.t5021 from rfl, allE_node, rows5020, irow5013, rows5021]
  all_goals rfl

theorem atot5013 : totK PD2M8K2 D2M8K2.u5013 = [0, 0, 356928127431, 933012214366, 436743022722, 26580874640, 0, 0] := by
  rw [show D2M8K2.u5013 = KTree.node D2M8K2.t5020 (nat_lit 11052450) (nat_lit 2354720587) (nat_lit 2048) D2M8K2.t5021 from rfl, totK_node, tot5020, tot5021]
  decide +kernel

theorem arows5014 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5014 = true := by
  rw [show D2M8K2.u5014 = KTree.node D2M8K2.t5022 (nat_lit 11054212) (nat_lit 3828483055) (nat_lit 0) D2M8K2.t5023 from rfl, allE_node, rows5022, irow5014, rows5023]
  all_goals rfl

theorem atot5014 : totK PD2M8K2 D2M8K2.u5014 = [0, 0, 144703593425, 731162725006, 755765062485, 97903526048, 1206465782, 0] := by
  rw [show D2M8K2.u5014 = KTree.node D2M8K2.t5022 (nat_lit 11054212) (nat_lit 3828483055) (nat_lit 0) D2M8K2.t5023 from rfl, totK_node, tot5022, tot5023]
  decide +kernel

theorem arows5019 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5019 = true := by
  rw [show D2M8K2.u5019 = KTree.node D2M8K2.t5024 (nat_lit 11056681) (nat_lit 1231560946) (nat_lit 0) D2M8K2.t5025 from rfl, allE_node, rows5024, irow5019, rows5025]
  all_goals rfl

theorem atot5019 : totK PD2M8K2 D2M8K2.u5019 = [0, 0, 379995130715, 955779588832, 466837721509, 36114693005, 0, 0] := by
  rw [show D2M8K2.u5019 = KTree.node D2M8K2.t5024 (nat_lit 11056681) (nat_lit 1231560946) (nat_lit 0) D2M8K2.t5025 from rfl, totK_node, tot5024, tot5025]
  decide +kernel

theorem arows5020 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5020 = true := by
  rw [show D2M8K2.u5020 = KTree.node D2M8K2.t5026 (nat_lit 11059694) (nat_lit 3781515585) (nat_lit 0) D2M8K2.t5027 from rfl, allE_node, rows5026, irow5020, rows5027]
  all_goals rfl

theorem atot5020 : totK PD2M8K2 D2M8K2.u5020 = [0, 0, 352502072380, 922688676909, 492269286571, 35454640967, 0, 0] := by
  rw [show D2M8K2.u5020 = KTree.node D2M8K2.t5026 (nat_lit 11059694) (nat_lit 3781515585) (nat_lit 0) D2M8K2.t5027 from rfl, totK_node, tot5026, tot5027]
  decide +kernel

theorem arows5022 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5022 = true := by
  rw [show D2M8K2.u5022 = KTree.node D2M8K2.t5028 (nat_lit 11061250) (nat_lit 4013028683) (nat_lit 0) D2M8K2.t5029 from rfl, allE_node, rows5028, irow5022, rows5029]
  all_goals rfl

theorem atot5022 : totK PD2M8K2 D2M8K2.u5022 = [0, 0, 83296233045, 599455424370, 825705686109, 223855095529, 10552856705, 0] := by
  rw [show D2M8K2.u5022 = KTree.node D2M8K2.t5028 (nat_lit 11061250) (nat_lit 4013028683) (nat_lit 0) D2M8K2.t5029 from rfl, totK_node, tot5028, tot5029]
  decide +kernel

theorem arows5023 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5023 = true := by
  rw [show D2M8K2.u5023 = KTree.node D2M8K2.t5030 (nat_lit 11066510) (nat_lit 3878762720) (nat_lit 0) D2M8K2.t5031 from rfl, allE_node, rows5030, irow5023, rows5031]
  all_goals rfl

theorem atot5023 : totK PD2M8K2 D2M8K2.u5023 = [0, 0, 328514608695, 861760406850, 509129897769, 77076255988, 2463340669, 0] := by
  rw [show D2M8K2.u5023 = KTree.node D2M8K2.t5030 (nat_lit 11066510) (nat_lit 3878762720) (nat_lit 0) D2M8K2.t5031 from rfl, totK_node, tot5030, tot5031]
  decide +kernel

theorem arows5026 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5026 = true := by
  rw [show D2M8K2.u5026 = KTree.node D2M8K2.t5032 (nat_lit 11068114) (nat_lit 2618707100) (nat_lit 0) D2M8K2.t5033 from rfl, allE_node, rows5032, irow5026, rows5033]
  all_goals rfl

theorem atot5026 : totK PD2M8K2 D2M8K2.u5026 = [0, 0, 91298305516, 685159602195, 805355277192, 131116301327, 2012620868, 0] := by
  rw [show D2M8K2.u5026 = KTree.node D2M8K2.t5032 (nat_lit 11068114) (nat_lit 2618707100) (nat_lit 0) D2M8K2.t5033 from rfl, totK_node, tot5032, tot5033]
  decide +kernel

theorem arows5027 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5027 = true := by
  rw [show D2M8K2.u5027 = KTree.node D2M8K2.t5034 (nat_lit 11070179) (nat_lit 2849658345) (nat_lit 0) D2M8K2.t5035 from rfl, allE_node, rows5034, irow5027, rows5035]
  all_goals rfl

theorem atot5027 : totK PD2M8K2 D2M8K2.u5027 = [0, 37944309145, 380925808104, 848994011113, 484120304522, 62766518504, 2561774784, 0] := by
  rw [show D2M8K2.u5027 = KTree.node D2M8K2.t5034 (nat_lit 11070179) (nat_lit 2849658345) (nat_lit 0) D2M8K2.t5035 from rfl, totK_node, tot5034, tot5035]
  decide +kernel

theorem arows5029 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5029 = true := by
  rw [show D2M8K2.u5029 = KTree.node D2M8K2.t5036 (nat_lit 11074105) (nat_lit 1439895473) (nat_lit 0) D2M8K2.t5037 from rfl, allE_node, rows5036, irow5029, rows5037]
  all_goals rfl

theorem atot5029 : totK PD2M8K2 D2M8K2.u5029 = [0, 339318858702, 927107019472, 485675430730, 32963619704, 0, 0, 0] := by
  rw [show D2M8K2.u5029 = KTree.node D2M8K2.t5036 (nat_lit 11074105) (nat_lit 1439895473) (nat_lit 0) D2M8K2.t5037 from rfl, totK_node, tot5036, tot5037]
  decide +kernel

theorem arows5030 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5030 = true := by
  rw [show D2M8K2.u5030 = KTree.node D2M8K2.t5038 (nat_lit 11075996) (nat_lit 3359611355) (nat_lit 0) D2M8K2.t5039 from rfl, allE_node, rows5038, irow5030, rows5039]
  all_goals rfl

theorem atot5030 : totK PD2M8K2 D2M8K2.u5030 = [0, 158839781470, 688407659570, 828253878725, 140718319381, 1369150432, 0, 0] := by
  rw [show D2M8K2.u5030 = KTree.node D2M8K2.t5038 (nat_lit 11075996) (nat_lit 3359611355) (nat_lit 0) D2M8K2.t5039 from rfl, totK_node, tot5038, tot5039]
  decide +kernel

theorem arows5034 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5034 = true := by
  rw [show D2M8K2.u5034 = KTree.node D2M8K2.t5040 (nat_lit 11077807) (nat_lit 2064580359) (nat_lit 0) D2M8K2.t5041 from rfl, allE_node, rows5040, irow5034, rows5041]
  all_goals rfl

theorem atot5034 : totK PD2M8K2 D2M8K2.u5034 = [0, 261241262944, 840744098290, 607646117968, 116318543252, 13132762340, 0, 0] := by
  rw [show D2M8K2.u5034 = KTree.node D2M8K2.t5040 (nat_lit 11077807) (nat_lit 2064580359) (nat_lit 0) D2M8K2.t5041 from rfl, totK_node, tot5040, tot5041]
  decide +kernel

theorem arows5035 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5035 = true := by
  rw [show D2M8K2.u5035 = KTree.node D2M8K2.t5042 (nat_lit 11079367) (nat_lit 2222680119) (nat_lit 0) D2M8K2.t5043 from rfl, allE_node, rows5042, irow5035, rows5043]
  all_goals rfl

theorem atot5035 : totK PD2M8K2 D2M8K2.u5035 = [0, 49080275478, 394528731284, 885129377574, 458945125361, 24429733046, 0, 0] := by
  rw [show D2M8K2.u5035 = KTree.node D2M8K2.t5042 (nat_lit 11079367) (nat_lit 2222680119) (nat_lit 0) D2M8K2.t5043 from rfl, totK_node, tot5042, tot5043]
  decide +kernel

theorem arows5037 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5037 = true := by
  rw [show D2M8K2.u5037 = KTree.node D2M8K2.t5044 (nat_lit 11084354) (nat_lit 4015663094) (nat_lit 0) D2M8K2.t5045 from rfl, allE_node, rows5044, irow5037, rows5045]
  all_goals rfl

theorem atot5037 : totK PD2M8K2 D2M8K2.u5037 = [0, 380698134798, 942749995113, 477828765689, 35572509608, 0, 0, 0] := by
  rw [show D2M8K2.u5037 = KTree.node D2M8K2.t5044 (nat_lit 11084354) (nat_lit 4015663094) (nat_lit 0) D2M8K2.t5045 from rfl, totK_node, tot5044, tot5045]
  decide +kernel

theorem arows5038 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5038 = true := by
  rw [show D2M8K2.u5038 = KTree.node D2M8K2.t5046 (nat_lit 11086010) (nat_lit 4223440842) (nat_lit 0) D2M8K2.t5047 from rfl, allE_node, rows5046, irow5038, rows5047]
  all_goals rfl

theorem atot5038 : totK PD2M8K2 D2M8K2.u5038 = [0, 8125304319, 494746621389, 956797883990, 300216159284, 13250685261, 0, 0] := by
  rw [show D2M8K2.u5038 = KTree.node D2M8K2.t5046 (nat_lit 11086010) (nat_lit 4223440842) (nat_lit 0) D2M8K2.t5047 from rfl, totK_node, tot5046, tot5047]
  decide +kernel

theorem arows5041 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5041 = true := by
  rw [show D2M8K2.u5041 = KTree.node D2M8K2.t5048 (nat_lit 11087370) (nat_lit 3823931145) (nat_lit 0) D2M8K2.t5049 from rfl, allE_node, rows5048, irow5041, rows5049]
  all_goals rfl

theorem atot5041 : totK PD2M8K2 D2M8K2.u5041 = [0, 330174124958, 886757832709, 538349397224, 53189592321, 0, 0, 0] := by
  rw [show D2M8K2.u5041 = KTree.node D2M8K2.t5048 (nat_lit 11087370) (nat_lit 3823931145) (nat_lit 0) D2M8K2.t5049 from rfl, totK_node, tot5048, tot5049]
  decide +kernel

theorem arows5042 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5042 = true := by
  rw [show D2M8K2.u5042 = KTree.node D2M8K2.t5050 (nat_lit 11088937) (nat_lit 1209918167) (nat_lit 0) D2M8K2.t5051 from rfl, allE_node, rows5050, irow5042, rows5051]
  all_goals rfl

theorem atot5042 : totK PD2M8K2 D2M8K2.u5042 = [0, 91718010228, 649794325753, 877023866244, 172469120676, 2165917952, 0, 0] := by
  rw [show D2M8K2.u5042 = KTree.node D2M8K2.t5050 (nat_lit 11088937) (nat_lit 1209918167) (nat_lit 0) D2M8K2.t5051 from rfl, totK_node, tot5050, tot5051]
  decide +kernel

theorem arows5044 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5044 = true := by
  rw [show D2M8K2.u5044 = KTree.node D2M8K2.t5052 (nat_lit 11091197) (nat_lit 1553846209) (nat_lit 0) D2M8K2.t5053 from rfl, allE_node, rows5052, irow5044, rows5053]
  all_goals rfl

theorem atot5044 : totK PD2M8K2 D2M8K2.u5044 = [0, 330174384325, 882257942229, 547811649087, 78636787040, 2814597007, 0, 0] := by
  rw [show D2M8K2.u5044 = KTree.node D2M8K2.t5052 (nat_lit 11091197) (nat_lit 1553846209) (nat_lit 0) D2M8K2.t5053 from rfl, totK_node, tot5052, tot5053]
  decide +kernel

theorem arows5045 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5045 = true := by
  rw [show D2M8K2.u5045 = KTree.node D2M8K2.t5054 (nat_lit 11093482) (nat_lit 4015847179) (nat_lit 0) D2M8K2.t5055 from rfl, allE_node, rows5054, irow5045, rows5055]
  all_goals rfl

theorem atot5045 : totK PD2M8K2 D2M8K2.u5045 = [0, 0, 418567016858, 964699711594, 372558384487, 18271634603, 0, 0] := by
  rw [show D2M8K2.u5045 = KTree.node D2M8K2.t5054 (nat_lit 11093482) (nat_lit 4015847179) (nat_lit 0) D2M8K2.t5055 from rfl, totK_node, tot5054, tot5055]
  decide +kernel

theorem arows5051 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5051 = true := by
  rw [show D2M8K2.u5051 = KTree.node D2M8K2.t5056 (nat_lit 11095087) (nat_lit 2024623013) (nat_lit 0) D2M8K2.t5057 from rfl, allE_node, rows5056, irow5051, rows5057]
  all_goals rfl

theorem atot5051 : totK PD2M8K2 D2M8K2.u5051 = [0, 0, 253635030521, 824734969940, 583566005482, 72325647821, 1239866073, 0] := by
  rw [show D2M8K2.u5051 = KTree.node D2M8K2.t5056 (nat_lit 11095087) (nat_lit 2024623013) (nat_lit 0) D2M8K2.t5057 from rfl, totK_node, tot5056, tot5057]
  decide +kernel

theorem arows5052 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5052 = true := by
  rw [show D2M8K2.u5052 = KTree.node D2M8K2.t5058 (nat_lit 11097647) (nat_lit 2749704928) (nat_lit 0) D2M8K2.t5059 from rfl, allE_node, rows5058, irow5052, rows5059]
  all_goals rfl

theorem atot5052 : totK PD2M8K2 D2M8K2.u5052 = [0, 0, 251332274207, 836612410310, 671931340640, 65557012449, 0, 0] := by
  rw [show D2M8K2.u5052 = KTree.node D2M8K2.t5058 (nat_lit 11097647) (nat_lit 2749704928) (nat_lit 0) D2M8K2.t5059 from rfl, totK_node, tot5058, tot5059]
  decide +kernel

theorem arows5054 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5054 = true := by
  rw [show D2M8K2.u5054 = KTree.node D2M8K2.t5060 (nat_lit 11098933) (nat_lit 965273417) (nat_lit 2) D2M8K2.t5061 from rfl, allE_node, rows5060, irow5054, rows5061]
  all_goals rfl

theorem atot5054 : totK PD2M8K2 D2M8K2.u5054 = [0, 0, 346136404987, 920976930742, 502655655129, 39928128612, 0, 0] := by
  rw [show D2M8K2.u5054 = KTree.node D2M8K2.t5060 (nat_lit 11098933) (nat_lit 965273417) (nat_lit 2) D2M8K2.t5061 from rfl, totK_node, tot5060, tot5061]
  decide +kernel

theorem arows5055 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5055 = true := by
  rw [show D2M8K2.u5055 = KTree.node D2M8K2.t5062 (nat_lit 11105596) (nat_lit 3369584643) (nat_lit 0) D2M8K2.t5063 from rfl, allE_node, rows5062, irow5055, rows5063]
  all_goals rfl

theorem atot5055 : totK PD2M8K2 D2M8K2.u5055 = [0, 0, 253262209647, 818907112614, 615572763241, 94099290681, 1171084559, 0] := by
  rw [show D2M8K2.u5055 = KTree.node D2M8K2.t5062 (nat_lit 11105596) (nat_lit 3369584643) (nat_lit 0) D2M8K2.t5063 from rfl, totK_node, tot5062, tot5063]
  decide +kernel

theorem arows5058 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5058 = true := by
  rw [show D2M8K2.u5058 = KTree.node D2M8K2.t5064 (nat_lit 11107302) (nat_lit 3792361165) (nat_lit 0) D2M8K2.t5065 from rfl, allE_node, rows5064, irow5058, rows5065]
  all_goals rfl

theorem atot5058 : totK PD2M8K2 D2M8K2.u5058 = [0, 0, 169581915327, 655639823631, 707767904714, 209056233891, 11934365838, 0] := by
  rw [show D2M8K2.u5058 = KTree.node D2M8K2.t5064 (nat_lit 11107302) (nat_lit 3792361165) (nat_lit 0) D2M8K2.t5065 from rfl, totK_node, tot5064, tot5065]
  decide +kernel

theorem arows5059 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5059 = true := by
  rw [show D2M8K2.u5059 = KTree.node D2M8K2.t5066 (nat_lit 11108740) (nat_lit 3599131598) (nat_lit 0) D2M8K2.t5067 from rfl, allE_node, rows5066, irow5059, rows5067]
  all_goals rfl

theorem atot5059 : totK PD2M8K2 D2M8K2.u5059 = [0, 0, 250318783376, 821398828785, 610501133291, 76142780459, 1053411165, 0] := by
  rw [show D2M8K2.u5059 = KTree.node D2M8K2.t5066 (nat_lit 11108740) (nat_lit 3599131598) (nat_lit 0) D2M8K2.t5067 from rfl, totK_node, tot5066, tot5067]
  decide +kernel

theorem arows5061 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5061 = true := by
  rw [show D2M8K2.u5061 = KTree.node D2M8K2.t5068 (nat_lit 11111062) (nat_lit 3553329980) (nat_lit 0) D2M8K2.t5069 from rfl, allE_node, rows5068, irow5061, rows5069]
  all_goals rfl

theorem atot5061 : totK PD2M8K2 D2M8K2.u5061 = [0, 0, 222133040475, 757785280119, 682201977346, 120832557790, 3667207281, 0] := by
  rw [show D2M8K2.u5061 = KTree.node D2M8K2.t5068 (nat_lit 11111062) (nat_lit 3553329980) (nat_lit 0) D2M8K2.t5069 from rfl, totK_node, tot5068, tot5069]
  decide +kernel

theorem arows5062 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5062 = true := by
  rw [show D2M8K2.u5062 = KTree.node D2M8K2.t5070 (nat_lit 11114612) (nat_lit 3652605966) (nat_lit 0) D2M8K2.t5071 from rfl, allE_node, rows5070, irow5062, rows5071]
  all_goals rfl

theorem atot5062 : totK PD2M8K2 D2M8K2.u5062 = [0, 257732979108, 687716943050, 577770697782, 248344187488, 20624007072, 0, 0] := by
  rw [show D2M8K2.u5062 = KTree.node D2M8K2.t5070 (nat_lit 11114612) (nat_lit 3652605966) (nat_lit 0) D2M8K2.t5071 from rfl, totK_node, tot5070, tot5071]
  decide +kernel

theorem arows5066 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5066 = true := by
  rw [show D2M8K2.u5066 = KTree.node D2M8K2.t5072 (nat_lit 11116234) (nat_lit 3871581885) (nat_lit 0) D2M8K2.t5073 from rfl, allE_node, rows5072, irow5066, rows5073]
  all_goals rfl

theorem atot5066 : totK PD2M8K2 D2M8K2.u5066 = [0, 138678414711, 716822544278, 792923139728, 117693108461, 1369150432, 0, 0] := by
  rw [show D2M8K2.u5066 = KTree.node D2M8K2.t5072 (nat_lit 11116234) (nat_lit 3871581885) (nat_lit 0) D2M8K2.t5073 from rfl, totK_node, tot5072, tot5073]
  decide +kernel

theorem arows5067 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5067 = true := by
  rw [show D2M8K2.u5067 = KTree.node D2M8K2.t5074 (nat_lit 11118579) (nat_lit 3681445855) (nat_lit 0) D2M8K2.t5075 from rfl, allE_node, rows5074, irow5067, rows5075]
  all_goals rfl

theorem atot5067 : totK PD2M8K2 D2M8K2.u5067 = [0, 319315960949, 866083283752, 579381188958, 60003372170, 0, 0, 0] := by
  rw [show D2M8K2.u5067 = KTree.node D2M8K2.t5074 (nat_lit 11118579) (nat_lit 3681445855) (nat_lit 0) D2M8K2.t5075 from rfl, totK_node, tot5074, tot5075]
  decide +kernel

theorem arows5069 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5069 = true := by
  rw [show D2M8K2.u5069 = KTree.node D2M8K2.t5076 (nat_lit 11120139) (nat_lit 3776241721) (nat_lit 0) D2M8K2.t5077 from rfl, allE_node, rows5076, irow5069, rows5077]
  all_goals rfl

theorem atot5069 : totK PD2M8K2 D2M8K2.u5069 = [0, 107013832152, 601863638267, 788664440949, 302253773174, 25356464804, 0, 0] := by
  rw [show D2M8K2.u5069 = KTree.node D2M8K2.t5076 (nat_lit 11120139) (nat_lit 3776241721) (nat_lit 0) D2M8K2.t5077 from rfl, totK_node, tot5076, tot5077]
  decide +kernel

theorem arows5070 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5070 = true := by
  rw [show D2M8K2.u5070 = KTree.node D2M8K2.t5078 (nat_lit 11121400) (nat_lit 3153762544) (nat_lit 0) D2M8K2.t5079 from rfl, allE_node, rows5078, irow5070, rows5079]
  all_goals rfl

theorem atot5070 : totK PD2M8K2 D2M8K2.u5070 = [0, 178101252088, 597630048052, 727547337810, 287033137881, 12202930986, 0, 0] := by
  rw [show D2M8K2.u5070 = KTree.node D2M8K2.t5078 (nat_lit 11121400) (nat_lit 3153762544) (nat_lit 0) D2M8K2.t5079 from rfl, totK_node, tot5078, tot5079]
  decide +kernel

theorem arows5073 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5073 = true := by
  rw [show D2M8K2.u5073 = KTree.node D2M8K2.t5080 (nat_lit 11122875) (nat_lit 3732120952) (nat_lit 0) D2M8K2.t5081 from rfl, allE_node, rows5080, irow5073, rows5081]
  all_goals rfl

theorem atot5073 : totK PD2M8K2 D2M8K2.u5073 = [0, 239430516859, 796430569754, 656514668416, 96606893660, 1164319620, 0, 0] := by
  rw [show D2M8K2.u5073 = KTree.node D2M8K2.t5080 (nat_lit 11122875) (nat_lit 3732120952) (nat_lit 0) D2M8K2.t5081 from rfl, totK_node, tot5080, tot5081]
  decide +kernel

theorem arows5074 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5074 = true := by
  rw [show D2M8K2.u5074 = KTree.node D2M8K2.t5082 (nat_lit 11124605) (nat_lit 2233364973) (nat_lit 0) D2M8K2.t5083 from rfl, allE_node, rows5082, irow5074, rows5083]
  all_goals rfl

theorem atot5074 : totK PD2M8K2 D2M8K2.u5074 = [0, 170590953727, 647439216372, 727660601102, 219974438939, 11885407614, 0, 0] := by
  rw [show D2M8K2.u5074 = KTree.node D2M8K2.t5082 (nat_lit 11124605) (nat_lit 2233364973) (nat_lit 0) D2M8K2.t5083 from rfl, totK_node, tot5082, tot5083]
  decide +kernel

theorem arows5076 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5076 = true := by
  rw [show D2M8K2.u5076 = KTree.node D2M8K2.t5084 (nat_lit 11126233) (nat_lit 1409730240) (nat_lit 0) D2M8K2.t5085 from rfl, allE_node, rows5084, irow5076, rows5085]
  all_goals rfl

theorem atot5076 : totK PD2M8K2 D2M8K2.u5076 = [0, 247149563842, 790571797967, 647587846446, 101060362633, 1198073392, 0, 0] := by
  rw [show D2M8K2.u5076 = KTree.node D2M8K2.t5084 (nat_lit 11126233) (nat_lit 1409730240) (nat_lit 0) D2M8K2.t5085 from rfl, totK_node, tot5084, tot5085]
  decide +kernel

theorem arows5077 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5077 = true := by
  rw [show D2M8K2.u5077 = KTree.node D2M8K2.t5086 (nat_lit 11127944) (nat_lit 3507696784) (nat_lit 0) D2M8K2.t5087 from rfl, allE_node, rows5086, irow5077, rows5087]
  all_goals rfl

theorem atot5077 : totK PD2M8K2 D2M8K2.u5077 = [0, 175160306834, 644523564792, 733842672921, 224229583636, 12052611869, 0, 0] := by
  rw [show D2M8K2.u5077 = KTree.node D2M8K2.t5086 (nat_lit 11127944) (nat_lit 3507696784) (nat_lit 0) D2M8K2.t5087 from rfl, totK_node, tot5086, tot5087]
  decide +kernel

theorem arows5082 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5082 = true := by
  rw [show D2M8K2.u5082 = KTree.node D2M8K2.t5088 (nat_lit 11129315) (nat_lit 2149552451) (nat_lit 0) D2M8K2.t5089 from rfl, allE_node, rows5088, irow5082, rows5089]
  all_goals rfl

theorem atot5082 : totK PD2M8K2 D2M8K2.u5082 = [0, 269119064056, 862266942946, 623527899539, 66585541786, 0, 0, 0] := by
  rw [show D2M8K2.u5082 = KTree.node D2M8K2.t5088 (nat_lit 11129315) (nat_lit 2149552451) (nat_lit 0) D2M8K2.t5089 from rfl, totK_node, tot5088, tot5089]
  decide +kernel

theorem arows5083 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5083 = true := by
  rw [show D2M8K2.u5083 = KTree.node D2M8K2.t5090 (nat_lit 11131245) (nat_lit 1493167766) (nat_lit 0) D2M8K2.t5091 from rfl, allE_node, rows5090, irow5083, rows5091]
  all_goals rfl

theorem atot5083 : totK PD2M8K2 D2M8K2.u5083 = [0, 0, 512170543776, 1020858939273, 268802244405, 6350335412, 0, 0] := by
  rw [show D2M8K2.u5083 = KTree.node D2M8K2.t5090 (nat_lit 11131245) (nat_lit 1493167766) (nat_lit 0) D2M8K2.t5091 from rfl, totK_node, tot5090, tot5091]
  decide +kernel

theorem arows5085 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5085 = true := by
  rw [show D2M8K2.u5085 = KTree.node D2M8K2.t5092 (nat_lit 11136493) (nat_lit 1128289678) (nat_lit 0) D2M8K2.t5093 from rfl, allE_node, rows5092, irow5085, rows5093]
  all_goals rfl

theorem atot5085 : totK PD2M8K2 D2M8K2.u5085 = [0, 0, 236864049952, 808694102272, 570831989114, 78131259578, 1138244013, 0] := by
  rw [show D2M8K2.u5085 = KTree.node D2M8K2.t5092 (nat_lit 11136493) (nat_lit 1128289678) (nat_lit 0) D2M8K2.t5093 from rfl, totK_node, tot5092, tot5093]
  decide +kernel

theorem arows5086 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5086 = true := by
  rw [show D2M8K2.u5086 = KTree.node D2M8K2.t5094 (nat_lit 11139161) (nat_lit 1700293131) (nat_lit 0) D2M8K2.t5095 from rfl, allE_node, rows5094, irow5086, rows5095]
  all_goals rfl

theorem atot5086 : totK PD2M8K2 D2M8K2.u5086 = [0, 0, 266949237983, 861030290552, 602904354535, 60775844272, 0, 0] := by
  rw [show D2M8K2.u5086 = KTree.node D2M8K2.t5094 (nat_lit 11139161) (nat_lit 1700293131) (nat_lit 0) D2M8K2.t5095 from rfl, totK_node, tot5094, tot5095]
  decide +kernel

theorem arows5089 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5089 = true := by
  rw [show D2M8K2.u5089 = KTree.node D2M8K2.t5096 (nat_lit 11140415) (nat_lit 2188132011) (nat_lit 0) D2M8K2.t5097 from rfl, allE_node, rows5096, irow5089, rows5097]
  all_goals rfl

theorem atot5089 : totK PD2M8K2 D2M8K2.u5089 = [0, 0, 364680952054, 947225446808, 466836211688, 28200879381, 0, 0] := by
  rw [show D2M8K2.u5089 = KTree.node D2M8K2.t5096 (nat_lit 11140415) (nat_lit 2188132011) (nat_lit 0) D2M8K2.t5097 from rfl, totK_node, tot5096, tot5097]
  decide +kernel

theorem arows5090 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5090 = true := by
  rw [show D2M8K2.u5090 = KTree.node D2M8K2.t5098 (nat_lit 11143635) (nat_lit 3606083326) (nat_lit 0) D2M8K2.t5099 from rfl, allE_node, rows5098, irow5090, rows5099]
  all_goals rfl

theorem atot5090 : totK PD2M8K2 D2M8K2.u5090 = [0, 0, 379297875771, 950721266805, 422144033098, 21541056324, 0, 0] := by
  rw [show D2M8K2.u5090 = KTree.node D2M8K2.t5098 (nat_lit 11143635) (nat_lit 3606083326) (nat_lit 0) D2M8K2.t5099 from rfl, totK_node, tot5098, tot5099]
  decide +kernel

theorem arows5092 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5092 = true := by
  rw [show D2M8K2.u5092 = KTree.node D2M8K2.t5100 (nat_lit 11146927) (nat_lit 2064212032) (nat_lit 0) D2M8K2.t5101 from rfl, allE_node, rows5100, irow5092, rows5101]
  all_goals rfl

theorem atot5092 : totK PD2M8K2 D2M8K2.u5092 = [0, 0, 357415351587, 942680321726, 468451806263, 23180947887, 0, 0] := by
  rw [show D2M8K2.u5092 = KTree.node D2M8K2.t5100 (nat_lit 11146927) (nat_lit 2064212032) (nat_lit 0) D2M8K2.t5101 from rfl, totK_node, tot5100, tot5101]
  decide +kernel

theorem arows5093 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5093 = true := by
  rw [show D2M8K2.u5093 = KTree.node D2M8K2.t5102 (nat_lit 11149954) (nat_lit 3650818592) (nat_lit 0) D2M8K2.t5103 from rfl, allE_node, rows5102, irow5093, rows5103]
  all_goals rfl

theorem atot5093 : totK PD2M8K2 D2M8K2.u5093 = [0, 0, 330575909230, 913436802010, 510893411876, 41165692854, 0, 0] := by
  rw [show D2M8K2.u5093 = KTree.node D2M8K2.t5102 (nat_lit 11149954) (nat_lit 3650818592) (nat_lit 0) D2M8K2.t5103 from rfl, totK_node, tot5102, tot5103]
  decide +kernel

theorem arows5097 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5097 = true := by
  rw [show D2M8K2.u5097 = KTree.node D2M8K2.t5104 (nat_lit 11151937) (nat_lit 1538809620) (nat_lit 0) D2M8K2.t5105 from rfl, allE_node, rows5104, irow5097, rows5105]
  all_goals rfl

theorem atot5097 : totK PD2M8K2 D2M8K2.u5097 = [0, 0, 122913013692, 659599851497, 783535389845, 183674573454, 4977114383, 0] := by
  rw [show D2M8K2.u5097 = KTree.node D2M8K2.t5104 (nat_lit 11151937) (nat_lit 1538809620) (nat_lit 0) D2M8K2.t5105 from rfl, totK_node, tot5104, tot5105]
  decide +kernel

theorem arows5098 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5098 = true := by
  rw [show D2M8K2.u5098 = KTree.node D2M8K2.t5106 (nat_lit 11198653) (nat_lit 1215652827) (nat_lit 0) D2M8K2.t5107 from rfl, allE_node, rows5106, irow5098, rows5107]
  all_goals rfl

theorem atot5098 : totK PD2M8K2 D2M8K2.u5098 = [0, 0, 297950682115, 879568199184, 558738895243, 41989767553, 0, 0] := by
  rw [show D2M8K2.u5098 = KTree.node D2M8K2.t5106 (nat_lit 11198653) (nat_lit 1215652827) (nat_lit 0) D2M8K2.t5107 from rfl, totK_node, tot5106, tot5107]
  decide +kernel

theorem arows5100 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5100 = true := by
  rw [show D2M8K2.u5100 = KTree.node D2M8K2.t5108 (nat_lit 11200672) (nat_lit 3588916934) (nat_lit 0) D2M8K2.t5109 from rfl, allE_node, rows5108, irow5100, rows5109]
  all_goals rfl

theorem atot5100 : totK PD2M8K2 D2M8K2.u5100 = [0, 0, 176369658508, 751290754745, 779673414023, 101484475345, 1369150432, 0] := by
  rw [show D2M8K2.u5100 = KTree.node D2M8K2.t5108 (nat_lit 11200672) (nat_lit 3588916934) (nat_lit 0) D2M8K2.t5109 from rfl, totK_node, tot5108, tot5109]
  decide +kernel

theorem arows5101 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5101 = true := by
  rw [show D2M8K2.u5101 = KTree.node D2M8K2.t5110 (nat_lit 11205843) (nat_lit 3399840399) (nat_lit 0) D2M8K2.t5111 from rfl, allE_node, rows5110, irow5101, rows5111]
  all_goals rfl

theorem atot5101 : totK PD2M8K2 D2M8K2.u5101 = [0, 0, 218455198012, 797889810970, 674123084569, 83673724400, 1164319620, 0] := by
  rw [show D2M8K2.u5101 = KTree.node D2M8K2.t5110 (nat_lit 11205843) (nat_lit 3399840399) (nat_lit 0) D2M8K2.t5111 from rfl, totK_node, tot5110, tot5111]
  decide +kernel

theorem arows5104 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5104 = true := by
  rw [show D2M8K2.u5104 = KTree.node D2M8K2.t5112 (nat_lit 11208083) (nat_lit 2569826151) (nat_lit 32) D2M8K2.t5113 from rfl, allE_node, rows5112, irow5104, rows5113]
  all_goals rfl

theorem atot5104 : totK PD2M8K2 D2M8K2.u5104 = [0, 0, 279466421745, 860985903376, 615523752584, 53948099153, 0, 0] := by
  rw [show D2M8K2.u5104 = KTree.node D2M8K2.t5112 (nat_lit 11208083) (nat_lit 2569826151) (nat_lit 32) D2M8K2.t5113 from rfl, totK_node, tot5112, tot5113]
  decide +kernel

theorem arows5105 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5105 = true := by
  rw [show D2M8K2.u5105 = KTree.node D2M8K2.t5114 (nat_lit 11209685) (nat_lit 1249855636) (nat_lit 0) D2M8K2.t5115 from rfl, allE_node, rows5114, irow5105, rows5115]
  all_goals rfl

theorem atot5105 : totK PD2M8K2 D2M8K2.u5105 = [0, 0, 119567109088, 731452470651, 823693257335, 105442064107, 1198073392, 0] := by
  rw [show D2M8K2.u5105 = KTree.node D2M8K2.t5114 (nat_lit 11209685) (nat_lit 1249855636) (nat_lit 0) D2M8K2.t5115 from rfl, totK_node, tot5114, tot5115]
  decide +kernel

theorem arows5107 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5107 = true := by
  rw [show D2M8K2.u5107 = KTree.node D2M8K2.t5116 (nat_lit 11211886) (nat_lit 2629755165) (nat_lit 0) D2M8K2.t5117 from rfl, allE_node, rows5116, irow5107, rows5117]
  all_goals rfl

theorem atot5107 : totK PD2M8K2 D2M8K2.u5107 = [0, 0, 382862753749, 913196129187, 462224329884, 32203077218, 0, 0] := by
  rw [show D2M8K2.u5107 = KTree.node D2M8K2.t5116 (nat_lit 11211886) (nat_lit 2629755165) (nat_lit 0) D2M8K2.t5117 from rfl, totK_node, tot5116, tot5117]
  decide +kernel

theorem arows5108 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5108 = true := by
  rw [show D2M8K2.u5108 = KTree.node D2M8K2.t5118 (nat_lit 11213610) (nat_lit 1609544485) (nat_lit 8) D2M8K2.t5119 from rfl, allE_node, rows5118, irow5108, rows5119]
  all_goals rfl

theorem atot5108 : totK PD2M8K2 D2M8K2.u5108 = [0, 0, 131783172819, 745066346062, 823317842212, 105116201786, 1096505104, 0] := by
  rw [show D2M8K2.u5108 = KTree.node D2M8K2.t5118 (nat_lit 11213610) (nat_lit 1609544485) (nat_lit 8) D2M8K2.t5119 from rfl, totK_node, tot5118, tot5119]
  decide +kernel

theorem arows5118 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5118 = true := by
  rw [show D2M8K2.u5118 = KTree.node D2M8K2.t5120 (nat_lit 11243384) (nat_lit 3357118011) (nat_lit 0) D2M8K2.t5121 from rfl, allE_node, rows5120, irow5118, rows5121]
  all_goals rfl

theorem atot5118 : totK PD2M8K2 D2M8K2.u5118 = [0, 0, 350078450232, 935077377377, 524845936245, 35865254710, 0, 0] := by
  rw [show D2M8K2.u5118 = KTree.node D2M8K2.t5120 (nat_lit 11243384) (nat_lit 3357118011) (nat_lit 0) D2M8K2.t5121 from rfl, totK_node, tot5120, tot5121]
  decide +kernel

theorem arows5119 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5119 = true := by
  rw [show D2M8K2.u5119 = KTree.node D2M8K2.t5122 (nat_lit 11244847) (nat_lit 1657038060) (nat_lit 0) D2M8K2.t5123 from rfl, allE_node, rows5122, irow5119, rows5123]
  all_goals rfl

theorem atot5119 : totK PD2M8K2 D2M8K2.u5119 = [0, 0, 0, 393502848976, 957700567152, 431016268951, 29394892645, 0] := by
  rw [show D2M8K2.u5119 = KTree.node D2M8K2.t5122 (nat_lit 11244847) (nat_lit 1657038060) (nat_lit 0) D2M8K2.t5123 from rfl, totK_node, tot5122, tot5123]
  decide +kernel

theorem arows5121 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5121 = true := by
  rw [show D2M8K2.u5121 = KTree.node D2M8K2.t5124 (nat_lit 11246215) (nat_lit 2200435174) (nat_lit 0) D2M8K2.t5125 from rfl, allE_node, rows5124, irow5121, rows5125]
  all_goals rfl

theorem atot5121 : totK PD2M8K2 D2M8K2.u5121 = [0, 0, 300247728352, 784220397193, 572560778557, 158990913866, 8104085798, 0] := by
  rw [show D2M8K2.u5121 = KTree.node D2M8K2.t5124 (nat_lit 11246215) (nat_lit 2200435174) (nat_lit 0) D2M8K2.t5125 from rfl, totK_node, tot5124, tot5125]
  decide +kernel

theorem arows5122 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5122 = true := by
  rw [show D2M8K2.u5122 = KTree.node D2M8K2.t5126 (nat_lit 11247879) (nat_lit 3638030424) (nat_lit 0) D2M8K2.t5127 from rfl, allE_node, rows5126, irow5122, rows5127]
  all_goals rfl

theorem atot5122 : totK PD2M8K2 D2M8K2.u5122 = [0, 0, 113361519492, 689697186156, 820200515795, 176762727189, 6821150176, 0] := by
  rw [show D2M8K2.u5122 = KTree.node D2M8K2.t5126 (nat_lit 11247879) (nat_lit 3638030424) (nat_lit 0) D2M8K2.t5127 from rfl, totK_node, tot5126, tot5127]
  decide +kernel

theorem arows5125 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5125 = true := by
  rw [show D2M8K2.u5125 = KTree.node D2M8K2.t5128 (nat_lit 11249746) (nat_lit 3970467854) (nat_lit 0) D2M8K2.t5129 from rfl, allE_node, rows5128, irow5125, rows5129]
  all_goals rfl

theorem atot5125 : totK PD2M8K2 D2M8K2.u5125 = [0, 0, 333391991296, 841993771600, 555401773505, 95275791780, 2266161007, 0] := by
  rw [show D2M8K2.u5125 = KTree.node D2M8K2.t5128 (nat_lit 11249746) (nat_lit 3970467854) (nat_lit 0) D2M8K2.t5129 from rfl, totK_node, tot5128, tot5129]
  decide +kernel

theorem arows5126 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5126 = true := by
  rw [show D2M8K2.u5126 = KTree.node D2M8K2.t5130 (nat_lit 11251387) (nat_lit 2230671150) (nat_lit 0) D2M8K2.t5131 from rfl, allE_node, rows5130, irow5126, rows5131]
  all_goals rfl

theorem atot5126 : totK PD2M8K2 D2M8K2.u5126 = [0, 0, 80460339412, 628962670904, 868501723877, 212637060582, 6860571838, 0] := by
  rw [show D2M8K2.u5126 = KTree.node D2M8K2.t5130 (nat_lit 11251387) (nat_lit 2230671150) (nat_lit 0) D2M8K2.t5131 from rfl, totK_node, tot5130, tot5131]
  decide +kernel

theorem arows5128 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5128 = true := by
  rw [show D2M8K2.u5128 = KTree.node D2M8K2.t5132 (nat_lit 11253230) (nat_lit 3861071316) (nat_lit 0) D2M8K2.t5133 from rfl, allE_node, rows5132, irow5128, rows5133]
  all_goals rfl

theorem atot5128 : totK PD2M8K2 D2M8K2.u5128 = [0, 0, 331587712623, 879661446449, 530674778506, 72292377720, 2348208889, 0] := by
  rw [show D2M8K2.u5128 = KTree.node D2M8K2.t5132 (nat_lit 11253230) (nat_lit 3861071316) (nat_lit 0) D2M8K2.t5133 from rfl, totK_node, tot5132, tot5133]
  decide +kernel

theorem arows5129 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5129 = true := by
  rw [show D2M8K2.u5129 = KTree.node D2M8K2.t5134 (nat_lit 11254851) (nat_lit 3715996827) (nat_lit 0) D2M8K2.t5135 from rfl, allE_node, rows5134, irow5129, rows5135]
  all_goals rfl

theorem atot5129 : totK PD2M8K2 D2M8K2.u5129 = [0, 0, 91681601894, 699395522336, 880869390702, 144520841929, 0, 0] := by
  rw [show D2M8K2.u5129 = KTree.node D2M8K2.t5134 (nat_lit 11254851) (nat_lit 3715996827) (nat_lit 0) D2M8K2.t5135 from rfl, totK_node, tot5134, tot5135]
  decide +kernel

theorem arows5133 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5133 = true := by
  rw [show D2M8K2.u5133 = KTree.node D2M8K2.t5136 (nat_lit 11257028) (nat_lit 3158495198) (nat_lit 0) D2M8K2.t5137 from rfl, allE_node, rows5136, irow5133, rows5137]
  all_goals rfl

theorem atot5133 : totK PD2M8K2 D2M8K2.u5133 = [0, 0, 347650490911, 904477273113, 545788824060, 70035284612, 2585032425, 0] := by
  rw [show D2M8K2.u5133 = KTree.node D2M8K2.t5136 (nat_lit 11257028) (nat_lit 3158495198) (nat_lit 0) D2M8K2.t5137 from rfl, totK_node, tot5136, tot5137]
  decide +kernel

theorem arows5134 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5134 = true := by
  rw [show D2M8K2.u5134 = KTree.node D2M8K2.t5138 (nat_lit 11259022) (nat_lit 2960917829) (nat_lit 0) D2M8K2.t5139 from rfl, allE_node, rows5138, irow5134, rows5139]
  all_goals rfl

theorem atot5134 : totK PD2M8K2 D2M8K2.u5134 = [0, 0, 105308681783, 569060808134, 840179456056, 259569340429, 9730542555, 0] := by
  rw [show D2M8K2.u5134 = KTree.node D2M8K2.t5138 (nat_lit 11259022) (nat_lit 2960917829) (nat_lit 0) D2M8K2.t5139 from rfl, totK_node, tot5138, tot5139]
  decide +kernel

theorem arows5136 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5136 = true := by
  rw [show D2M8K2.u5136 = KTree.node D2M8K2.t5140 (nat_lit 11281653) (nat_lit 1741627740) (nat_lit 0) D2M8K2.t5141 from rfl, allE_node, rows5140, irow5136, rows5141]
  all_goals rfl

theorem atot5136 : totK PD2M8K2 D2M8K2.u5136 = [0, 0, 271293877001, 817510635805, 590862732937, 80416302122, 1310166938, 0] := by
  rw [show D2M8K2.u5136 = KTree.node D2M8K2.t5140 (nat_lit 11281653) (nat_lit 1741627740) (nat_lit 0) D2M8K2.t5141 from rfl, totK_node, tot5140, tot5141]
  decide +kernel

theorem arows5137 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5137 = true := by
  rw [show D2M8K2.u5137 = KTree.node D2M8K2.t5142 (nat_lit 11284221) (nat_lit 1463288653) (nat_lit 0) D2M8K2.t5143 from rfl, allE_node, rows5142, irow5137, rows5143]
  all_goals rfl

theorem atot5137 : totK PD2M8K2 D2M8K2.u5137 = [0, 0, 226103857557, 802216936625, 734469094489, 77030093653, 0, 0] := by
  rw [show D2M8K2.u5137 = KTree.node D2M8K2.t5142 (nat_lit 11284221) (nat_lit 1463288653) (nat_lit 0) D2M8K2.t5143 from rfl, totK_node, tot5142, tot5143]
  decide +kernel

theorem arows5140 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5140 = true := by
  rw [show D2M8K2.u5140 = KTree.node D2M8K2.t5144 (nat_lit 11285459) (nat_lit 2889790332) (nat_lit 0) D2M8K2.t5145 from rfl, allE_node, rows5144, irow5140, rows5145]
  all_goals rfl

theorem atot5140 : totK PD2M8K2 D2M8K2.u5140 = [0, 0, 193373530450, 729455057120, 723413126780, 189665182795, 9631076594, 0] := by
  rw [show D2M8K2.u5140 = KTree.node D2M8K2.t5144 (nat_lit 11285459) (nat_lit 2889790332) (nat_lit 0) D2M8K2.t5145 from rfl, totK_node, tot5144, tot5145]
  decide +kernel

theorem arows5141 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5141 = true := by
  rw [show D2M8K2.u5141 = KTree.node D2M8K2.t5146 (nat_lit 11287301) (nat_lit 2330038851) (nat_lit 0) D2M8K2.t5147 from rfl, allE_node, rows5146, irow5141, rows5147]
  all_goals rfl

theorem atot5141 : totK PD2M8K2 D2M8K2.u5141 = [0, 0, 190917800172, 700415260200, 732699584739, 191844808487, 5382912678, 0] := by
  rw [show D2M8K2.u5141 = KTree.node D2M8K2.t5146 (nat_lit 11287301) (nat_lit 2330038851) (nat_lit 0) D2M8K2.t5147 from rfl, totK_node, tot5146, tot5147]
  decide +kernel

theorem arows5143 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5143 = true := by
  rw [show D2M8K2.u5143 = KTree.node D2M8K2.t5148 (nat_lit 11288776) (nat_lit 3841397406) (nat_lit 0) D2M8K2.t5149 from rfl, allE_node, rows5148, irow5143, rows5149]
  all_goals rfl

theorem atot5143 : totK PD2M8K2 D2M8K2.u5143 = [0, 0, 246611103308, 805592050909, 655678913748, 98904175638, 1164319620, 0] := by
  rw [show D2M8K2.u5143 = KTree.node D2M8K2.t5148 (nat_lit 11288776) (nat_lit 3841397406) (nat_lit 0) D2M8K2.t5149 from rfl, totK_node, tot5148, tot5149]
  decide +kernel

theorem arows5144 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5144 = true := by
  rw [show D2M8K2.u5144 = KTree.node D2M8K2.t5150 (nat_lit 11290469) (nat_lit 2312267637) (nat_lit 0) D2M8K2.t5151 from rfl, allE_node, rows5150, irow5144, rows5151]
  all_goals rfl

theorem atot5144 : totK PD2M8K2 D2M8K2.u5144 = [0, 0, 170051513913, 647684836886, 736461023071, 218363923354, 11885407614, 0] := by
  rw [show D2M8K2.u5144 = KTree.node D2M8K2.t5150 (nat_lit 11290469) (nat_lit 2312267637) (nat_lit 0) D2M8K2.t5151 from rfl, totK_node, tot5150, tot5151]
  decide +kernel

theorem arows5149 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5149 = true := by
  rw [show D2M8K2.u5149 = KTree.node D2M8K2.t5152 (nat_lit 11295296) (nat_lit 3643195736) (nat_lit 0) D2M8K2.t5153 from rfl, allE_node, rows5152, irow5149, rows5153]
  all_goals rfl

theorem atot5149 : totK PD2M8K2 D2M8K2.u5149 = [0, 0, 251138478841, 803617006720, 636348392858, 87386444401, 1096505104, 0] := by
  rw [show D2M8K2.u5149 = KTree.node D2M8K2.t5152 (nat_lit 11295296) (nat_lit 3643195736) (nat_lit 0) D2M8K2.t5153 from rfl, totK_node, tot5152, tot5153]
  decide +kernel

theorem arows5150 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5150 = true := by
  rw [show D2M8K2.u5150 = KTree.node D2M8K2.t5154 (nat_lit 11297243) (nat_lit 844870777) (nat_lit 0) D2M8K2.t5155 from rfl, allE_node, rows5154, irow5150, rows5155]
  all_goals rfl

theorem atot5150 : totK PD2M8K2 D2M8K2.u5150 = [0, 0, 153051350169, 708502700615, 802785065576, 157307772787, 3884009855, 0] := by
  rw [show D2M8K2.u5150 = KTree.node D2M8K2.t5154 (nat_lit 11297243) (nat_lit 844870777) (nat_lit 0) D2M8K2.t5155 from rfl, totK_node, tot5154, tot5155]
  decide +kernel

theorem arows5152 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5152 = true := by
  rw [show D2M8K2.u5152 = KTree.node D2M8K2.t5156 (nat_lit 11299396) (nat_lit 3772546580) (nat_lit 0) D2M8K2.t5157 from rfl, allE_node, rows5156, irow5152, rows5157]
  all_goals rfl

theorem atot5152 : totK PD2M8K2 D2M8K2.u5152 = [0, 0, 176664425682, 746614268082, 769928318023, 134423330149, 1391126877, 0] := by
  rw [show D2M8K2.u5152 = KTree.node D2M8K2.t5156 (nat_lit 11299396) (nat_lit 3772546580) (nat_lit 0) D2M8K2.t5157 from rfl, totK_node, tot5156, tot5157]
  decide +kernel

theorem arows5153 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5153 = true := by
  rw [show D2M8K2.u5153 = KTree.node D2M8K2.t5158 (nat_lit 11322818) (nat_lit 3731212820) (nat_lit 0) D2M8K2.t5159 from rfl, allE_node, rows5158, irow5153, rows5159]
  all_goals rfl

theorem atot5153 : totK PD2M8K2 D2M8K2.u5153 = [0, 0, 376690099417, 937536515809, 438550308584, 27050786794, 0, 0] := by
  rw [show D2M8K2.u5153 = KTree.node D2M8K2.t5158 (nat_lit 11322818) (nat_lit 3731212820) (nat_lit 0) D2M8K2.t5159 from rfl, totK_node, tot5158, tot5159]
  decide +kernel

theorem arows5156 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5156 = true := by
  rw [show D2M8K2.u5156 = KTree.node D2M8K2.t5160 (nat_lit 11324752) (nat_lit 3137581481) (nat_lit 0) D2M8K2.t5161 from rfl, allE_node, rows5160, irow5156, rows5161]
  all_goals rfl

theorem atot5156 : totK PD2M8K2 D2M8K2.u5156 = [0, 0, 112050439025, 672153978469, 888786723592, 133042011496, 1310517177, 0] := by
  rw [show D2M8K2.u5156 = KTree.node D2M8K2.t5160 (nat_lit 11324752) (nat_lit 3137581481) (nat_lit 0) D2M8K2.t5161 from rfl, totK_node, tot5160, tot5161]
  decide +kernel

theorem arows5157 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5157 = true := by
  rw [show D2M8K2.u5157 = KTree.node D2M8K2.t5162 (nat_lit 11326544) (nat_lit 3801488390) (nat_lit 0) D2M8K2.t5163 from rfl, allE_node, rows5162, irow5157, rows5163]
  all_goals rfl

theorem atot5157 : totK PD2M8K2 D2M8K2.u5157 = [0, 0, 307500922556, 918172074145, 565240579598, 49883877354, 0, 0] := by
  rw [show D2M8K2.u5157 = KTree.node D2M8K2.t5162 (nat_lit 11326544) (nat_lit 3801488390) (nat_lit 0) D2M8K2.t5163 from rfl, totK_node, tot5162, tot5163]
  decide +kernel

theorem arows5159 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5159 = true := by
  rw [show D2M8K2.u5159 = KTree.node D2M8K2.t5164 (nat_lit 11328242) (nat_lit 4010551708) (nat_lit 0) D2M8K2.t5165 from rfl, allE_node, rows5164, irow5159, rows5165]
  all_goals rfl

theorem atot5159 : totK PD2M8K2 D2M8K2.u5159 = [0, 0, 88388825251, 538585974167, 853200931213, 323244030939, 15066332673, 0] := by
  rw [show D2M8K2.u5159 = KTree.node D2M8K2.t5164 (nat_lit 11328242) (nat_lit 4010551708) (nat_lit 0) D2M8K2.t5165 from rfl, totK_node, tot5164, tot5165]
  decide +kernel

theorem arows5160 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5160 = true := by
  rw [show D2M8K2.u5160 = KTree.node D2M8K2.t5166 (nat_lit 11333348) (nat_lit 3303207460) (nat_lit 0) D2M8K2.t5167 from rfl, allE_node, rows5166, irow5160, rows5167]
  all_goals rfl

theorem atot5160 : totK PD2M8K2 D2M8K2.u5160 = [0, 0, 349327490504, 919266098567, 525473105975, 44156851463, 0, 0] := by
  rw [show D2M8K2.u5160 = KTree.node D2M8K2.t5166 (nat_lit 11333348) (nat_lit 3303207460) (nat_lit 0) D2M8K2.t5167 from rfl, totK_node, tot5166, tot5167]
  decide +kernel

theorem arows5164 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5164 = true := by
  rw [show D2M8K2.u5164 = KTree.node D2M8K2.t5168 (nat_lit 11334994) (nat_lit 3690754492) (nat_lit 0) D2M8K2.t5169 from rfl, allE_node, rows5168, irow5164, rows5169]
  all_goals rfl

theorem atot5164 : totK PD2M8K2 D2M8K2.u5164 = [0, 0, 58758900076, 494398575502, 916898397414, 293886020396, 13170675918, 0] := by
  rw [show D2M8K2.u5164 = KTree.node D2M8K2.t5168 (nat_lit 11334994) (nat_lit 3690754492) (nat_lit 0) D2M8K2.t5169 from rfl, totK_node, tot5168, tot5169]
  decide +kernel

theorem arows5165 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5165 = true := by
  rw [show D2M8K2.u5165 = KTree.node D2M8K2.t5170 (nat_lit 11336368) (nat_lit 3439917932) (nat_lit 0) D2M8K2.t5171 from rfl, allE_node, rows5170, irow5165, rows5171]
  all_goals rfl

theorem atot5165 : totK PD2M8K2 D2M8K2.u5165 = [0, 0, 362467063986, 917469141361, 480646722824, 40827619798, 0, 0] := by
  rw [show D2M8K2.u5165 = KTree.node D2M8K2.t5170 (nat_lit 11336368) (nat_lit 3439917932) (nat_lit 0) D2M8K2.t5171 from rfl, totK_node, tot5170, tot5171]
  decide +kernel

theorem arows5167 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5167 = true := by
  rw [show D2M8K2.u5167 = KTree.node D2M8K2.t5172 (nat_lit 11338087) (nat_lit 2065516491) (nat_lit 0) D2M8K2.t5173 from rfl, allE_node, rows5172, irow5167, rows5173]
  all_goals rfl

theorem atot5167 : totK PD2M8K2 D2M8K2.u5167 = [0, 0, 66973279467, 610878695572, 900075526916, 202618657050, 4980514959, 0] := by
  rw [show D2M8K2.u5167 = KTree.node D2M8K2.t5172 (nat_lit 11338087) (nat_lit 2065516491) (nat_lit 0) D2M8K2.t5173 from rfl, totK_node, tot5172, tot5173]
  decide +kernel

theorem arows5168 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5168 = true := by
  rw [show D2M8K2.u5168 = KTree.node D2M8K2.t5174 (nat_lit 11340236) (nat_lit 3103822266) (nat_lit 0) D2M8K2.t5175 from rfl, allE_node, rows5174, irow5168, rows5175]
  all_goals rfl

theorem atot5168 : totK PD2M8K2 D2M8K2.u5168 = [0, 0, 262893181160, 873818062665, 643152325980, 68292673334, 0, 0] := by
  rw [show D2M8K2.u5168 = KTree.node D2M8K2.t5174 (nat_lit 11340236) (nat_lit 3103822266) (nat_lit 0) D2M8K2.t5175 from rfl, totK_node, tot5174, tot5175]
  decide +kernel

theorem arows5171 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5171 = true := by
  rw [show D2M8K2.u5171 = KTree.node D2M8K2.t5176 (nat_lit 11363522) (nat_lit 3081068894) (nat_lit 0) D2M8K2.t5177 from rfl, allE_node, rows5176, irow5171, rows5177]
  all_goals rfl

theorem atot5171 : totK PD2M8K2 D2M8K2.u5171 = [0, 0, 256535150838, 798820428471, 618210390909, 110235699912, 1398595139, 0] := by
  rw [show D2M8K2.u5171 = KTree.node D2M8K2.t5176 (nat_lit 11363522) (nat_lit 3081068894) (nat_lit 0) D2M8K2.t5177 from rfl, totK_node, tot5176, tot5177]
  decide +kernel

theorem arows5172 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5172 = true := by
  rw [show D2M8K2.u5172 = KTree.node D2M8K2.t5178 (nat_lit 11365156) (nat_lit 3706606476) (nat_lit 0) D2M8K2.t5179 from rfl, allE_node, rows5178, irow5172, rows5179]
  all_goals rfl

theorem atot5172 : totK PD2M8K2 D2M8K2.u5172 = [0, 0, 138081896298, 710704436228, 783123800030, 114312056544, 1326647619, 0] := by
  rw [show D2M8K2.u5172 = KTree.node D2M8K2.t5178 (nat_lit 11365156) (nat_lit 3706606476) (nat_lit 0) D2M8K2.t5179 from rfl, totK_node, tot5178, tot5179]
  decide +kernel

theorem arows5174 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5174 = true := by
  rw [show D2M8K2.u5174 = KTree.node D2M8K2.t5180 (nat_lit 11367505) (nat_lit 1480700494) (nat_lit 0) D2M8K2.t5181 from rfl, allE_node, rows5180, irow5174, rows5181]
  all_goals rfl

theorem atot5174 : totK PD2M8K2 D2M8K2.u5174 = [0, 0, 355466894047, 887204228602, 534847146654, 45461247915, 0, 0] := by
  rw [show D2M8K2.u5174 = KTree.node D2M8K2.t5180 (nat_lit 11367505) (nat_lit 1480700494) (nat_lit 0) D2M8K2.t5181 from rfl, totK_node, tot5180, tot5181]
  decide +kernel

theorem arows5175 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5175 = true := by
  rw [show D2M8K2.u5175 = KTree.node D2M8K2.t5182 (nat_lit 11369043) (nat_lit 3694163947) (nat_lit 0) D2M8K2.t5183 from rfl, allE_node, rows5182, irow5175, rows5183]
  all_goals rfl

theorem atot5175 : totK PD2M8K2 D2M8K2.u5175 = [0, 0, 69515879333, 535404639803, 851841777645, 323186080180, 22301562661, 0] := by
  rw [show D2M8K2.u5175 = KTree.node D2M8K2.t5182 (nat_lit 11369043) (nat_lit 3694163947) (nat_lit 0) D2M8K2.t5183 from rfl, totK_node, tot5182, tot5183]
  decide +kernel

theorem arows5181 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5181 = true := by
  rw [show D2M8K2.u5181 = KTree.node D2M8K2.t5184 (nat_lit 11370507) (nat_lit 1302704321) (nat_lit 0) D2M8K2.t5185 from rfl, allE_node, rows5184, irow5181, rows5185]
  all_goals rfl

theorem atot5181 : totK PD2M8K2 D2M8K2.u5181 = [0, 0, 261633226920, 784060661680, 642439549606, 131342613278, 1409560813, 0] := by
  rw [show D2M8K2.u5181 = KTree.node D2M8K2.t5184 (nat_lit 11370507) (nat_lit 1302704321) (nat_lit 0) D2M8K2.t5185 from rfl, totK_node, tot5184, tot5185]
  decide +kernel

theorem arows5182 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5182 = true := by
  rw [show D2M8K2.u5182 = KTree.node D2M8K2.t5186 (nat_lit 11372038) (nat_lit 3340375324) (nat_lit 0) D2M8K2.t5187 from rfl, allE_node, rows5186, irow5182, rows5187]
  all_goals rfl

theorem atot5182 : totK PD2M8K2 D2M8K2.u5182 = [0, 0, 154981718383, 674731219989, 761941422882, 167503501621, 7025833541, 0] := by
  rw [show D2M8K2.u5182 = KTree.node D2M8K2.t5186 (nat_lit 11372038) (nat_lit 3340375324) (nat_lit 0) D2M8K2.t5187 from rfl, totK_node, tot5186, tot5187]
  decide +kernel

theorem arows5184 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5184 = true := by
  rw [show D2M8K2.u5184 = KTree.node D2M8K2.t5188 (nat_lit 11373896) (nat_lit 3491903270) (nat_lit 0) D2M8K2.t5189 from rfl, allE_node, rows5188, irow5184, rows5189]
  all_goals rfl

theorem atot5184 : totK PD2M8K2 D2M8K2.u5184 = [0, 0, 261759600285, 765645130755, 627189187532, 124903917098, 5883432551, 0] := by
  rw [show D2M8K2.u5184 = KTree.node D2M8K2.t5188 (nat_lit 11373896) (nat_lit 3491903270) (nat_lit 0) D2M8K2.t5189 from rfl, totK_node, tot5188, tot5189]
  decide +kernel

theorem arows5185 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5185 = true := by
  rw [show D2M8K2.u5185 = KTree.node D2M8K2.t5190 (nat_lit 11375432) (nat_lit 3583337978) (nat_lit 0) D2M8K2.t5191 from rfl, allE_node, rows5190, irow5185, rows5191]
  all_goals rfl

theorem atot5185 : totK PD2M8K2 D2M8K2.u5185 = [0, 0, 155067496513, 708867785643, 764845078719, 142379371220, 2279498976, 0] := by
  rw [show D2M8K2.u5185 = KTree.node D2M8K2.t5190 (nat_lit 11375432) (nat_lit 3583337978) (nat_lit 0) D2M8K2.t5191 from rfl, totK_node, tot5190, tot5191]
  decide +kernel

theorem arows5188 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5188 = true := by
  rw [show D2M8K2.u5188 = KTree.node D2M8K2.t5192 (nat_lit 11377277) (nat_lit 2223835371) (nat_lit 0) D2M8K2.t5193 from rfl, allE_node, rows5192, irow5188, rows5193]
  all_goals rfl

theorem atot5188 : totK PD2M8K2 D2M8K2.u5188 = [0, 0, 262825909177, 733370895307, 633730973749, 165404307275, 10830574984, 0] := by
  rw [show D2M8K2.u5188 = KTree.node D2M8K2.t5192 (nat_lit 11377277) (nat_lit 2223835371) (nat_lit 0) D2M8K2.t5193 from rfl, totK_node, tot5192, tot5193]
  decide +kernel

theorem arows5189 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5189 = true := by
  rw [show D2M8K2.u5189 = KTree.node D2M8K2.t5194 (nat_lit 11378454) (nat_lit 3560106283) (nat_lit 0) D2M8K2.t5195 from rfl, allE_node, rows5194, irow5189, rows5195]
  all_goals rfl

theorem atot5189 : totK PD2M8K2 D2M8K2.u5189 = [0, 0, 180758428870, 777054414739, 737218465625, 109021448362, 1096505104, 0] := by
  rw [show D2M8K2.u5189 = KTree.node D2M8K2.t5194 (nat_lit 11378454) (nat_lit 3560106283) (nat_lit 0) D2M8K2.t5195 from rfl, totK_node, tot5194, tot5195]
  decide +kernel

theorem arows5191 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5191 = true := by
  rw [show D2M8K2.u5191 = KTree.node D2M8K2.t5196 (nat_lit 11384165) (nat_lit 2300618398) (nat_lit 0) D2M8K2.t5197 from rfl, allE_node, rows5196, irow5191, rows5197]
  all_goals rfl

theorem atot5191 : totK PD2M8K2 D2M8K2.u5191 = [0, 0, 0, 464044467769, 984161829427, 307781150334, 8515795467, 0] := by
  rw [show D2M8K2.u5191 = KTree.node D2M8K2.t5196 (nat_lit 11384165) (nat_lit 2300618398) (nat_lit 0) D2M8K2.t5197 from rfl, totK_node, tot5196, tot5197]
  decide +kernel

theorem arows5192 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5192 = true := by
  rw [show D2M8K2.u5192 = KTree.node D2M8K2.t5198 (nat_lit 11387932) (nat_lit 3824643601) (nat_lit 0) D2M8K2.t5199 from rfl, allE_node, rows5198, irow5192, rows5199]
  all_goals rfl

theorem atot5192 : totK PD2M8K2 D2M8K2.u5192 = [0, 0, 0, 398301464078, 938060681921, 408199390621, 24119314466, 0] := by
  rw [show D2M8K2.u5192 = KTree.node D2M8K2.t5198 (nat_lit 11387932) (nat_lit 3824643601) (nat_lit 0) D2M8K2.t5199 from rfl, totK_node, tot5198, tot5199]
  decide +kernel

theorem arows5196 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5196 = true := by
  rw [show D2M8K2.u5196 = KTree.node D2M8K2.t5200 (nat_lit 11391100) (nat_lit 3809035114) (nat_lit 0) D2M8K2.t5201 from rfl, allE_node, rows5200, irow5196, rows5201]
  all_goals rfl

theorem atot5196 : totK PD2M8K2 D2M8K2.u5196 = [0, 0, 0, 414604517947, 961517699309, 386851496272, 18743348488, 0] := by
  rw [show D2M8K2.u5196 = KTree.node D2M8K2.t5200 (nat_lit 11391100) (nat_lit 3809035114) (nat_lit 0) D2M8K2.t5201 from rfl, totK_node, tot5200, tot5201]
  decide +kernel

theorem arows5197 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5197 = true := by
  rw [show D2M8K2.u5197 = KTree.node D2M8K2.t5202 (nat_lit 11394540) (nat_lit 3199526130) (nat_lit 0) D2M8K2.t5203 from rfl, allE_node, rows5202, irow5197, rows5203]
  all_goals rfl

theorem atot5197 : totK PD2M8K2 D2M8K2.u5197 = [0, 0, 0, 410429986268, 957308921634, 374852448249, 22018507381, 0] := by
  rw [show D2M8K2.u5197 = KTree.node D2M8K2.t5202 (nat_lit 11394540) (nat_lit 3199526130) (nat_lit 0) D2M8K2.t5203 from rfl, totK_node, tot5202, tot5203]
  decide +kernel

theorem arows5199 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5199 = true := by
  rw [show D2M8K2.u5199 = KTree.node D2M8K2.t5204 (nat_lit 11397979) (nat_lit 2224911653) (nat_lit 0) D2M8K2.t5205 from rfl, allE_node, rows5204, irow5199, rows5205]
  all_goals rfl

theorem atot5199 : totK PD2M8K2 D2M8K2.u5199 = [0, 0, 0, 396168449100, 943040267563, 417130257984, 28155033948, 0] := by
  rw [show D2M8K2.u5199 = KTree.node D2M8K2.t5204 (nat_lit 11397979) (nat_lit 2224911653) (nat_lit 0) D2M8K2.t5205 from rfl, totK_node, tot5204, tot5205]
  decide +kernel

theorem arows5200 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5200 = true := by
  rw [show D2M8K2.u5200 = KTree.node D2M8K2.t5206 (nat_lit 11399157) (nat_lit 1741952189) (nat_lit 0) D2M8K2.t5207 from rfl, allE_node, rows5206, irow5200, rows5207]
  all_goals rfl

theorem atot5200 : totK PD2M8K2 D2M8K2.u5200 = [0, 0, 0, 189093621931, 838216235692, 657964467862, 66949954731, 0] := by
  rw [show D2M8K2.u5200 = KTree.node D2M8K2.t5206 (nat_lit 11399157) (nat_lit 1741952189) (nat_lit 0) D2M8K2.t5207 from rfl, totK_node, tot5206, tot5207]
  decide +kernel

theorem arows5203 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5203 = true := by
  rw [show D2M8K2.u5203 = KTree.node D2M8K2.t5208 (nat_lit 11446537) (nat_lit 1508690721) (nat_lit 0) D2M8K2.t5209 from rfl, allE_node, rows5208, irow5203, rows5209]
  all_goals rfl

theorem atot5203 : totK PD2M8K2 D2M8K2.u5203 = [0, 266240933957, 671275698610, 316812140983, 157261827204, 283241831618, 88149113051, 1493059870] := by
  rw [show D2M8K2.u5203 = KTree.node D2M8K2.t5208 (nat_lit 11446537) (nat_lit 1508690721) (nat_lit 0) D2M8K2.t5209 from rfl, totK_node, tot5208, tot5209]
  decide +kernel

theorem arows5204 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5204 = true := by
  rw [show D2M8K2.u5204 = KTree.node D2M8K2.t5210 (nat_lit 11448075) (nat_lit 2454845779) (nat_lit 0) D2M8K2.t5211 from rfl, allE_node, rows5210, irow5204, rows5211]
  all_goals rfl

theorem atot5204 : totK PD2M8K2 D2M8K2.u5204 = [0, 152146670825, 720371513454, 784382586935, 134642132443, 1369150432, 0, 0] := by
  rw [show D2M8K2.u5204 = KTree.node D2M8K2.t5210 (nat_lit 11448075) (nat_lit 2454845779) (nat_lit 0) D2M8K2.t5211 from rfl, totK_node, tot5210, tot5211]
  decide +kernel

theorem arows5206 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5206 = true := by
  rw [show D2M8K2.u5206 = KTree.node D2M8K2.t5212 (nat_lit 11453658) (nat_lit 3208842754) (nat_lit 0) D2M8K2.t5213 from rfl, allE_node, rows5212, irow5206, rows5213]
  all_goals rfl

theorem atot5206 : totK PD2M8K2 D2M8K2.u5206 = [0, 313297622624, 896035079189, 555632875312, 51234883101, 0, 0, 0] := by
  rw [show D2M8K2.u5206 = KTree.node D2M8K2.t5212 (nat_lit 11453658) (nat_lit 3208842754) (nat_lit 0) D2M8K2.t5213 from rfl, totK_node, tot5212, tot5213]
  decide +kernel

theorem arows5207 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5207 = true := by
  rw [show D2M8K2.u5207 = KTree.node D2M8K2.t5214 (nat_lit 11455247) (nat_lit 2119518289) (nat_lit 0) D2M8K2.t5215 from rfl, allE_node, rows5214, irow5207, rows5215]
  all_goals rfl

theorem atot5207 : totK PD2M8K2 D2M8K2.u5207 = [0, 87773917060, 608466842894, 891080779268, 208386150877, 5398830306, 0, 0] := by
  rw [show D2M8K2.u5207 = KTree.node D2M8K2.t5214 (nat_lit 11455247) (nat_lit 2119518289) (nat_lit 0) D2M8K2.t5215 from rfl, totK_node, tot5214, tot5215]
  decide +kernel

theorem arows5212 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5212 = true := by
  rw [show D2M8K2.u5212 = KTree.node D2M8K2.t5216 (nat_lit 11457533) (nat_lit 993761352) (nat_lit 0) D2M8K2.t5217 from rfl, allE_node, rows5216, irow5212, rows5217]
  all_goals rfl

theorem atot5212 : totK PD2M8K2 D2M8K2.u5212 = [0, 381958506181, 920176118123, 471402906753, 42586971670, 0, 0, 0] := by
  rw [show D2M8K2.u5212 = KTree.node D2M8K2.t5216 (nat_lit 11457533) (nat_lit 993761352) (nat_lit 0) D2M8K2.t5217 from rfl, totK_node, tot5216, tot5217]
  decide +kernel

theorem arows5213 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5213 = true := by
  rw [show D2M8K2.u5213 = KTree.node D2M8K2.t5218 (nat_lit 11459263) (nat_lit 2372499785) (nat_lit 0) D2M8K2.t5219 from rfl, allE_node, rows5218, irow5213, rows5219]
  all_goals rfl

theorem atot5213 : totK PD2M8K2 D2M8K2.u5213 = [0, 70271379464, 587656563871, 916986449837, 223494126566, 5455647540, 0, 0] := by
  rw [show D2M8K2.u5213 = KTree.node D2M8K2.t5218 (nat_lit 11459263) (nat_lit 2372499785) (nat_lit 0) D2M8K2.t5219 from rfl, totK_node, tot5218, tot5219]
  decide +kernel

theorem arows5215 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5215 = true := by
  rw [show D2M8K2.u5215 = KTree.node D2M8K2.t5220 (nat_lit 11464260) (nat_lit 3241439807) (nat_lit 0) D2M8K2.t5221 from rfl, allE_node, rows5220, irow5215, rows5221]
  all_goals rfl

theorem atot5215 : totK PD2M8K2 D2M8K2.u5215 = [0, 371853052056, 939448330731, 476787113765, 34258255495, 0, 0, 0] := by
  rw [show D2M8K2.u5215 = KTree.node D2M8K2.t5220 (nat_lit 11464260) (nat_lit 3241439807) (nat_lit 0) D2M8K2.t5221 from rfl, totK_node, tot5220, tot5221]
  decide +kernel

theorem arows5216 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5216 = true := by
  rw [show D2M8K2.u5216 = KTree.node D2M8K2.t5222 (nat_lit 11465900) (nat_lit 2751390494) (nat_lit 0) D2M8K2.t5223 from rfl, allE_node, rows5222, irow5216, rows5223]
  all_goals rfl

theorem atot5216 : totK PD2M8K2 D2M8K2.u5216 = [0, 0, 491988407332, 985365178849, 289615922276, 8710740030, 0, 0] := by
  rw [show D2M8K2.u5216 = KTree.node D2M8K2.t5222 (nat_lit 11465900) (nat_lit 2751390494) (nat_lit 0) D2M8K2.t5223 from rfl, totK_node, tot5222, tot5223]
  decide +kernel

theorem arows5219 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5219 = true := by
  rw [show D2M8K2.u5219 = KTree.node D2M8K2.t5224 (nat_lit 11467716) (nat_lit 3249755499) (nat_lit 0) D2M8K2.t5225 from rfl, allE_node, rows5224, irow5219, rows5225]
  all_goals rfl

theorem atot5219 : totK PD2M8K2 D2M8K2.u5219 = [0, 0, 352038672094, 947521631212, 436829628145, 24160202976, 0, 0] := by
  rw [show D2M8K2.u5219 = KTree.node D2M8K2.t5224 (nat_lit 11467716) (nat_lit 3249755499) (nat_lit 0) D2M8K2.t5225 from rfl, totK_node, tot5224, tot5225]
  decide +kernel

theorem arows5220 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5220 = true := by
  rw [show D2M8K2.u5220 = KTree.node D2M8K2.t5226 (nat_lit 11469323) (nat_lit 2840675583) (nat_lit 0) D2M8K2.t5227 from rfl, allE_node, rows5226, irow5220, rows5227]
  all_goals rfl

theorem atot5220 : totK PD2M8K2 D2M8K2.u5220 = [0, 0, 135491689428, 712532632746, 780097984235, 118449031218, 1369150432, 0] := by
  rw [show D2M8K2.u5220 = KTree.node D2M8K2.t5226 (nat_lit 11469323) (nat_lit 2840675583) (nat_lit 0) D2M8K2.t5227 from rfl, totK_node, tot5226, tot5227]
  decide +kernel

theorem arows5222 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5222 = true := by
  rw [show D2M8K2.u5222 = KTree.node D2M8K2.t5228 (nat_lit 11474658) (nat_lit 1444780542) (nat_lit 0) D2M8K2.t5229 from rfl, allE_node, rows5228, irow5222, rows5229]
  all_goals rfl

theorem atot5222 : totK PD2M8K2 D2M8K2.u5222 = [0, 0, 353237845970, 958097988469, 450878995108, 21533860688, 0, 0] := by
  rw [show D2M8K2.u5222 = KTree.node D2M8K2.t5228 (nat_lit 11474658) (nat_lit 1444780542) (nat_lit 0) D2M8K2.t5229 from rfl, totK_node, tot5228, tot5229]
  decide +kernel

theorem arows5223 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5223 = true := by
  rw [show D2M8K2.u5223 = KTree.node D2M8K2.t5230 (nat_lit 11478336) (nat_lit 3507538042) (nat_lit 0) D2M8K2.t5231 from rfl, allE_node, rows5230, irow5223, rows5231]
  all_goals rfl

theorem atot5223 : totK PD2M8K2 D2M8K2.u5223 = [0, 0, 400712848751, 952830819964, 414943736610, 22780315802, 0, 0] := by
  rw [show D2M8K2.u5223 = KTree.node D2M8K2.t5230 (nat_lit 11478336) (nat_lit 3507538042) (nat_lit 0) D2M8K2.t5231 from rfl, totK_node, tot5230, tot5231]
  decide +kernel

theorem arows5227 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5227 = true := by
  rw [show D2M8K2.u5227 = KTree.node D2M8K2.t5232 (nat_lit 11484851) (nat_lit 2957674858) (nat_lit 0) D2M8K2.t5233 from rfl, allE_node, rows5232, irow5227, rows5233]
  all_goals rfl

theorem atot5227 : totK PD2M8K2 D2M8K2.u5227 = [0, 0, 355018022687, 947755686215, 469489898689, 23864900379, 0, 0] := by
  rw [show D2M8K2.u5227 = KTree.node D2M8K2.t5232 (nat_lit 11484851) (nat_lit 2957674858) (nat_lit 0) D2M8K2.t5233 from rfl, totK_node, tot5232, tot5233]
  decide +kernel

theorem arows5228 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5228 = true := by
  rw [show D2M8K2.u5228 = KTree.node D2M8K2.t5234 (nat_lit 11491759) (nat_lit 2213124872) (nat_lit 0) D2M8K2.t5235 from rfl, allE_node, rows5234, irow5228, rows5235]
  all_goals rfl

theorem atot5228 : totK PD2M8K2 D2M8K2.u5228 = [0, 270969029763, 763706865458, 614830481653, 177341528568, 13468148062, 0, 0] := by
  rw [show D2M8K2.u5228 = KTree.node D2M8K2.t5234 (nat_lit 11491759) (nat_lit 2213124872) (nat_lit 0) D2M8K2.t5235 from rfl, totK_node, tot5234, tot5235]
  decide +kernel

theorem arows5230 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5230 = true := by
  rw [show D2M8K2.u5230 = KTree.node D2M8K2.t5236 (nat_lit 11493264) (nat_lit 2727639945) (nat_lit 0) D2M8K2.t5237 from rfl, allE_node, rows5236, irow5230, rows5237]
  all_goals rfl

theorem atot5230 : totK PD2M8K2 D2M8K2.u5230 = [0, 170862182657, 647361898157, 714039235372, 279986049339, 25373788367, 0, 0] := by
  rw [show D2M8K2.u5230 = KTree.node D2M8K2.t5236 (nat_lit 11493264) (nat_lit 2727639945) (nat_lit 0) D2M8K2.t5237 from rfl, totK_node, tot5236, tot5237]
  decide +kernel

theorem arows5231 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5231 = true := by
  rw [show D2M8K2.u5231 = KTree.node D2M8K2.t5238 (nat_lit 11494446) (nat_lit 4025775211) (nat_lit 0) D2M8K2.t5239 from rfl, allE_node, rows5238, irow5231, rows5239]
  all_goals rfl

theorem atot5231 : totK PD2M8K2 D2M8K2.u5231 = [0, 156254519113, 587531763432, 765122222137, 305974515849, 12235609738, 0, 0] := by
  rw [show D2M8K2.u5231 = KTree.node D2M8K2.t5238 (nat_lit 11494446) (nat_lit 4025775211) (nat_lit 0) D2M8K2.t5239 from rfl, totK_node, tot5238, tot5239]
  decide +kernel

theorem arows5234 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5234 = true := by
  rw [show D2M8K2.u5234 = KTree.node D2M8K2.t5240 (nat_lit 11496001) (nat_lit 1341458369) (nat_lit 0) D2M8K2.t5241 from rfl, allE_node, rows5240, irow5234, rows5241]
  all_goals rfl

theorem atot5234 : totK PD2M8K2 D2M8K2.u5234 = [0, 258902961877, 808196139545, 645059505853, 97872524615, 1163840124, 0, 0] := by
  rw [show D2M8K2.u5234 = KTree.node D2M8K2.t5240 (nat_lit 11496001) (nat_lit 1341458369) (nat_lit 0) D2M8K2.t5241 from rfl, totK_node, tot5240, tot5241]
  decide +kernel

theorem arows5235 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5235 = true := by
  rw [show D2M8K2.u5235 = KTree.node D2M8K2.t5242 (nat_lit 11497730) (nat_lit 3635478296) (nat_lit 0) D2M8K2.t5243 from rfl, allE_node, rows5242, irow5235, rows5243]
  all_goals rfl

theorem atot5235 : totK PD2M8K2 D2M8K2.u5235 = [0, 156352226729, 656349602425, 774419804474, 214503860116, 10448781023, 0, 0] := by
  rw [show D2M8K2.u5235 = KTree.node D2M8K2.t5242 (nat_lit 11497730) (nat_lit 3635478296) (nat_lit 0) D2M8K2.t5243 from rfl, totK_node, tot5242, tot5243]
  decide +kernel

theorem arows5237 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5237 = true := by
  rw [show D2M8K2.u5237 = KTree.node D2M8K2.t5244 (nat_lit 11499417) (nat_lit 1794628471) (nat_lit 0) D2M8K2.t5245 from rfl, allE_node, rows5244, irow5237, rows5245]
  all_goals rfl

theorem atot5237 : totK PD2M8K2 D2M8K2.u5237 = [0, 259054156422, 805108173219, 644745537248, 100407248319, 1197396724, 0, 0] := by
  rw [show D2M8K2.u5237 = KTree.node D2M8K2.t5244 (nat_lit 11499417) (nat_lit 1794628471) (nat_lit 0) D2M8K2.t5245 from rfl, totK_node, tot5244, tot5245]
  decide +kernel

theorem arows5238 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5238 = true := by
  rw [show D2M8K2.u5238 = KTree.node D2M8K2.t5246 (nat_lit 11501137) (nat_lit 1245391183) (nat_lit 0) D2M8K2.t5247 from rfl, allE_node, rows5246, irow5238, rows5247]
  all_goals rfl

theorem atot5238 : totK PD2M8K2 D2M8K2.u5238 = [0, 103410131108, 591208552571, 870780626381, 255227013589, 10575243248, 0, 0] := by
  rw [show D2M8K2.u5238 = KTree.node D2M8K2.t5246 (nat_lit 11501137) (nat_lit 1245391183) (nat_lit 0) D2M8K2.t5247 from rfl, totK_node, tot5246, tot5247]
  decide +kernel

theorem arows5245 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5245 = true := by
  rw [show D2M8K2.u5245 = KTree.node D2M8K2.t5248 (nat_lit 11502776) (nat_lit 3820835085) (nat_lit 0) D2M8K2.t5249 from rfl, allE_node, rows5248, irow5245, rows5249]
  all_goals rfl

theorem atot5245 : totK PD2M8K2 D2M8K2.u5245 = [0, 242113639394, 868531782926, 679812133409, 67175122461, 0, 0, 0] := by
  rw [show D2M8K2.u5245 = KTree.node D2M8K2.t5248 (nat_lit 11502776) (nat_lit 3820835085) (nat_lit 0) D2M8K2.t5249 from rfl, totK_node, tot5248, tot5249]
  decide +kernel

theorem arows5246 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5246 = true := by
  rw [show D2M8K2.u5246 = KTree.node D2M8K2.t5250 (nat_lit 11505381) (nat_lit 1389198724) (nat_lit 0) D2M8K2.t5251 from rfl, allE_node, rows5250, irow5246, rows5251]
  all_goals rfl

theorem atot5246 : totK PD2M8K2 D2M8K2.u5246 = [0, 284171888635, 797540607081, 620600471653, 122976081056, 2575744806, 0, 0] := by
  rw [show D2M8K2.u5246 = KTree.node D2M8K2.t5250 (nat_lit 11505381) (nat_lit 1389198724) (nat_lit 0) D2M8K2.t5251 from rfl, totK_node, tot5250, tot5251]
  decide +kernel

theorem arows5248 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5248 = true := by
  rw [show D2M8K2.u5248 = KTree.node D2M8K2.t5252 (nat_lit 11506812) (nat_lit 3192875363) (nat_lit 0) D2M8K2.t5253 from rfl, allE_node, rows5252, irow5248, rows5253]
  all_goals rfl

theorem atot5248 : totK PD2M8K2 D2M8K2.u5248 = [0, 144995043752, 666385707594, 795241473962, 196022669923, 4961529011, 0, 0] := by
  rw [show D2M8K2.u5248 = KTree.node D2M8K2.t5252 (nat_lit 11506812) (nat_lit 3192875363) (nat_lit 0) D2M8K2.t5253 from rfl, totK_node, tot5252, tot5253]
  decide +kernel

theorem arows5249 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5249 = true := by
  rw [show D2M8K2.u5249 = KTree.node D2M8K2.t5254 (nat_lit 11512257) (nat_lit 1828015520) (nat_lit 0) D2M8K2.t5255 from rfl, allE_node, rows5254, irow5249, rows5255]
  all_goals rfl

theorem atot5249 : totK PD2M8K2 D2M8K2.u5249 = [0, 0, 361386321456, 909530072558, 499614187498, 45539324426, 0, 0] := by
  rw [show D2M8K2.u5249 = KTree.node D2M8K2.t5254 (nat_lit 11512257) (nat_lit 1828015520) (nat_lit 0) D2M8K2.t5255 from rfl, totK_node, tot5254, tot5255]
  decide +kernel

theorem arows5252 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5252 = true := by
  rw [show D2M8K2.u5252 = KTree.node D2M8K2.t5256 (nat_lit 11513418) (nat_lit 3842250255) (nat_lit 0) D2M8K2.t5257 from rfl, allE_node, rows5256, irow5252, rows5257]
  all_goals rfl

theorem atot5252 : totK PD2M8K2 D2M8K2.u5252 = [0, 0, 261980331105, 781287597651, 593843231406, 183469896944, 21385604922, 0] := by
  rw [show D2M8K2.u5252 = KTree.node D2M8K2.t5256 (nat_lit 11513418) (nat_lit 3842250255) (nat_lit 0) D2M8K2.t5257 from rfl, totK_node, tot5256, tot5257]
  decide +kernel

theorem arows5253 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5253 = true := by
  rw [show D2M8K2.u5253 = KTree.node D2M8K2.t5258 (nat_lit 11514876) (nat_lit 2449989230) (nat_lit 0) D2M8K2.t5259 from rfl, allE_node, rows5258, irow5253, rows5259]
  all_goals rfl

theorem atot5253 : totK PD2M8K2 D2M8K2.u5253 = [0, 0, 65839548356, 449484830469, 877072171554, 365817314653, 15536268932, 0] := by
  rw [show D2M8K2.u5253 = KTree.node D2M8K2.t5258 (nat_lit 11514876) (nat_lit 2449989230) (nat_lit 0) D2M8K2.t5259 from rfl, totK_node, tot5258, tot5259]
  decide +kernel

theorem arows5255 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5255 = true := by
  rw [show D2M8K2.u5255 = KTree.node D2M8K2.t5260 (nat_lit 11516160) (nat_lit 3401275093) (nat_lit 0) D2M8K2.t5261 from rfl, allE_node, rows5260, irow5255, rows5261]
  all_goals rfl

theorem atot5255 : totK PD2M8K2 D2M8K2.u5255 = [0, 0, 348244778834, 924262552676, 519063233302, 37664520086, 0, 0] := by
  rw [show D2M8K2.u5255 = KTree.node D2M8K2.t5260 (nat_lit 11516160) (nat_lit 3401275093) (nat_lit 0) D2M8K2.t5261 from rfl, totK_node, tot5260, tot5261]
  decide +kernel

theorem arows5256 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5256 = true := by
  rw [show D2M8K2.u5256 = KTree.node D2M8K2.t5262 (nat_lit 11518301) (nat_lit 2299445701) (nat_lit 0) D2M8K2.t5263 from rfl, allE_node, rows5262, irow5256, rows5263]
  all_goals rfl

theorem atot5256 : totK PD2M8K2 D2M8K2.u5256 = [0, 0, 97229344615, 626502679604, 860837087246, 199002014684, 5159868635, 0] := by
  rw [show D2M8K2.u5256 = KTree.node D2M8K2.t5262 (nat_lit 11518301) (nat_lit 2299445701) (nat_lit 0) D2M8K2.t5263 from rfl, totK_node, tot5262, tot5263]
  decide +kernel

theorem arows5260 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5260 = true := by
  rw [show D2M8K2.u5260 = KTree.node D2M8K2.t5264 (nat_lit 11520028) (nat_lit 3468013403) (nat_lit 0) D2M8K2.t5265 from rfl, allE_node, rows5264, irow5260, rows5265]
  all_goals rfl

theorem atot5260 : totK PD2M8K2 D2M8K2.u5260 = [0, 0, 313307575975, 906571547060, 556926605695, 45698201144, 0, 0] := by
  rw [show D2M8K2.u5260 = KTree.node D2M8K2.t5264 (nat_lit 11520028) (nat_lit 3468013403) (nat_lit 0) D2M8K2.t5265 from rfl, totK_node, tot5264, tot5265]
  decide +kernel

theorem arows5261 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5261 = true := by
  rw [show D2M8K2.u5261 = KTree.node D2M8K2.t5266 (nat_lit 11521880) (nat_lit 3412343236) (nat_lit 0) D2M8K2.t5267 from rfl, allE_node, rows5266, irow5261, rows5267]
  all_goals rfl

theorem atot5261 : totK PD2M8K2 D2M8K2.u5261 = [0, 0, 121689987511, 619725268517, 862233566964, 217596941884, 5218872685, 0] := by
  rw [show D2M8K2.u5261 = KTree.node D2M8K2.t5266 (nat_lit 11521880) (nat_lit 3412343236) (nat_lit 0) D2M8K2.t5267 from rfl, totK_node, tot5266, tot5267]
  decide +kernel

theorem arows5263 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5263 = true := by
  rw [show D2M8K2.u5263 = KTree.node D2M8K2.t5268 (nat_lit 11523529) (nat_lit 1382924231) (nat_lit 0) D2M8K2.t5269 from rfl, allE_node, rows5268, irow5263, rows5269]
  all_goals rfl

theorem atot5263 : totK PD2M8K2 D2M8K2.u5263 = [0, 0, 222615429568, 854134797806, 695930501953, 67132520376, 0, 0] := by
  rw [show D2M8K2.u5263 = KTree.node D2M8K2.t5268 (nat_lit 11523529) (nat_lit 1382924231) (nat_lit 0) D2M8K2.t5269 from rfl, totK_node, tot5268, tot5269]
  decide +kernel

theorem arows5264 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5264 = true := by
  rw [show D2M8K2.u5264 = KTree.node D2M8K2.t5270 (nat_lit 11526149) (nat_lit 2175670471) (nat_lit 0) D2M8K2.t5271 from rfl, allE_node, rows5270, irow5264, rows5271]
  all_goals rfl

theorem atot5264 : totK PD2M8K2 D2M8K2.u5264 = [0, 0, 301767290715, 820784892611, 599661015966, 102247152834, 1415142070, 0] := by
  rw [show D2M8K2.u5264 = KTree.node D2M8K2.t5270 (nat_lit 11526149) (nat_lit 2175670471) (nat_lit 0) D2M8K2.t5271 from rfl, totK_node, tot5270, tot5271]
  decide +kernel

theorem arows5267 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5267 = true := by
  rw [show D2M8K2.u5267 = KTree.node D2M8K2.t5272 (nat_lit 11527811) (nat_lit 2864153303) (nat_lit 0) D2M8K2.t5273 from rfl, allE_node, rows5272, irow5267, rows5273]
  all_goals rfl

theorem atot5267 : totK PD2M8K2 D2M8K2.u5267 = [0, 0, 122989245013, 699267605190, 816019961610, 163684786454, 1238673482, 0] := by
  rw [show D2M8K2.u5267 = KTree.node D2M8K2.t5272 (nat_lit 11527811) (nat_lit 2864153303) (nat_lit 0) D2M8K2.t5273 from rfl, totK_node, tot5272, tot5273]
  decide +kernel

theorem arows5268 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5268 = true := by
  rw [show D2M8K2.u5268 = KTree.node D2M8K2.t5274 (nat_lit 11529792) (nat_lit 3719395728) (nat_lit 0) D2M8K2.t5275 from rfl, allE_node, rows5274, irow5268, rows5275]
  all_goals rfl

theorem atot5268 : totK PD2M8K2 D2M8K2.u5268 = [0, 292271814381, 698448039030, 382887973590, 269153583045, 125335128258, 8063697217, 0] := by
  rw [show D2M8K2.u5268 = KTree.node D2M8K2.t5274 (nat_lit 11529792) (nat_lit 3719395728) (nat_lit 0) D2M8K2.t5275 from rfl, totK_node, tot5274, tot5275]
  decide +kernel

theorem arows5270 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5270 = true := by
  rw [show D2M8K2.u5270 = KTree.node D2M8K2.t5276 (nat_lit 11531170) (nat_lit 3448101636) (nat_lit 0) D2M8K2.t5277 from rfl, allE_node, rows5276, irow5270, rows5277]
  all_goals rfl

theorem atot5270 : totK PD2M8K2 D2M8K2.u5270 = [0, 113458766030, 679098380534, 865672218777, 141271034623, 1369150432, 0, 0] := by
  rw [show D2M8K2.u5270 = KTree.node D2M8K2.t5276 (nat_lit 11531170) (nat_lit 3448101636) (nat_lit 0) D2M8K2.t5277 from rfl, totK_node, tot5276, tot5277]
  decide +kernel

theorem arows5271 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5271 = true := by
  rw [show D2M8K2.u5271 = KTree.node D2M8K2.t5278 (nat_lit 11533571) (nat_lit 2821340958) (nat_lit 0) D2M8K2.t5279 from rfl, allE_node, rows5278, irow5271, rows5279]
  all_goals rfl

theorem atot5271 : totK PD2M8K2 D2M8K2.u5271 = [0, 389614701539, 937725601840, 480823487603, 39383579422, 0, 0, 0] := by
  rw [show D2M8K2.u5271 = KTree.node D2M8K2.t5278 (nat_lit 11533571) (nat_lit 2821340958) (nat_lit 0) D2M8K2.t5279 from rfl, totK_node, tot5278, tot5279]
  decide +kernel

theorem arows5276 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5276 = true := by
  rw [show D2M8K2.u5276 = KTree.node D2M8K2.t5280 (nat_lit 11535076) (nat_lit 3861555415) (nat_lit 0) D2M8K2.t5281 from rfl, allE_node, rows5280, irow5276, rows5281]
  all_goals rfl

theorem atot5276 : totK PD2M8K2 D2M8K2.u5276 = [0, 0, 440160152197, 941047386000, 417161408842, 29350937260, 0, 0] := by
  rw [show D2M8K2.u5276 = KTree.node D2M8K2.t5280 (nat_lit 11535076) (nat_lit 3861555415) (nat_lit 0) D2M8K2.t5281 from rfl, totK_node, tot5280, tot5281]
  decide +kernel

theorem arows5277 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5277 = true := by
  rw [show D2M8K2.u5277 = KTree.node D2M8K2.t5282 (nat_lit 11536454) (nat_lit 4180261009) (nat_lit 0) D2M8K2.t5283 from rfl, allE_node, rows5282, irow5277, rows5283]
  all_goals rfl

theorem atot5277 : totK PD2M8K2 D2M8K2.u5277 = [0, 266635319940, 766421731254, 605870119542, 172012864108, 8209931632, 0, 0] := by
  rw [show D2M8K2.u5277 = KTree.node D2M8K2.t5282 (nat_lit 11536454) (nat_lit 4180261009) (nat_lit 0) D2M8K2.t5283 from rfl, totK_node, tot5282, tot5283]
  decide +kernel

theorem arows5279 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5279 = true := by
  rw [show D2M8K2.u5279 = KTree.node D2M8K2.t5284 (nat_lit 11537878) (nat_lit 3417492328) (nat_lit 0) D2M8K2.t5285 from rfl, allE_node, rows5284, irow5279, rows5285]
  all_goals rfl

theorem atot5279 : totK PD2M8K2 D2M8K2.u5279 = [0, 171490899704, 706873337003, 772189168062, 159469194314, 2309606161, 0, 0] := by
  rw [show D2M8K2.u5279 = KTree.node D2M8K2.t5284 (nat_lit 11537878) (nat_lit 3417492328) (nat_lit 0) D2M8K2.t5285 from rfl, totK_node, tot5284, tot5285]
  decide +kernel

theorem arows5280 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5280 = true := by
  rw [show D2M8K2.u5280 = KTree.node D2M8K2.t5286 (nat_lit 11543183) (nat_lit 2421902922) (nat_lit 128) D2M8K2.t5287 from rfl, allE_node, rows5286, irow5280, rows5287]
  all_goals rfl

theorem atot5280 : totK PD2M8K2 D2M8K2.u5280 = [0, 240719510558, 731814737024, 656286952405, 167866272792, 10740121073, 0, 0] := by
  rw [show D2M8K2.u5280 = KTree.node D2M8K2.t5286 (nat_lit 11543183) (nat_lit 2421902922) (nat_lit 128) D2M8K2.t5287 from rfl, totK_node, tot5286, tot5287]
  decide +kernel

theorem arows5283 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5283 = true := by
  rw [show D2M8K2.u5283 = KTree.node D2M8K2.t5288 (nat_lit 11545178) (nat_lit 4079365871) (nat_lit 0) D2M8K2.t5289 from rfl, allE_node, rows5288, irow5283, rows5289]
  all_goals rfl

theorem atot5283 : totK PD2M8K2 D2M8K2.u5283 = [0, 169972050077, 721725661040, 761159291788, 147335066601, 3884009855, 0, 0] := by
  rw [show D2M8K2.u5283 = KTree.node D2M8K2.t5288 (nat_lit 11545178) (nat_lit 4079365871) (nat_lit 0) D2M8K2.t5289 from rfl, totK_node, tot5288, tot5289]
  decide +kernel

theorem arows5284 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5284 = true := by
  rw [show D2M8K2.u5284 = KTree.node D2M8K2.t5290 (nat_lit 11547223) (nat_lit 1152246304) (nat_lit 0) D2M8K2.t5291 from rfl, allE_node, rows5290, irow5284, rows5291]
  all_goals rfl

theorem atot5284 : totK PD2M8K2 D2M8K2.u5284 = [0, 342894143858, 928923806242, 523744883680, 39690068785, 0, 0, 0] := by
  rw [show D2M8K2.u5284 = KTree.node D2M8K2.t5290 (nat_lit 11547223) (nat_lit 1152246304) (nat_lit 0) D2M8K2.t5291 from rfl, totK_node, tot5290, tot5291]
  decide +kernel

theorem arows5286 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5286 = true := by
  rw [show D2M8K2.u5286 = KTree.node D2M8K2.t5292 (nat_lit 11548901) (nat_lit 2320275364) (nat_lit 0) D2M8K2.t5293 from rfl, allE_node, rows5292, irow5286, rows5293]
  all_goals rfl

theorem atot5286 : totK PD2M8K2 D2M8K2.u5286 = [0, 0, 460720558582, 978712324321, 330378998258, 9936117106, 0, 0] := by
  rw [show D2M8K2.u5286 = KTree.node D2M8K2.t5292 (nat_lit 11548901) (nat_lit 2320275364) (nat_lit 0) D2M8K2.t5293 from rfl, totK_node, tot5292, tot5293]
  decide +kernel

theorem arows5287 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5287 = true := by
  rw [show D2M8K2.u5287 = KTree.node D2M8K2.t5294 (nat_lit 11550732) (nat_lit 3039064465) (nat_lit 0) D2M8K2.t5295 from rfl, allE_node, rows5294, irow5287, rows5295]
  all_goals rfl

theorem atot5287 : totK PD2M8K2 D2M8K2.u5287 = [0, 0, 378006304882, 943653476510, 415119971358, 26926807673, 0, 0] := by
  rw [show D2M8K2.u5287 = KTree.node D2M8K2.t5294 (nat_lit 11550732) (nat_lit 3039064465) (nat_lit 0) D2M8K2.t5295 from rfl, totK_node, tot5294, tot5295]
  decide +kernel

theorem arows5291 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5291 = true := by
  rw [show D2M8K2.u5291 = KTree.node D2M8K2.t5296 (nat_lit 11552840) (nat_lit 3697004479) (nat_lit 0) D2M8K2.t5297 from rfl, allE_node, rows5296, irow5291, rows5297]
  all_goals rfl

theorem atot5291 : totK PD2M8K2 D2M8K2.u5291 = [0, 0, 118886349465, 711118415011, 822165904514, 121651839798, 1206465782, 0] := by
  rw [show D2M8K2.u5291 = KTree.node D2M8K2.t5296 (nat_lit 11552840) (nat_lit 3697004479) (nat_lit 0) D2M8K2.t5297 from rfl, totK_node, tot5296, tot5297]
  decide +kernel

theorem arows5292 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5292 = true := by
  rw [show D2M8K2.u5292 = KTree.node D2M8K2.t5298 (nat_lit 11554664) (nat_lit 3942464715) (nat_lit 0) D2M8K2.t5299 from rfl, allE_node, rows5298, irow5292, rows5299]
  all_goals rfl

theorem atot5292 : totK PD2M8K2 D2M8K2.u5292 = [0, 0, 384927553688, 957069005542, 449958600551, 26535372397, 0, 0] := by
  rw [show D2M8K2.u5292 = KTree.node D2M8K2.t5298 (nat_lit 11554664) (nat_lit 3942464715) (nat_lit 0) D2M8K2.t5299 from rfl, totK_node, tot5298, tot5299]
  decide +kernel

theorem arows5294 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5294 = true := by
  rw [show D2M8K2.u5294 = KTree.node D2M8K2.t5300 (nat_lit 11557634) (nat_lit 4025770644) (nat_lit 0) D2M8K2.t5301 from rfl, allE_node, rows5300, irow5294, rows5301]
  all_goals rfl

theorem atot5294 : totK PD2M8K2 D2M8K2.u5294 = [0, 0, 352911600509, 948409049605, 485071536260, 30830301070, 0, 0] := by
  rw [show D2M8K2.u5294 = KTree.node D2M8K2.t5300 (nat_lit 11557634) (nat_lit 4025770644) (nat_lit 0) D2M8K2.t5301 from rfl, totK_node, tot5300, tot5301]
  decide +kernel

theorem arows5295 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5295 = true := by
  rw [show D2M8K2.u5295 = KTree.node D2M8K2.t5302 (nat_lit 11559323) (nat_lit 2164695725) (nat_lit 0) D2M8K2.t5303 from rfl, allE_node, rows5302, irow5295, rows5303]
  all_goals rfl

theorem atot5295 : totK PD2M8K2 D2M8K2.u5295 = [0, 0, 66172613228, 531447830786, 871298389319, 257907386820, 9467545976, 0] := by
  rw [show D2M8K2.u5295 = KTree.node D2M8K2.t5302 (nat_lit 11559323) (nat_lit 2164695725) (nat_lit 0) D2M8K2.t5303 from rfl, totK_node, tot5302, tot5303]
  decide +kernel

theorem arows5298 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5298 = true := by
  rw [show D2M8K2.u5298 = KTree.node D2M8K2.t5304 (nat_lit 11564557) (nat_lit 1191660879) (nat_lit 0) D2M8K2.t5305 from rfl, allE_node, rows5304, irow5298, rows5305]
  all_goals rfl

theorem atot5298 : totK PD2M8K2 D2M8K2.u5298 = [0, 0, 259936078175, 908071872253, 601899334456, 39661764798, 0, 0] := by
  rw [show D2M8K2.u5298 = KTree.node D2M8K2.t5304 (nat_lit 11564557) (nat_lit 1191660879) (nat_lit 0) D2M8K2.t5305 from rfl, totK_node, tot5304, tot5305]
  decide +kernel

theorem arows5299 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5299 = true := by
  rw [show D2M8K2.u5299 = KTree.node D2M8K2.t5306 (nat_lit 11567496) (nat_lit 3586145959) (nat_lit 0) D2M8K2.t5307 from rfl, allE_node, rows5306, irow5299, rows5307]
  all_goals rfl

theorem atot5299 : totK PD2M8K2 D2M8K2.u5299 = [0, 0, 260445246798, 794420379189, 627643047906, 99199018682, 1330264907, 0] := by
  rw [show D2M8K2.u5299 = KTree.node D2M8K2.t5306 (nat_lit 11567496) (nat_lit 3586145959) (nat_lit 0) D2M8K2.t5307 from rfl, totK_node, tot5306, tot5307]
  decide +kernel

theorem arows5301 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5301 = true := by
  rw [show D2M8K2.u5301 = KTree.node D2M8K2.t5308 (nat_lit 11570710) (nat_lit 3547600099) (nat_lit 0) D2M8K2.t5309 from rfl, allE_node, rows5308, irow5301, rows5309]
  all_goals rfl

theorem atot5301 : totK PD2M8K2 D2M8K2.u5301 = [0, 228115287078, 677845375377, 627541104575, 250235408605, 17476474534, 0, 0] := by
  rw [show D2M8K2.u5301 = KTree.node D2M8K2.t5308 (nat_lit 11570710) (nat_lit 3547600099) (nat_lit 0) D2M8K2.t5309 from rfl, totK_node, tot5308, tot5309]
  decide +kernel

theorem arows5302 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5302 = true := by
  rw [show D2M8K2.u5302 = KTree.node D2M8K2.t5310 (nat_lit 11572399) (nat_lit 2177577682) (nat_lit 0) D2M8K2.t5311 from rfl, allE_node, rows5310, irow5302, rows5311]
  all_goals rfl

theorem atot5302 : totK PD2M8K2 D2M8K2.u5302 = [0, 150799174962, 727428831761, 783086363172, 123785562284, 1369150432, 0, 0] := by
  rw [show D2M8K2.u5302 = KTree.node D2M8K2.t5310 (nat_lit 11572399) (nat_lit 2177577682) (nat_lit 0) D2M8K2.t5311 from rfl, totK_node, tot5310, tot5311]
  decide +kernel

theorem arows5308 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5308 = true := by
  rw [show D2M8K2.u5308 = KTree.node D2M8K2.t5312 (nat_lit 11574788) (nat_lit 3137021106) (nat_lit 0) D2M8K2.t5313 from rfl, allE_node, rows5312, irow5308, rows5313]
  all_goals rfl

theorem atot5308 : totK PD2M8K2 D2M8K2.u5308 = [0, 332330514117, 884139015362, 578242764526, 61785693718, 0, 0, 0] := by
  rw [show D2M8K2.u5308 = KTree.node D2M8K2.t5312 (nat_lit 11574788) (nat_lit 3137021106) (nat_lit 0) D2M8K2.t5313 from rfl, totK_node, tot5312, tot5313]
  decide +kernel

theorem arows5309 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5309 = true := by
  rw [show D2M8K2.u5309 = KTree.node D2M8K2.t5314 (nat_lit 11576345) (nat_lit 1692115988) (nat_lit 0) D2M8K2.t5315 from rfl, allE_node, rows5314, irow5309, rows5315]
  all_goals rfl

theorem atot5309 : totK PD2M8K2 D2M8K2.u5309 = [0, 88459214294, 552425165115, 820695829627, 339983377328, 28205077490, 0, 0] := by
  rw [show D2M8K2.u5309 = KTree.node D2M8K2.t5314 (nat_lit 11576345) (nat_lit 1692115988) (nat_lit 0) D2M8K2.t5315 from rfl, totK_node, tot5314, tot5315]
  decide +kernel

theorem arows5311 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5311 = true := by
  rw [show D2M8K2.u5311 = KTree.node D2M8K2.t5316 (nat_lit 11581113) (nat_lit 1483209194) (nat_lit 0) D2M8K2.t5317 from rfl, allE_node, rows5316, irow5311, rows5317]
  all_goals rfl

theorem atot5311 : totK PD2M8K2 D2M8K2.u5311 = [0, 210452571835, 659705554127, 697962438087, 243645861877, 9353868799, 0, 0] := by
  rw [show D2M8K2.u5311 = KTree.node D2M8K2.t5316 (nat_lit 11581113) (nat_lit 1483209194) (nat_lit 0) D2M8K2.t5317 from rfl, totK_node, tot5316, tot5317]
  decide +kernel

theorem arows5312 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5312 = true := by
  rw [show D2M8K2.u5312 = KTree.node D2M8K2.t5318 (nat_lit 11582566) (nat_lit 3818741657) (nat_lit 0) D2M8K2.t5319 from rfl, allE_node, rows5318, irow5312, rows5319]
  all_goals rfl

theorem atot5312 : totK PD2M8K2 D2M8K2.u5312 = [0, 227867549869, 791478590091, 674646475659, 108002664505, 1198073392, 0, 0] := by
  rw [show D2M8K2.u5312 = KTree.node D2M8K2.t5318 (nat_lit 11582566) (nat_lit 3818741657) (nat_lit 0) D2M8K2.t5319 from rfl, totK_node, tot5318, tot5319]
  decide +kernel

theorem arows5315 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5315 = true := by
  rw [show D2M8K2.u5315 = KTree.node D2M8K2.t5320 (nat_lit 11584246) (nat_lit 3545471484) (nat_lit 0) D2M8K2.t5321 from rfl, allE_node, rows5320, irow5315, rows5321]
  all_goals rfl

theorem atot5315 : totK PD2M8K2 D2M8K2.u5315 = [0, 152574673325, 633445696868, 771815507263, 235831790246, 12052611869, 0, 0] := by
  rw [show D2M8K2.u5315 = KTree.node D2M8K2.t5320 (nat_lit 11584246) (nat_lit 3545471484) (nat_lit 0) D2M8K2.t5321 from rfl, totK_node, tot5320, tot5321]
  decide +kernel

theorem arows5316 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5316 = true := by
  rw [show D2M8K2.u5316 = KTree.node D2M8K2.t5322 (nat_lit 11585916) (nat_lit 2954287894) (nat_lit 0) D2M8K2.t5323 from rfl, allE_node, rows5322, irow5316, rows5323]
  all_goals rfl

theorem atot5316 : totK PD2M8K2 D2M8K2.u5316 = [0, 174773797690, 793174027588, 773645162882, 90405457921, 0, 0, 0] := by
  rw [show D2M8K2.u5316 = KTree.node D2M8K2.t5322 (nat_lit 11585916) (nat_lit 2954287894) (nat_lit 0) D2M8K2.t5323 from rfl, totK_node, tot5322, tot5323]
  decide +kernel

theorem arows5318 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5318 = true := by
  rw [show D2M8K2.u5318 = KTree.node D2M8K2.t5324 (nat_lit 11588475) (nat_lit 3677238597) (nat_lit 0) D2M8K2.t5325 from rfl, allE_node, rows5324, irow5318, rows5325]
  all_goals rfl

theorem atot5318 : totK PD2M8K2 D2M8K2.u5318 = [0, 333489663746, 845883781042, 526336666614, 100098063712, 3884009855, 0, 0] := by
  rw [show D2M8K2.u5318 = KTree.node D2M8K2.t5324 (nat_lit 11588475) (nat_lit 3677238597) (nat_lit 0) D2M8K2.t5325 from rfl, totK_node, tot5324, tot5325]
  decide +kernel

theorem arows5319 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5319 = true := by
  rw [show D2M8K2.u5319 = KTree.node D2M8K2.t5326 (nat_lit 11590019) (nat_lit 2876481568) (nat_lit 0) D2M8K2.t5327 from rfl, allE_node, rows5326, irow5319, rows5327]
  all_goals rfl

theorem atot5319 : totK PD2M8K2 D2M8K2.u5319 = [0, 92934196222, 578254886391, 866463039394, 247428161080, 6030373525, 0, 0] := by
  rw [show D2M8K2.u5319 = KTree.node D2M8K2.t5326 (nat_lit 11590019) (nat_lit 2876481568) (nat_lit 0) D2M8K2.t5327 from rfl, totK_node, tot5326, tot5327]
  decide +kernel

theorem arows5323 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5323 = true := by
  rw [show D2M8K2.u5323 = KTree.node D2M8K2.t5328 (nat_lit 11591668) (nat_lit 2684200353) (nat_lit 0) D2M8K2.t5329 from rfl, allE_node, rows5328, irow5323, rows5329]
  all_goals rfl

theorem atot5323 : totK PD2M8K2 D2M8K2.u5323 = [0, 0, 384025124593, 948564399620, 419821660699, 27095274420, 0, 0] := by
  rw [show D2M8K2.u5323 = KTree.node D2M8K2.t5328 (nat_lit 11591668) (nat_lit 2684200353) (nat_lit 0) D2M8K2.t5329 from rfl, totK_node, tot5328, tot5329]
  decide +kernel

theorem arows5324 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5324 = true := by
  rw [show D2M8K2.u5324 = KTree.node D2M8K2.t5330 (nat_lit 11593394) (nat_lit 1779261914) (nat_lit 0) D2M8K2.t5331 from rfl, allE_node, rows5330, irow5324, rows5331]
  all_goals rfl

theorem atot5324 : totK PD2M8K2 D2M8K2.u5324 = [0, 0, 142655788216, 733067747366, 775332904392, 106566857264, 1239866073, 0] := by
  rw [show D2M8K2.u5324 = KTree.node D2M8K2.t5330 (nat_lit 11593394) (nat_lit 1779261914) (nat_lit 0) D2M8K2.t5331 from rfl, totK_node, tot5330, tot5331]
  decide +kernel

theorem arows5326 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5326 = true := by
  rw [show D2M8K2.u5326 = KTree.node D2M8K2.t5332 (nat_lit 11595875) (nat_lit 2949372238) (nat_lit 0) D2M8K2.t5333 from rfl, allE_node, rows5332, irow5326, rows5333]
  all_goals rfl

theorem atot5326 : totK PD2M8K2 D2M8K2.u5326 = [0, 0, 363615824374, 946822338712, 499504629170, 37973287210, 0, 0] := by
  rw [show D2M8K2.u5326 = KTree.node D2M8K2.t5332 (nat_lit 11595875) (nat_lit 2949372238) (nat_lit 0) D2M8K2.t5333 from rfl, totK_node, tot5332, tot5333]
  decide +kernel

theorem arows5327 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5327 = true := by
  rw [show D2M8K2.u5327 = KTree.node D2M8K2.t5334 (nat_lit 11602316) (nat_lit 3222256475) (nat_lit 0) D2M8K2.t5335 from rfl, allE_node, rows5334, irow5327, rows5335]
  all_goals rfl

theorem atot5327 : totK PD2M8K2 D2M8K2.u5327 = [0, 0, 348068502358, 915326119496, 496117642630, 39977461155, 0, 0] := by
  rw [show D2M8K2.u5327 = KTree.node D2M8K2.t5334 (nat_lit 11602316) (nat_lit 3222256475) (nat_lit 0) D2M8K2.t5335 from rfl, totK_node, tot5334, tot5335]
  decide +kernel

theorem arows5330 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5330 = true := by
  rw [show D2M8K2.u5330 = KTree.node D2M8K2.t5336 (nat_lit 11603850) (nat_lit 3824912076) (nat_lit 0) D2M8K2.t5337 from rfl, allE_node, rows5336, irow5330, rows5337]
  all_goals rfl

theorem atot5330 : totK PD2M8K2 D2M8K2.u5330 = [0, 0, 88698579362, 581108028712, 852078450310, 225394783121, 8235505476, 0] := by
  rw [show D2M8K2.u5330 = KTree.node D2M8K2.t5336 (nat_lit 11603850) (nat_lit 3824912076) (nat_lit 0) D2M8K2.t5337 from rfl, totK_node, tot5336, tot5337]
  decide +kernel

theorem arows5331 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5331 = true := by
  rw [show D2M8K2.u5331 = KTree.node D2M8K2.t5338 (nat_lit 11605755) (nat_lit 3667210038) (nat_lit 0) D2M8K2.t5339 from rfl, allE_node, rows5338, irow5331, rows5339]
  all_goals rfl

theorem atot5331 : totK PD2M8K2 D2M8K2.u5331 = [0, 0, 326434470085, 903125084809, 520223686491, 64754828637, 1291861884, 0] := by
  rw [show D2M8K2.u5331 = KTree.node D2M8K2.t5338 (nat_lit 11605755) (nat_lit 3667210038) (nat_lit 0) D2M8K2.t5339 from rfl, totK_node, tot5338, tot5339]
  decide +kernel

theorem arows5333 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5333 = true := by
  rw [show D2M8K2.u5333 = KTree.node D2M8K2.t5340 (nat_lit 11608304) (nat_lit 3717254639) (nat_lit 0) D2M8K2.t5341 from rfl, allE_node, rows5340, irow5333, rows5341]
  all_goals rfl

theorem atot5333 : totK PD2M8K2 D2M8K2.u5333 = [0, 0, 171485742426, 754507206644, 746888118041, 108812980868, 1376099875, 0] := by
  rw [show D2M8K2.u5333 = KTree.node D2M8K2.t5340 (nat_lit 11608304) (nat_lit 3717254639) (nat_lit 0) D2M8K2.t5341 from rfl, totK_node, tot5340, tot5341]
  decide +kernel

theorem arows5334 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5334 = true := by
  rw [show D2M8K2.u5334 = KTree.node D2M8K2.t5342 (nat_lit 11610173) (nat_lit 2186153325) (nat_lit 0) D2M8K2.t5343 from rfl, allE_node, rows5342, irow5334, rows5343]
  all_goals rfl

theorem atot5334 : totK PD2M8K2 D2M8K2.u5334 = [0, 121950136720, 520979144774, 755758991434, 386895245330, 31352647171, 0, 0] := by
  rw [show D2M8K2.u5334 = KTree.node D2M8K2.t5342 (nat_lit 11610173) (nat_lit 2186153325) (nat_lit 0) D2M8K2.t5343 from rfl, totK_node, tot5342, tot5343]
  decide +kernel

theorem arows5339 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5339 = true := by
  rw [show D2M8K2.u5339 = KTree.node D2M8K2.t5344 (nat_lit 11654865) (nat_lit 1592790270) (nat_lit 0) D2M8K2.t5345 from rfl, allE_node, rows5344, irow5339, rows5345]
  all_goals rfl

theorem atot5339 : totK PD2M8K2 D2M8K2.u5339 = [0, 276717337871, 837455402318, 583092831115, 75638968986, 1369150432, 0, 0] := by
  rw [show D2M8K2.u5339 = KTree.node D2M8K2.t5344 (nat_lit 11654865) (nat_lit 1592790270) (nat_lit 0) D2M8K2.t5345 from rfl, totK_node, tot5344, tot5345]
  decide +kernel

theorem arows5340 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5340 = true := by
  rw [show D2M8K2.u5340 = KTree.node D2M8K2.t5346 (nat_lit 11656938) (nat_lit 3660238081) (nat_lit 0) D2M8K2.t5347 from rfl, allE_node, rows5346, irow5340, rows5347]
  all_goals rfl

theorem atot5340 : totK PD2M8K2 D2M8K2.u5340 = [0, 180575128572, 752919110596, 789896810343, 103293459327, 0, 0, 0] := by
  rw [show D2M8K2.u5340 = KTree.node D2M8K2.t5346 (nat_lit 11656938) (nat_lit 3660238081) (nat_lit 0) D2M8K2.t5347 from rfl, totK_node, tot5346, tot5347]
  decide +kernel

theorem arows5342 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5342 = true := by
  rw [show D2M8K2.u5342 = KTree.node D2M8K2.t5348 (nat_lit 11658580) (nat_lit 4015875971) (nat_lit 0) D2M8K2.t5349 from rfl, allE_node, rows5348, irow5342, rows5349]
  all_goals rfl

theorem atot5342 : totK PD2M8K2 D2M8K2.u5342 = [0, 247006746667, 766571234685, 613210321360, 190284188051, 21376388639, 0, 0] := by
  rw [show D2M8K2.u5342 = KTree.node D2M8K2.t5348 (nat_lit 11658580) (nat_lit 4015875971) (nat_lit 0) D2M8K2.t5349 from rfl, totK_node, tot5348, tot5349]
  decide +kernel

theorem arows5343 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5343 = true := by
  rw [show D2M8K2.u5343 = KTree.node D2M8K2.t5350 (nat_lit 11660046) (nat_lit 3977210588) (nat_lit 0) D2M8K2.t5351 from rfl, allE_node, rows5350, irow5343, rows5351]
  all_goals rfl

theorem atot5343 : totK PD2M8K2 D2M8K2.u5343 = [0, 83079777321, 461813594811, 856019246215, 382926075122, 16140229592, 0, 0] := by
  rw [show D2M8K2.u5343 = KTree.node D2M8K2.t5350 (nat_lit 11660046) (nat_lit 3977210588) (nat_lit 0) D2M8K2.t5351 from rfl, totK_node, tot5350, tot5351]
  decide +kernel

theorem arows5346 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5346 = true := by
  rw [show D2M8K2.u5346 = KTree.node D2M8K2.t5352 (nat_lit 11661292) (nat_lit 3939139242) (nat_lit 0) D2M8K2.t5353 from rfl, allE_node, rows5352, irow5346, rows5353]
  all_goals rfl

theorem atot5346 : totK PD2M8K2 D2M8K2.u5346 = [0, 336114626732, 924343585046, 523116799177, 39494377841, 0, 0, 0] := by
  rw [show D2M8K2.u5346 = KTree.node D2M8K2.t5352 (nat_lit 11661292) (nat_lit 3939139242) (nat_lit 0) D2M8K2.t5353 from rfl, totK_node, tot5352, tot5353]
  decide +kernel

theorem arows5347 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5347 = true := by
  rw [show D2M8K2.u5347 = KTree.node D2M8K2.t5354 (nat_lit 11662999) (nat_lit 898641841) (nat_lit 0) D2M8K2.t5355 from rfl, allE_node, rows5354, irow5347, rows5355]
  all_goals rfl

theorem atot5347 : totK PD2M8K2 D2M8K2.u5347 = [0, 64609315486, 501254530461, 904796000684, 283927568323, 11627360713, 0, 0] := by
  rw [show D2M8K2.u5347 = KTree.node D2M8K2.t5354 (nat_lit 11662999) (nat_lit 898641841) (nat_lit 0) D2M8K2.t5355 from rfl, totK_node, tot5354, tot5355]
  decide +kernel

theorem arows5349 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5349 = true := by
  rw [show D2M8K2.u5349 = KTree.node D2M8K2.t5356 (nat_lit 11664980) (nat_lit 3437397580) (nat_lit 0) D2M8K2.t5357 from rfl, allE_node, rows5356, irow5349, rows5357]
  all_goals rfl

theorem atot5349 : totK PD2M8K2 D2M8K2.u5349 = [0, 354813875211, 935561305647, 496775070131, 35693395884, 0, 0, 0] := by
  rw [show D2M8K2.u5349 = KTree.node D2M8K2.t5356 (nat_lit 11664980) (nat_lit 3437397580) (nat_lit 0) D2M8K2.t5357 from rfl, totK_node, tot5356, tot5357]
  decide +kernel

theorem arows5350 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5350 = true := by
  rw [show D2M8K2.u5350 = KTree.node D2M8K2.t5358 (nat_lit 11666685) (nat_lit 1551222957) (nat_lit 0) D2M8K2.t5359 from rfl, allE_node, rows5358, irow5350, rows5359]
  all_goals rfl

theorem atot5350 : totK PD2M8K2 D2M8K2.u5350 = [0, 18567060971, 489928773475, 957019891054, 298866382397, 11781118163, 0, 0] := by
  rw [show D2M8K2.u5350 = KTree.node D2M8K2.t5358 (nat_lit 11666685) (nat_lit 1551222957) (nat_lit 0) D2M8K2.t5359 from rfl, totK_node, tot5358, tot5359]
  decide +kernel

theorem arows5354 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5354 = true := by
  rw [show D2M8K2.u5354 = KTree.node D2M8K2.t5360 (nat_lit 11671523) (nat_lit 2849658345) (nat_lit 0) D2M8K2.t5361 from rfl, allE_node, rows5360, irow5354, rows5361]
  all_goals rfl

theorem atot5354 : totK PD2M8K2 D2M8K2.u5354 = [0, 372244867916, 937908732125, 493848784904, 39633215863, 0, 0, 0] := by
  rw [show D2M8K2.u5354 = KTree.node D2M8K2.t5360 (nat_lit 11671523) (nat_lit 2849658345) (nat_lit 0) D2M8K2.t5361 from rfl, totK_node, tot5360, tot5361]
  decide +kernel

theorem arows5355 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5355 = true := by
  rw [show D2M8K2.u5355 = KTree.node D2M8K2.t5362 (nat_lit 11673018) (nat_lit 3895382182) (nat_lit 0) D2M8K2.t5363 from rfl, allE_node, rows5362, irow5355, rows5363]
  all_goals rfl

theorem atot5355 : totK PD2M8K2 D2M8K2.u5355 = [0, 53308269301, 534172811721, 920380067110, 280392682738, 8710740030, 0, 0] := by
  rw [show D2M8K2.u5355 = KTree.node D2M8K2.t5362 (nat_lit 11673018) (nat_lit 3895382182) (nat_lit 0) D2M8K2.t5363 from rfl, totK_node, tot5362, tot5363]
  decide +kernel

theorem arows5357 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5357 = true := by
  rw [show D2M8K2.u5357 = KTree.node D2M8K2.t5364 (nat_lit 11674951) (nat_lit 2076127139) (nat_lit 0) D2M8K2.t5365 from rfl, allE_node, rows5364, irow5357, rows5365]
  all_goals rfl

theorem atot5357 : totK PD2M8K2 D2M8K2.u5357 = [0, 0, 387570322009, 950786185125, 417622908563, 22692591333, 0, 0] := by
  rw [show D2M8K2.u5357 = KTree.node D2M8K2.t5364 (nat_lit 11674951) (nat_lit 2076127139) (nat_lit 0) D2M8K2.t5365 from rfl, totK_node, tot5364, tot5365]
  decide +kernel

theorem arows5358 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5358 = true := by
  rw [show D2M8K2.u5358 = KTree.node D2M8K2.t5366 (nat_lit 11676293) (nat_lit 1707522717) (nat_lit 0) D2M8K2.t5367 from rfl, allE_node, rows5366, irow5358, rows5367]
  all_goals rfl

theorem atot5358 : totK PD2M8K2 D2M8K2.u5358 = [0, 0, 102077584784, 689449290353, 841689802587, 117914843824, 1310285577, 0] := by
  rw [show D2M8K2.u5358 = KTree.node D2M8K2.t5366 (nat_lit 11676293) (nat_lit 1707522717) (nat_lit 0) D2M8K2.t5367 from rfl, totK_node, tot5366, tot5367]
  decide +kernel

theorem arows5361 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5361 = true := by
  rw [show D2M8K2.u5361 = KTree.node D2M8K2.t5368 (nat_lit 11678658) (nat_lit 930401778) (nat_lit 0) D2M8K2.t5369 from rfl, allE_node, rows5368, irow5361, rows5369]
  all_goals rfl

theorem atot5361 : totK PD2M8K2 D2M8K2.u5361 = [0, 0, 388074789639, 932442207875, 483779581855, 39371504641, 0, 0] := by
  rw [show D2M8K2.u5361 = KTree.node D2M8K2.t5368 (nat_lit 11678658) (nat_lit 930401778) (nat_lit 0) D2M8K2.t5369 from rfl, totK_node, tot5368, tot5369]
  decide +kernel

theorem arows5362 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5362 = true := by
  rw [show D2M8K2.u5362 = KTree.node D2M8K2.t5370 (nat_lit 11681682) (nat_lit 2548529369) (nat_lit 0) D2M8K2.t5371 from rfl, allE_node, rows5370, irow5362, rows5371]
  all_goals rfl

theorem atot5362 : totK PD2M8K2 D2M8K2.u5362 = [0, 0, 353842316537, 910818380333, 494767906686, 42534212713, 0, 0] := by
  rw [show D2M8K2.u5362 = KTree.node D2M8K2.t5370 (nat_lit 11681682) (nat_lit 2548529369) (nat_lit 0) D2M8K2.t5371 from rfl, totK_node, tot5370, tot5371]
  decide +kernel

theorem arows5364 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5364 = true := by
  rw [show D2M8K2.u5364 = KTree.node D2M8K2.t5372 (nat_lit 11683202) (nat_lit 2999827055) (nat_lit 0) D2M8K2.t5373 from rfl, allE_node, rows5372, irow5364, rows5373]
  all_goals rfl

theorem atot5364 : totK PD2M8K2 D2M8K2.u5364 = [0, 0, 97159877541, 664860611232, 817217623461, 162444824949, 4879840392, 0] := by
  rw [show D2M8K2.u5364 = KTree.node D2M8K2.t5372 (nat_lit 11683202) (nat_lit 2999827055) (nat_lit 0) D2M8K2.t5373 from rfl, totK_node, tot5372, tot5373]
  decide +kernel

theorem arows5365 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5365 = true := by
  rw [show D2M8K2.u5365 = KTree.node D2M8K2.t5374 (nat_lit 11685250) (nat_lit 3923195380) (nat_lit 0) D2M8K2.t5375 from rfl, allE_node, rows5374, irow5365, rows5375]
  all_goals rfl

theorem atot5365 : totK PD2M8K2 D2M8K2.u5365 = [0, 0, 334998697337, 892082913700, 518844352273, 47936593455, 0, 0] := by
  rw [show D2M8K2.u5365 = KTree.node D2M8K2.t5374 (nat_lit 11685250) (nat_lit 3923195380) (nat_lit 0) D2M8K2.t5375 from rfl, totK_node, tot5374, tot5375]
  decide +kernel

theorem arows5373 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5373 = true := by
  rw [show D2M8K2.u5373 = KTree.node D2M8K2.t5376 (nat_lit 11686836) (nat_lit 2652665184) (nat_lit 0) D2M8K2.t5377 from rfl, allE_node, rows5376, irow5373, rows5377]
  all_goals rfl

theorem atot5373 : totK PD2M8K2 D2M8K2.u5373 = [0, 0, 100945888900, 646036184514, 839853246497, 178358903266, 4931404646, 0] := by
  rw [show D2M8K2.u5373 = KTree.node D2M8K2.t5376 (nat_lit 11686836) (nat_lit 2652665184) (nat_lit 0) D2M8K2.t5377 from rfl, totK_node, tot5376, tot5377]
  decide +kernel

theorem arows5374 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5374 = true := by
  rw [show D2M8K2.u5374 = KTree.node D2M8K2.t5378 (nat_lit 11692258) (nat_lit 4004572508) (nat_lit 0) D2M8K2.t5379 from rfl, allE_node, rows5378, irow5374, rows5379]
  all_goals rfl

theorem atot5374 : totK PD2M8K2 D2M8K2.u5374 = [0, 0, 377841118992, 938612111328, 476685539669, 32679690692, 0, 0] := by
  rw [show D2M8K2.u5374 = KTree.node D2M8K2.t5378 (nat_lit 11692258) (nat_lit 4004572508) (nat_lit 0) D2M8K2.t5379 from rfl, totK_node, tot5378, tot5379]
  decide +kernel

theorem arows5376 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5376 = true := by
  rw [show D2M8K2.u5376 = KTree.node D2M8K2.t5380 (nat_lit 11693767) (nat_lit 1474631476) (nat_lit 0) D2M8K2.t5381 from rfl, allE_node, rows5380, irow5376, rows5381]
  all_goals rfl

theorem atot5376 : totK PD2M8K2 D2M8K2.u5376 = [0, 0, 49142996948, 550388760236, 898723745360, 253768589382, 8424427256, 0] := by
  rw [show D2M8K2.u5376 = KTree.node D2M8K2.t5380 (nat_lit 11693767) (nat_lit 1474631476) (nat_lit 0) D2M8K2.t5381 from rfl, totK_node, tot5380, tot5381]
  decide +kernel

theorem arows5377 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5377 = true := by
  rw [show D2M8K2.u5377 = KTree.node D2M8K2.t5382 (nat_lit 11695729) (nat_lit 1507317077) (nat_lit 0) D2M8K2.t5383 from rfl, allE_node, rows5382, irow5377, rows5383]
  all_goals rfl

theorem atot5377 : totK PD2M8K2 D2M8K2.u5377 = [0, 0, 309863805053, 791401454231, 509942787549, 140695425120, 13326740810, 0] := by
  rw [show D2M8K2.u5377 = KTree.node D2M8K2.t5382 (nat_lit 11695729) (nat_lit 1507317077) (nat_lit 0) D2M8K2.t5383 from rfl, totK_node, tot5382, tot5383]
  decide +kernel

theorem arows5380 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5380 = true := by
  rw [show D2M8K2.u5380 = KTree.node D2M8K2.t5384 (nat_lit 11696977) (nat_lit 1558578335) (nat_lit 0) D2M8K2.t5385 from rfl, allE_node, rows5384, irow5380, rows5385]
  all_goals rfl

theorem atot5380 : totK PD2M8K2 D2M8K2.u5380 = [0, 0, 103314565783, 711257680031, 814061420122, 126244139205, 1369150432, 0] := by
  rw [show D2M8K2.u5380 = KTree.node D2M8K2.t5384 (nat_lit 11696977) (nat_lit 1558578335) (nat_lit 0) D2M8K2.t5385 from rfl, totK_node, tot5384, tot5385]
  decide +kernel

theorem arows5381 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5381 = true := by
  rw [show D2M8K2.u5381 = KTree.node D2M8K2.t5386 (nat_lit 11702638) (nat_lit 3865195220) (nat_lit 0) D2M8K2.t5387 from rfl, allE_node, rows5386, irow5381, rows5387]
  all_goals rfl

theorem atot5381 : totK PD2M8K2 D2M8K2.u5381 = [0, 0, 399862894737, 933456282771, 446793484279, 31011256633, 0, 0] := by
  rw [show D2M8K2.u5381 = KTree.node D2M8K2.t5386 (nat_lit 11702638) (nat_lit 3865195220) (nat_lit 0) D2M8K2.t5387 from rfl, totK_node, tot5386, tot5387]
  decide +kernel

theorem arows5383 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5383 = true := by
  rw [show D2M8K2.u5383 = KTree.node D2M8K2.t5388 (nat_lit 11706416) (nat_lit 3779522820) (nat_lit 0) D2M8K2.t5389 from rfl, allE_node, rows5388, irow5383, rows5389]
  all_goals rfl

theorem atot5383 : totK PD2M8K2 D2M8K2.u5383 = [0, 0, 400106457751, 949739627660, 444173344996, 26379869784, 0, 0] := by
  rw [show D2M8K2.u5383 = KTree.node D2M8K2.t5388 (nat_lit 11706416) (nat_lit 3779522820) (nat_lit 0) D2M8K2.t5389 from rfl, totK_node, tot5388, tot5389]
  decide +kernel

theorem arows5384 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5384 = true := by
  rw [show D2M8K2.u5384 = KTree.node D2M8K2.t5390 (nat_lit 11713001) (nat_lit 1797739736) (nat_lit 0) D2M8K2.t5391 from rfl, allE_node, rows5390, irow5384, rows5391]
  all_goals rfl

theorem atot5384 : totK PD2M8K2 D2M8K2.u5384 = [0, 0, 398868743808, 946159499306, 445450763677, 27578426022, 0, 0] := by
  rw [show D2M8K2.u5384 = KTree.node D2M8K2.t5390 (nat_lit 11713001) (nat_lit 1797739736) (nat_lit 0) D2M8K2.t5391 from rfl, totK_node, tot5390, tot5391]
  decide +kernel

theorem arows5388 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5388 = true := by
  rw [show D2M8K2.u5388 = KTree.node D2M8K2.t5392 (nat_lit 11740655) (nat_lit 2144643705) (nat_lit 0) D2M8K2.t5393 from rfl, allE_node, rows5392, irow5388, rows5393]
  all_goals rfl

theorem atot5388 : totK PD2M8K2 D2M8K2.u5388 = [0, 0, 342585719654, 908925417055, 544693976199, 51148430743, 0, 0] := by
  rw [show D2M8K2.u5388 = KTree.node D2M8K2.t5392 (nat_lit 11740655) (nat_lit 2144643705) (nat_lit 0) D2M8K2.t5393 from rfl, totK_node, tot5392, tot5393]
  decide +kernel

theorem arows5389 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5389 = true := by
  rw [show D2M8K2.u5389 = KTree.node D2M8K2.t5394 (nat_lit 11742150) (nat_lit 3783624472) (nat_lit 0) D2M8K2.t5395 from rfl, allE_node, rows5394, irow5389, rows5395]
  all_goals rfl

theorem atot5389 : totK PD2M8K2 D2M8K2.u5389 = [0, 0, 126440840104, 622271966938, 762901318507, 292824905357, 25330798048, 0] := by
  rw [show D2M8K2.u5389 = KTree.node D2M8K2.t5394 (nat_lit 11742150) (nat_lit 3783624472) (nat_lit 0) D2M8K2.t5395 from rfl, totK_node, tot5394, tot5395]
  decide +kernel

theorem arows5391 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5391 = true := by
  rw [show D2M8K2.u5391 = KTree.node D2M8K2.t5396 (nat_lit 11743375) (nat_lit 2091562265) (nat_lit 0) D2M8K2.t5397 from rfl, allE_node, rows5396, irow5391, rows5397]
  all_goals rfl

theorem atot5391 : totK PD2M8K2 D2M8K2.u5391 = [0, 0, 154156719226, 593521387442, 773244801080, 290686700743, 12169858900, 0] := by
  rw [show D2M8K2.u5391 = KTree.node D2M8K2.t5396 (nat_lit 11743375) (nat_lit 2091562265) (nat_lit 0) D2M8K2.t5397 from rfl, totK_node, tot5396, tot5397]
  decide +kernel

theorem arows5392 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5392 = true := by
  rw [show D2M8K2.u5392 = KTree.node D2M8K2.t5398 (nat_lit 11744968) (nat_lit 3841397406) (nat_lit 0) D2M8K2.t5399 from rfl, allE_node, rows5398, irow5392, rows5399]
  all_goals rfl

theorem atot5392 : totK PD2M8K2 D2M8K2.u5392 = [0, 0, 258330629400, 822607690195, 640881472860, 89473978818, 0, 0] := by
  rw [show D2M8K2.u5392 = KTree.node D2M8K2.t5398 (nat_lit 11744968) (nat_lit 3841397406) (nat_lit 0) D2M8K2.t5399 from rfl, totK_node, tot5398, tot5399]
  decide +kernel

theorem arows5395 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5395 = true := by
  rw [show D2M8K2.u5395 = KTree.node D2M8K2.t5400 (nat_lit 11746728) (nat_lit 2804612754) (nat_lit 0) D2M8K2.t5401 from rfl, allE_node, rows5400, irow5395, rows5401]
  all_goals rfl

theorem atot5395 : totK PD2M8K2 D2M8K2.u5395 = [0, 0, 175195872452, 665946723340, 760937333771, 202245599811, 6583681375, 0] := by
  rw [show D2M8K2.u5395 = KTree.node D2M8K2.t5400 (nat_lit 11746728) (nat_lit 2804612754) (nat_lit 0) D2M8K2.t5401 from rfl, totK_node, tot5400, tot5401]
  decide +kernel

theorem arows5396 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5396 = true := by
  rw [show D2M8K2.u5396 = KTree.node D2M8K2.t5402 (nat_lit 11748456) (nat_lit 3446532554) (nat_lit 0) D2M8K2.t5403 from rfl, allE_node, rows5402, irow5396, rows5403]
  all_goals rfl

theorem atot5396 : totK PD2M8K2 D2M8K2.u5396 = [0, 0, 237548696723, 821743887950, 668035210526, 89144612174, 0, 0] := by
  rw [show D2M8K2.u5396 = KTree.node D2M8K2.t5402 (nat_lit 11748456) (nat_lit 3446532554) (nat_lit 0) D2M8K2.t5403 from rfl, totK_node, tot5402, tot5403]
  decide +kernel

theorem arows5398 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5398 = true := by
  rw [show D2M8K2.u5398 = KTree.node D2M8K2.t5404 (nat_lit 11750235) (nat_lit 3626850800) (nat_lit 0) D2M8K2.t5405 from rfl, allE_node, rows5404, irow5398, rows5405]
  all_goals rfl

theorem atot5398 : totK PD2M8K2 D2M8K2.u5398 = [0, 0, 173220819551, 651741762559, 768595223930, 213859307676, 6656488309, 0] := by
  rw [show D2M8K2.u5398 = KTree.node D2M8K2.t5404 (nat_lit 11750235) (nat_lit 3626850800) (nat_lit 0) D2M8K2.t5405 from rfl, totK_node, tot5404, tot5405]
  decide +kernel

theorem arows5399 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5399 = true := by
  rw [show D2M8K2.u5399 = KTree.node D2M8K2.t5406 (nat_lit 11752480) (nat_lit 3729444138) (nat_lit 0) D2M8K2.t5407 from rfl, allE_node, rows5406, irow5399, rows5407]
  all_goals rfl

theorem atot5399 : totK PD2M8K2 D2M8K2.u5399 = [0, 0, 171128825911, 789872189676, 771991618557, 105032759704, 0, 0] := by
  rw [show D2M8K2.u5399 = KTree.node D2M8K2.t5406 (nat_lit 11752480) (nat_lit 3729444138) (nat_lit 0) D2M8K2.t5407 from rfl, totK_node, tot5406, tot5407]
  decide +kernel

theorem arows5404 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5404 = true := by
  rw [show D2M8K2.u5404 = KTree.node D2M8K2.t5408 (nat_lit 11754450) (nat_lit 2111622844) (nat_lit 0) D2M8K2.t5409 from rfl, allE_node, rows5408, irow5404, rows5409]
  all_goals rfl

theorem atot5404 : totK PD2M8K2 D2M8K2.u5404 = [0, 0, 367533216935, 894532859447, 488696355480, 67705663114, 1429815836, 0] := by
  rw [show D2M8K2.u5404 = KTree.node D2M8K2.t5408 (nat_lit 11754450) (nat_lit 2111622844) (nat_lit 0) D2M8K2.t5409 from rfl, totK_node, tot5408, tot5409]
  decide +kernel

theorem arows5405 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5405 = true := by
  rw [show D2M8K2.u5405 = KTree.node D2M8K2.t5410 (nat_lit 11755989) (nat_lit 1334133918) (nat_lit 0) D2M8K2.t5411 from rfl, allE_node, rows5410, irow5405, rows5411]
  all_goals rfl

theorem atot5405 : totK PD2M8K2 D2M8K2.u5405 = [0, 0, 56561114677, 553812819376, 909855981922, 259490010118, 4845320938, 0] := by
  rw [show D2M8K2.u5405 = KTree.node D2M8K2.t5410 (nat_lit 11755989) (nat_lit 1334133918) (nat_lit 0) D2M8K2.t5411 from rfl, totK_node, tot5410, tot5411]
  decide +kernel

theorem arows5407 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5407 = true := by
  rw [show D2M8K2.u5407 = KTree.node D2M8K2.t5412 (nat_lit 11778669) (nat_lit 1388824972) (nat_lit 0) D2M8K2.t5413 from rfl, allE_node, rows5412, irow5407, rows5413]
  all_goals rfl

theorem atot5407 : totK PD2M8K2 D2M8K2.u5407 = [0, 0, 375647630150, 809916205111, 465803328535, 141190529657, 11406585291, 0] := by
  rw [show D2M8K2.u5407 = KTree.node D2M8K2.t5412 (nat_lit 11778669) (nat_lit 1388824972) (nat_lit 0) D2M8K2.t5413 from rfl, totK_node, tot5412, tot5413]
  decide +kernel

theorem arows5408 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5408 = true := by
  rw [show D2M8K2.u5408 = KTree.node D2M8K2.t5414 (nat_lit 11780957) (nat_lit 2244757439) (nat_lit 0) D2M8K2.t5415 from rfl, allE_node, rows5414, irow5408, rows5415]
  all_goals rfl

theorem atot5408 : totK PD2M8K2 D2M8K2.u5408 = [0, 0, 122823664054, 701360258187, 842114497759, 136401531504, 1369150432, 0] := by
  rw [show D2M8K2.u5408 = KTree.node D2M8K2.t5414 (nat_lit 11780957) (nat_lit 2244757439) (nat_lit 0) D2M8K2.t5415 from rfl, totK_node, tot5414, tot5415]
  decide +kernel

theorem arows5411 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5411 = true := by
  rw [show D2M8K2.u5411 = KTree.node D2M8K2.t5416 (nat_lit 11782758) (nat_lit 3528864611) (nat_lit 0) D2M8K2.t5417 from rfl, allE_node, rows5416, irow5411, rows5417]
  all_goals rfl

theorem atot5411 : totK PD2M8K2 D2M8K2.u5411 = [0, 0, 297349758948, 901371396027, 576901453412, 62988687191, 0, 0] := by
  rw [show D2M8K2.u5411 = KTree.node D2M8K2.t5416 (nat_lit 11782758) (nat_lit 3528864611) (nat_lit 0) D2M8K2.t5417 from rfl, totK_node, tot5416, tot5417]
  decide +kernel

theorem arows5412 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5412 = true := by
  rw [show D2M8K2.u5412 = KTree.node D2M8K2.t5418 (nat_lit 11784326) (nat_lit 2611831190) (nat_lit 0) D2M8K2.t5419 from rfl, allE_node, rows5418, irow5412, rows5419]
  all_goals rfl

theorem atot5412 : totK PD2M8K2 D2M8K2.u5412 = [0, 0, 29588901100, 361001844515, 894955459656, 474740907840, 32764831815, 0] := by
  rw [show D2M8K2.u5412 = KTree.node D2M8K2.t5418 (nat_lit 11784326) (nat_lit 2611831190) (nat_lit 0) D2M8K2.t5419 from rfl, totK_node, tot5418, tot5419]
  decide +kernel

theorem arows5414 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5414 = true := by
  rw [show D2M8K2.u5414 = KTree.node D2M8K2.t5420 (nat_lit 11785587) (nat_lit 3673020845) (nat_lit 0) D2M8K2.t5421 from rfl, allE_node, rows5420, irow5414, rows5421]
  all_goals rfl

theorem atot5414 : totK PD2M8K2 D2M8K2.u5414 = [0, 0, 381609985257, 939472096904, 461330738798, 35000060844, 0, 0] := by
  rw [show D2M8K2.u5414 = KTree.node D2M8K2.t5420 (nat_lit 11785587) (nat_lit 3673020845) (nat_lit 0) D2M8K2.t5421 from rfl, totK_node, tot5420, tot5421]
  decide +kernel

theorem arows5415 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5415 = true := by
  rw [show D2M8K2.u5415 = KTree.node D2M8K2.t5422 (nat_lit 11787272) (nat_lit 3551904898) (nat_lit 0) D2M8K2.t5423 from rfl, allE_node, rows5422, irow5415, rows5423]
  all_goals rfl

theorem atot5415 : totK PD2M8K2 D2M8K2.u5415 = [0, 0, 19433589518, 526284441464, 946934677133, 273067632755, 9483552028, 0] := by
  rw [show D2M8K2.u5415 = KTree.node D2M8K2.t5422 (nat_lit 11787272) (nat_lit 3551904898) (nat_lit 0) D2M8K2.t5423 from rfl, totK_node, tot5422, tot5423]
  decide +kernel

theorem arows5419 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5419 = true := by
  rw [show D2M8K2.u5419 = KTree.node D2M8K2.t5424 (nat_lit 11792570) (nat_lit 3901167752) (nat_lit 0) D2M8K2.t5425 from rfl, allE_node, rows5424, irow5419, rows5425]
  all_goals rfl

theorem atot5419 : totK PD2M8K2 D2M8K2.u5419 = [0, 0, 325021365497, 898222582639, 563778245125, 53367833729, 0, 0] := by
  rw [show D2M8K2.u5419 = KTree.node D2M8K2.t5424 (nat_lit 11792570) (nat_lit 3901167752) (nat_lit 0) D2M8K2.t5425 from rfl, totK_node, tot5424, tot5425]
  decide +kernel

theorem arows5420 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5420 = true := by
  rw [show D2M8K2.u5420 = KTree.node D2M8K2.t5426 (nat_lit 11795459) (nat_lit 2975440576) (nat_lit 0) D2M8K2.t5427 from rfl, allE_node, rows5426, irow5420, rows5427]
  all_goals rfl

theorem atot5420 : totK PD2M8K2 D2M8K2.u5420 = [0, 0, 259060026118, 782160247631, 669713593613, 106511943424, 1394496256, 0] := by
  rw [show D2M8K2.u5420 = KTree.node D2M8K2.t5426 (nat_lit 11795459) (nat_lit 2975440576) (nat_lit 0) D2M8K2.t5427 from rfl, totK_node, tot5426, tot5427]
  decide +kernel

theorem arows5422 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5422 = true := by
  rw [show D2M8K2.u5422 = KTree.node D2M8K2.t5428 (nat_lit 11796974) (nat_lit 2609194944) (nat_lit 0) D2M8K2.t5429 from rfl, allE_node, rows5428, irow5422, rows5429]
  all_goals rfl

theorem atot5422 : totK PD2M8K2 D2M8K2.u5422 = [0, 0, 164043053881, 743595445828, 756404656196, 134182412299, 1268739303, 0] := by
  rw [show D2M8K2.u5422 = KTree.node D2M8K2.t5428 (nat_lit 11796974) (nat_lit 2609194944) (nat_lit 0) D2M8K2.t5429 from rfl, totK_node, tot5428, tot5429]
  decide +kernel

theorem arows5423 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5423 = true := by
  rw [show D2M8K2.u5423 = KTree.node D2M8K2.t5430 (nat_lit 11798697) (nat_lit 958186622) (nat_lit 0) D2M8K2.t5431 from rfl, allE_node, rows5430, irow5423, rows5431]
  all_goals rfl

theorem atot5423 : totK PD2M8K2 D2M8K2.u5423 = [0, 0, 0, 354350973604, 963919624534, 414644450438, 19458756099, 0] := by
  rw [show D2M8K2.u5423 = KTree.node D2M8K2.t5430 (nat_lit 11798697) (nat_lit 958186622) (nat_lit 0) D2M8K2.t5431 from rfl, totK_node, tot5430, tot5431]
  decide +kernel

theorem arows5426 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5426 = true := by
  rw [show D2M8K2.u5426 = KTree.node D2M8K2.t5432 (nat_lit 11802702) (nat_lit 3767989680) (nat_lit 0) D2M8K2.t5433 from rfl, allE_node, rows5432, irow5426, rows5433]
  all_goals rfl

theorem atot5426 : totK PD2M8K2 D2M8K2.u5426 = [0, 0, 0, 521840531892, 951471479146, 333191106037, 14147640871, 0] := by
  rw [show D2M8K2.u5426 = KTree.node D2M8K2.t5432 (nat_lit 11802702) (nat_lit 3767989680) (nat_lit 0) D2M8K2.t5433 from rfl, totK_node, tot5432, tot5433]
  decide +kernel

theorem arows5427 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5427 = true := by
  rw [show D2M8K2.u5427 = KTree.node D2M8K2.t5434 (nat_lit 11806043) (nat_lit 2843911894) (nat_lit 0) D2M8K2.t5435 from rfl, allE_node, rows5434, irow5427, rows5435]
  all_goals rfl

theorem atot5427 : totK PD2M8K2 D2M8K2.u5427 = [0, 0, 0, 395995508653, 948083068465, 419251676141, 25479295312, 0] := by
  rw [show D2M8K2.u5427 = KTree.node D2M8K2.t5434 (nat_lit 11806043) (nat_lit 2843911894) (nat_lit 0) D2M8K2.t5435 from rfl, totK_node, tot5434, tot5435]
  decide +kernel

theorem arows5429 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5429 = true := by
  rw [show D2M8K2.u5429 = KTree.node D2M8K2.t5436 (nat_lit 11807754) (nat_lit 1978234713) (nat_lit 0) D2M8K2.t5437 from rfl, allE_node, rows5436, irow5429, rows5437]
  all_goals rfl

theorem atot5429 : totK PD2M8K2 D2M8K2.u5429 = [0, 0, 0, 136167415747, 770873631959, 737197608935, 111776948763, 1501162176] := by
  rw [show D2M8K2.u5429 = KTree.node D2M8K2.t5436 (nat_lit 11807754) (nat_lit 1978234713) (nat_lit 0) D2M8K2.t5437 from rfl, totK_node, tot5436, tot5437]
  decide +kernel

theorem arows5430 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5430 = true := by
  rw [show D2M8K2.u5430 = KTree.node D2M8K2.t5438 (nat_lit 11813859) (nat_lit 3679374307) (nat_lit 0) D2M8K2.t5439 from rfl, allE_node, rows5438, irow5430, rows5439]
  all_goals rfl

theorem atot5430 : totK PD2M8K2 D2M8K2.u5430 = [0, 0, 0, 473238212565, 977437481275, 308736134046, 11159088779, 0] := by
  rw [show D2M8K2.u5430 = KTree.node D2M8K2.t5438 (nat_lit 11813859) (nat_lit 3679374307) (nat_lit 0) D2M8K2.t5439 from rfl, totK_node, tot5438, tot5439]
  decide +kernel

theorem arows5436 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5436 = true := by
  rw [show D2M8K2.u5436 = KTree.node D2M8K2.t5440 (nat_lit 11817551) (nat_lit 2161348375) (nat_lit 0) D2M8K2.t5441 from rfl, allE_node, rows5440, irow5436, rows5441]
  all_goals rfl

theorem atot5436 : totK PD2M8K2 D2M8K2.u5436 = [0, 0, 156214179190, 530056972901, 740523861722, 341002428600, 21769257112, 0] := by
  rw [show D2M8K2.u5436 = KTree.node D2M8K2.t5440 (nat_lit 11817551) (nat_lit 2161348375) (nat_lit 0) D2M8K2.t5441 from rfl, totK_node, tot5440, tot5441]
  decide +kernel

theorem arows5437 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5437 = true := by
  rw [show D2M8K2.u5437 = KTree.node D2M8K2.t5442 (nat_lit 11821183) (nat_lit 2407249918) (nat_lit 0) D2M8K2.t5443 from rfl, allE_node, rows5442, irow5437, rows5443]
  all_goals rfl

theorem atot5437 : totK PD2M8K2 D2M8K2.u5437 = [0, 0, 219541710748, 781168094755, 689478712437, 101504088599, 1369150432, 0] := by
  rw [show D2M8K2.u5437 = KTree.node D2M8K2.t5442 (nat_lit 11821183) (nat_lit 2407249918) (nat_lit 0) D2M8K2.t5443 from rfl, totK_node, tot5442, tot5443]
  decide +kernel

theorem arows5439 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5439 = true := by
  rw [show D2M8K2.u5439 = KTree.node D2M8K2.t5444 (nat_lit 11823652) (nat_lit 3753750724) (nat_lit 0) D2M8K2.t5445 from rfl, allE_node, rows5444, irow5439, rows5445]
  all_goals rfl

theorem atot5439 : totK PD2M8K2 D2M8K2.u5439 = [0, 0, 331786587939, 894408904233, 569280375192, 57042750805, 0, 0] := by
  rw [show D2M8K2.u5439 = KTree.node D2M8K2.t5444 (nat_lit 11823652) (nat_lit 3753750724) (nat_lit 0) D2M8K2.t5445 from rfl, totK_node, tot5444, tot5445]
  decide +kernel

theorem arows5440 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5440 = true := by
  rw [show D2M8K2.u5440 = KTree.node D2M8K2.t5446 (nat_lit 11825187) (nat_lit 3687294742) (nat_lit 0) D2M8K2.t5447 from rfl, allE_node, rows5446, irow5440, rows5447]
  all_goals rfl

theorem atot5440 : totK PD2M8K2 D2M8K2.u5440 = [0, 0, 88459214294, 541041136093, 816238721313, 340889550145, 24731817083, 0] := by
  rw [show D2M8K2.u5440 = KTree.node D2M8K2.t5446 (nat_lit 11825187) (nat_lit 3687294742) (nat_lit 0) D2M8K2.t5447 from rfl, totK_node, tot5446, tot5447]
  decide +kernel

theorem arows5443 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5443 = true := by
  rw [show D2M8K2.u5443 = KTree.node D2M8K2.t5448 (nat_lit 11829980) (nat_lit 3335255375) (nat_lit 0) D2M8K2.t5449 from rfl, allE_node, rows5448, irow5443, rows5449]
  all_goals rfl

theorem atot5443 : totK PD2M8K2 D2M8K2.u5443 = [0, 0, 235034065969, 697993737840, 670734551860, 207316517553, 8073768252, 0] := by
  rw [show D2M8K2.u5443 = KTree.node D2M8K2.t5448 (nat_lit 11829980) (nat_lit 3335255375) (nat_lit 0) D2M8K2.t5449 from rfl, totK_node, tot5448, tot5449]
  decide +kernel

theorem arows5444 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5444 = true := by
  rw [show D2M8K2.u5444 = KTree.node D2M8K2.t5450 (nat_lit 11831464) (nat_lit 3580321257) (nat_lit 0) D2M8K2.t5451 from rfl, allE_node, rows5450, irow5444, rows5451]
  all_goals rfl

theorem atot5444 : totK PD2M8K2 D2M8K2.u5444 = [0, 0, 196755543613, 784635646464, 705009251787, 111659189116, 1198073392, 0] := by
  rw [show D2M8K2.u5444 = KTree.node D2M8K2.t5450 (nat_lit 11831464) (nat_lit 3580321257) (nat_lit 0) D2M8K2.t5451 from rfl, totK_node, tot5450, tot5451]
  decide +kernel

theorem arows5446 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5446 = true := by
  rw [show D2M8K2.u5446 = KTree.node D2M8K2.t5452 (nat_lit 11833148) (nat_lit 2793270257) (nat_lit 0) D2M8K2.t5453 from rfl, allE_node, rows5452, irow5446, rows5453]
  all_goals rfl

theorem atot5446 : totK PD2M8K2 D2M8K2.u5446 = [0, 0, 239202547983, 681605644835, 689763486546, 204796422006, 8379551475, 0] := by
  rw [show D2M8K2.u5446 = KTree.node D2M8K2.t5452 (nat_lit 11833148) (nat_lit 2793270257) (nat_lit 0) D2M8K2.t5453 from rfl, totK_node, tot5452, tot5453]
  decide +kernel

theorem arows5447 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5447 = true := by
  rw [show D2M8K2.u5447 = KTree.node D2M8K2.t5454 (nat_lit 11835476) (nat_lit 3681043666) (nat_lit 0) D2M8K2.t5455 from rfl, allE_node, rows5454, irow5447, rows5455]
  all_goals rfl

theorem atot5447 : totK PD2M8K2 D2M8K2.u5447 = [0, 0, 167118803586, 757534595708, 758384450567, 116778293089, 1430229726, 0] := by
  rw [show D2M8K2.u5447 = KTree.node D2M8K2.t5454 (nat_lit 11835476) (nat_lit 3681043666) (nat_lit 0) D2M8K2.t5455 from rfl, totK_node, tot5454, tot5455]
  decide +kernel

theorem arows5451 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5451 = true := by
  rw [show D2M8K2.u5451 = KTree.node D2M8K2.t5456 (nat_lit 11837585) (nat_lit 2139162495) (nat_lit 0) D2M8K2.t5457 from rfl, allE_node, rows5456, irow5451, rows5457]
  all_goals rfl

theorem atot5451 : totK PD2M8K2 D2M8K2.u5451 = [0, 0, 342011648963, 925407680321, 521890571303, 41468474959, 0, 0] := by
  rw [show D2M8K2.u5451 = KTree.node D2M8K2.t5456 (nat_lit 11837585) (nat_lit 2139162495) (nat_lit 0) D2M8K2.t5457 from rfl, totK_node, tot5456, tot5457]
  decide +kernel

theorem arows5452 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5452 = true := by
  rw [show D2M8K2.u5452 = KTree.node D2M8K2.t5458 (nat_lit 11839278) (nat_lit 2686527156) (nat_lit 0) D2M8K2.t5459 from rfl, allE_node, rows5458, irow5452, rows5459]
  all_goals rfl

theorem atot5452 : totK PD2M8K2 D2M8K2.u5452 = [0, 0, 0, 436745493874, 973818270520, 349224979643, 11413764339, 0] := by
  rw [show D2M8K2.u5452 = KTree.node D2M8K2.t5458 (nat_lit 11839278) (nat_lit 2686527156) (nat_lit 0) D2M8K2.t5459 from rfl, totK_node, tot5458, tot5459]
  decide +kernel

theorem arows5454 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5454 = true := by
  rw [show D2M8K2.u5454 = KTree.node D2M8K2.t5460 (nat_lit 11841384) (nat_lit 3443070030) (nat_lit 0) D2M8K2.t5461 from rfl, allE_node, rows5460, irow5454, rows5461]
  all_goals rfl

theorem atot5454 : totK PD2M8K2 D2M8K2.u5454 = [0, 0, 0, 463534725783, 965906769437, 340744853507, 16453917952, 0] := by
  rw [show D2M8K2.u5454 = KTree.node D2M8K2.t5460 (nat_lit 11841384) (nat_lit 3443070030) (nat_lit 0) D2M8K2.t5461 from rfl, totK_node, tot5460, tot5461]
  decide +kernel

theorem arows5455 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5455 = true := by
  rw [show D2M8K2.u5455 = KTree.node D2M8K2.t5462 (nat_lit 11845190) (nat_lit 4151327674) (nat_lit 0) D2M8K2.t5463 from rfl, allE_node, rows5462, irow5455, rows5463]
  all_goals rfl

theorem atot5455 : totK PD2M8K2 D2M8K2.u5455 = [0, 0, 0, 471580263085, 960535394275, 362178143987, 15601098855, 0] := by
  rw [show D2M8K2.u5455 = KTree.node D2M8K2.t5462 (nat_lit 11845190) (nat_lit 4151327674) (nat_lit 0) D2M8K2.t5463 from rfl, totK_node, tot5462, tot5463]
  decide +kernel

theorem arows5458 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5458 = true := by
  rw [show D2M8K2.u5458 = KTree.node D2M8K2.t5464 (nat_lit 11851924) (nat_lit 1489340181) (nat_lit 2056) D2M8K2.t5465 from rfl, allE_node, rows5464, irow5458, rows5465]
  all_goals rfl

theorem atot5458 : totK PD2M8K2 D2M8K2.u5458 = [0, 0, 0, 276740366290, 898468000633, 566259198654, 43684762418, 0] := by
  rw [show D2M8K2.u5458 = KTree.node D2M8K2.t5464 (nat_lit 11851924) (nat_lit 1489340181) (nat_lit 2056) D2M8K2.t5465 from rfl, totK_node, tot5464, tot5465]
  decide +kernel

theorem arows5459 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5459 = true := by
  rw [show D2M8K2.u5459 = KTree.node D2M8K2.t5466 (nat_lit 11854201) (nat_lit 1501233833) (nat_lit 0) D2M8K2.t5467 from rfl, allE_node, rows5466, irow5459, rows5467]
  all_goals rfl

theorem atot5459 : totK PD2M8K2 D2M8K2.u5459 = [0, 0, 0, 353340385599, 804330363550, 521260075065, 87598966713, 1510868091] := by
  rw [show D2M8K2.u5459 = KTree.node D2M8K2.t5466 (nat_lit 11854201) (nat_lit 1501233833) (nat_lit 0) D2M8K2.t5467 from rfl, totK_node, tot5466, tot5467]
  decide +kernel

theorem arows5461 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5461 = true := by
  rw [show D2M8K2.u5461 = KTree.node D2M8K2.t5468 (nat_lit 11858257) (nat_lit 1511483226) (nat_lit 0) D2M8K2.t5469 from rfl, allE_node, rows5468, irow5461, rows5469]
  all_goals rfl

theorem atot5461 : totK PD2M8K2 D2M8K2.u5461 = [0, 0, 0, 383336205732, 958725319644, 432578826772, 19467100881, 0] := by
  rw [show D2M8K2.u5461 = KTree.node D2M8K2.t5468 (nat_lit 11858257) (nat_lit 1511483226) (nat_lit 0) D2M8K2.t5469 from rfl, totK_node, tot5468, tot5469]
  decide +kernel

theorem arows5462 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5462 = true := by
  rw [show D2M8K2.u5462 = KTree.node D2M8K2.t5470 (nat_lit 11903308) (nat_lit 3902263508) (nat_lit 0) D2M8K2.t5471 from rfl, allE_node, rows5470, irow5462, rows5471]
  all_goals rfl

theorem atot5462 : totK PD2M8K2 D2M8K2.u5462 = [0, 0, 394317118174, 901301638294, 410502530850, 84328978169, 10848362472, 0] := by
  rw [show D2M8K2.u5462 = KTree.node D2M8K2.t5470 (nat_lit 11903308) (nat_lit 3902263508) (nat_lit 0) D2M8K2.t5471 from rfl, totK_node, tot5470, tot5471]
  decide +kernel

theorem arows5467 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5467 = true := by
  rw [show D2M8K2.u5467 = KTree.node D2M8K2.t5472 (nat_lit 11905199) (nat_lit 2180194614) (nat_lit 0) D2M8K2.t5473 from rfl, allE_node, rows5472, irow5467, rows5473]
  all_goals rfl

theorem atot5467 : totK PD2M8K2 D2M8K2.u5467 = [0, 0, 126523862594, 680073655525, 855704267493, 146298296906, 1369150432, 0] := by
  rw [show D2M8K2.u5467 = KTree.node D2M8K2.t5472 (nat_lit 11905199) (nat_lit 2180194614) (nat_lit 0) D2M8K2.t5473 from rfl, totK_node, tot5472, tot5473]
  decide +kernel

theorem arows5468 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5468 = true := by
  rw [show D2M8K2.u5468 = KTree.node D2M8K2.t5474 (nat_lit 11907136) (nat_lit 3720816941) (nat_lit 0) D2M8K2.t5475 from rfl, allE_node, rows5474, irow5468, rows5475]
  all_goals rfl

theorem atot5468 : totK PD2M8K2 D2M8K2.u5468 = [0, 0, 301058012645, 909395561250, 562628447709, 51641552047, 0, 0] := by
  rw [show D2M8K2.u5468 = KTree.node D2M8K2.t5474 (nat_lit 11907136) (nat_lit 3720816941) (nat_lit 0) D2M8K2.t5475 from rfl, totK_node, tot5474, tot5475]
  decide +kernel

theorem arows5470 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5470 = true := by
  rw [show D2M8K2.u5470 = KTree.node D2M8K2.t5476 (nat_lit 11908639) (nat_lit 2354506643) (nat_lit 0) D2M8K2.t5477 from rfl, allE_node, rows5476, irow5470, rows5477]
  all_goals rfl

theorem atot5470 : totK PD2M8K2 D2M8K2.u5470 = [0, 0, 0, 341137534348, 949322394215, 476962912628, 25975903238, 0] := by
  rw [show D2M8K2.u5470 = KTree.node D2M8K2.t5476 (nat_lit 11908639) (nat_lit 2354506643) (nat_lit 0) D2M8K2.t5477 from rfl, totK_node, tot5476, tot5477]
  decide +kernel

theorem arows5471 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5471 = true := by
  rw [show D2M8K2.u5471 = KTree.node D2M8K2.t5478 (nat_lit 11909963) (nat_lit 2888716578) (nat_lit 0) D2M8K2.t5479 from rfl, allE_node, rows5478, irow5471, rows5479]
  all_goals rfl

theorem atot5471 : totK PD2M8K2 D2M8K2.u5471 = [0, 0, 395254857413, 924741698940, 430178932174, 45501488580, 4431529051, 0] := by
  rw [show D2M8K2.u5471 = KTree.node D2M8K2.t5478 (nat_lit 11909963) (nat_lit 2888716578) (nat_lit 0) D2M8K2.t5479 from rfl, totK_node, tot5478, tot5479]
  decide +kernel

theorem arows5474 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5474 = true := by
  rw [show D2M8K2.u5474 = KTree.node D2M8K2.t5480 (nat_lit 11911696) (nat_lit 3414903850) (nat_lit 0) D2M8K2.t5481 from rfl, allE_node, rows5480, irow5474, rows5481]
  all_goals rfl

theorem atot5474 : totK PD2M8K2 D2M8K2.u5474 = [0, 0, 19498359861, 538722218307, 972751075827, 244412006043, 6480510805, 0] := by
  rw [show D2M8K2.u5474 = KTree.node D2M8K2.t5480 (nat_lit 11911696) (nat_lit 3414903850) (nat_lit 0) D2M8K2.t5481 from rfl, totK_node, tot5480, tot5481]
  decide +kernel

theorem arows5475 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5475 = true := by
  rw [show D2M8K2.u5475 = KTree.node D2M8K2.t5482 (nat_lit 11913722) (nat_lit 4226979444) (nat_lit 0) D2M8K2.t5483 from rfl, allE_node, rows5482, irow5475, rows5483]
  all_goals rfl

theorem atot5475 : totK PD2M8K2 D2M8K2.u5475 = [0, 0, 403142550542, 939153208863, 435143582742, 32200493449, 0, 0] := by
  rw [show D2M8K2.u5475 = KTree.node D2M8K2.t5482 (nat_lit 11913722) (nat_lit 4226979444) (nat_lit 0) D2M8K2.t5483 from rfl, totK_node, tot5482, tot5483]
  decide +kernel

theorem arows5477 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5477 = true := by
  rw [show D2M8K2.u5477 = KTree.node D2M8K2.t5484 (nat_lit 11915451) (nat_lit 3754049546) (nat_lit 0) D2M8K2.t5485 from rfl, allE_node, rows5484, irow5477, rows5485]
  all_goals rfl

theorem atot5477 : totK PD2M8K2 D2M8K2.u5477 = [0, 0, 15617221314, 526827892231, 973856486517, 255460159041, 6544344931, 0] := by
  rw [show D2M8K2.u5477 = KTree.node D2M8K2.t5484 (nat_lit 11915451) (nat_lit 3754049546) (nat_lit 0) D2M8K2.t5485 from rfl, totK_node, tot5484, tot5485]
  decide +kernel

theorem arows5478 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5478 = true := by
  rw [show D2M8K2.u5478 = KTree.node D2M8K2.t5486 (nat_lit 11920338) (nat_lit 2623007378) (nat_lit 0) D2M8K2.t5487 from rfl, allE_node, rows5486, irow5478, rows5487]
  all_goals rfl

theorem atot5478 : totK PD2M8K2 D2M8K2.u5478 = [0, 0, 381980739989, 938229078778, 478211718134, 37928610242, 0, 0] := by
  rw [show D2M8K2.u5478 = KTree.node D2M8K2.t5486 (nat_lit 11920338) (nat_lit 2623007378) (nat_lit 0) D2M8K2.t5487 from rfl, totK_node, tot5486, tot5487]
  decide +kernel

theorem arows5482 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5482 = true := by
  rw [show D2M8K2.u5482 = KTree.node D2M8K2.t5488 (nat_lit 11921838) (nat_lit 4028649927) (nat_lit 0) D2M8K2.t5489 from rfl, allE_node, rows5488, irow5482, rows5489]
  all_goals rfl

theorem atot5482 : totK PD2M8K2 D2M8K2.u5482 = [0, 0, 56835226932, 555003846334, 903844279169, 270667633102, 8710740030, 0] := by
  rw [show D2M8K2.u5482 = KTree.node D2M8K2.t5488 (nat_lit 11921838) (nat_lit 4028649927) (nat_lit 0) D2M8K2.t5489 from rfl, totK_node, tot5488, tot5489]
  decide +kernel

theorem arows5483 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5483 = true := by
  rw [show D2M8K2.u5483 = KTree.node D2M8K2.t5490 (nat_lit 11923471) (nat_lit 1858120047) (nat_lit 0) D2M8K2.t5491 from rfl, allE_node, rows5490, irow5483, rows5491]
  all_goals rfl

theorem atot5483 : totK PD2M8K2 D2M8K2.u5483 = [0, 0, 0, 411382370481, 953883918389, 359068897820, 17043727609, 0] := by
  rw [show D2M8K2.u5483 = KTree.node D2M8K2.t5490 (nat_lit 11923471) (nat_lit 1858120047) (nat_lit 0) D2M8K2.t5491 from rfl, totK_node, tot5490, tot5491]
  decide +kernel

theorem arows5485 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5485 = true := by
  rw [show D2M8K2.u5485 = KTree.node D2M8K2.t5492 (nat_lit 11927276) (nat_lit 3545745038) (nat_lit 0) D2M8K2.t5493 from rfl, allE_node, rows5492, irow5485, rows5493]
  all_goals rfl

theorem atot5485 : totK PD2M8K2 D2M8K2.u5485 = [0, 0, 0, 417839351617, 974097294174, 407456579720, 21752439294, 0] := by
  rw [show D2M8K2.u5485 = KTree.node D2M8K2.t5492 (nat_lit 11927276) (nat_lit 3545745038) (nat_lit 0) D2M8K2.t5493 from rfl, totK_node, tot5492, tot5493]
  decide +kernel

theorem arows5486 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5486 = true := by
  rw [show D2M8K2.u5486 = KTree.node D2M8K2.t5494 (nat_lit 11930486) (nat_lit 3897848555) (nat_lit 0) D2M8K2.t5495 from rfl, allE_node, rows5494, irow5486, rows5495]
  all_goals rfl

theorem atot5486 : totK PD2M8K2 D2M8K2.u5486 = [0, 0, 0, 390728625447, 926340850585, 428744073935, 28283431639, 0] := by
  rw [show D2M8K2.u5486 = KTree.node D2M8K2.t5494 (nat_lit 11930486) (nat_lit 3897848555) (nat_lit 0) D2M8K2.t5495 from rfl, totK_node, tot5494, tot5495]
  decide +kernel

theorem arows5489 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5489 = true := by
  rw [show D2M8K2.u5489 = KTree.node D2M8K2.t5496 (nat_lit 11932270) (nat_lit 3948008406) (nat_lit 0) D2M8K2.t5497 from rfl, allE_node, rows5496, irow5489, rows5497]
  all_goals rfl

theorem atot5489 : totK PD2M8K2 D2M8K2.u5489 = [0, 0, 0, 164905175804, 768952895700, 709556682506, 107080588716, 1406452163] := by
  rw [show D2M8K2.u5489 = KTree.node D2M8K2.t5496 (nat_lit 11932270) (nat_lit 3948008406) (nat_lit 0) D2M8K2.t5497 from rfl, totK_node, tot5496, tot5497]
  decide +kernel

theorem arows5490 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5490 = true := by
  rw [show D2M8K2.u5490 = KTree.node D2M8K2.t5498 (nat_lit 11934605) (nat_lit 923947322) (nat_lit 0) D2M8K2.t5499 from rfl, allE_node, rows5498, irow5490, rows5499]
  all_goals rfl

theorem atot5490 : totK PD2M8K2 D2M8K2.u5490 = [0, 0, 0, 329325398760, 939973965716, 484476561313, 30280388812, 0] := by
  rw [show D2M8K2.u5490 = KTree.node D2M8K2.t5498 (nat_lit 11934605) (nat_lit 923947322) (nat_lit 0) D2M8K2.t5499 from rfl, totK_node, tot5498, tot5499]
  decide +kernel

theorem arows5492 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5492 = true := by
  rw [show D2M8K2.u5492 = KTree.node D2M8K2.t5500 (nat_lit 11936814) (nat_lit 4048482758) (nat_lit 0) D2M8K2.t5501 from rfl, allE_node, rows5500, irow5492, rows5501]
  all_goals rfl

theorem atot5492 : totK PD2M8K2 D2M8K2.u5492 = [0, 0, 0, 173635257284, 789783944599, 698236430179, 107897593678, 1415681459] := by
  rw [show D2M8K2.u5492 = KTree.node D2M8K2.t5500 (nat_lit 11936814) (nat_lit 4048482758) (nat_lit 0) D2M8K2.t5501 from rfl, totK_node, tot5500, tot5501]
  decide +kernel

theorem arows5493 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5493 = true := by
  rw [show D2M8K2.u5493 = KTree.node D2M8K2.t5502 (nat_lit 11941929) (nat_lit 1131969689) (nat_lit 512) D2M8K2.t5503 from rfl, allE_node, rows5502, irow5493, rows5503]
  all_goals rfl

theorem atot5493 : totK PD2M8K2 D2M8K2.u5493 = [0, 0, 0, 267746219242, 861861728308, 615731124761, 55868589442, 0] := by
  rw [show D2M8K2.u5493 = KTree.node D2M8K2.t5502 (nat_lit 11941929) (nat_lit 1131969689) (nat_lit 512) D2M8K2.t5503 from rfl, totK_node, tot5502, tot5503]
  decide +kernel

theorem arows5500 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5500 = true := by
  rw [show D2M8K2.u5500 = KTree.node D2M8K2.t5504 (nat_lit 11943768) (nat_lit 3560977960) (nat_lit 0) D2M8K2.t5505 from rfl, allE_node, rows5504, irow5500, rows5505]
  all_goals rfl

theorem atot5500 : totK PD2M8K2 D2M8K2.u5500 = [180062721715, 379215245065, 113678248214, 1369820453, 247841467323, 617659404114, 235492752849, 10297110227] := by
  rw [show D2M8K2.u5500 = KTree.node D2M8K2.t5504 (nat_lit 11943768) (nat_lit 3560977960) (nat_lit 0) D2M8K2.t5505 from rfl, totK_node, tot5504, tot5505]
  decide +kernel

theorem arows5501 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5501 = true := by
  rw [show D2M8K2.u5501 = KTree.node D2M8K2.t5506 (nat_lit 11945258) (nat_lit 3061085027) (nat_lit 0) D2M8K2.t5507 from rfl, allE_node, rows5506, irow5501, rows5507]
  all_goals rfl

theorem atot5501 : totK PD2M8K2 D2M8K2.u5501 = [262362370781, 836854972553, 614785886532, 85383223934, 1369150432, 0, 0, 0] := by
  rw [show D2M8K2.u5501 = KTree.node D2M8K2.t5506 (nat_lit 11945258) (nat_lit 3061085027) (nat_lit 0) D2M8K2.t5507 from rfl, totK_node, tot5506, tot5507]
  decide +kernel

theorem arows5503 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5503 = true := by
  rw [show D2M8K2.u5503 = KTree.node D2M8K2.t5508 (nat_lit 11947172) (nat_lit 2532168262) (nat_lit 0) D2M8K2.t5509 from rfl, allE_node, rows5508, irow5503, rows5509]
  all_goals rfl

theorem atot5503 : totK PD2M8K2 D2M8K2.u5503 = [170667201217, 753560908055, 800557513444, 108865139539, 0, 0, 0, 0] := by
  rw [show D2M8K2.u5503 = KTree.node D2M8K2.t5508 (nat_lit 11947172) (nat_lit 2532168262) (nat_lit 0) D2M8K2.t5509 from rfl, totK_node, tot5508, tot5509]
  decide +kernel

theorem arows5504 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5504 = true := by
  rw [show D2M8K2.u5504 = KTree.node D2M8K2.t5510 (nat_lit 11952318) (nat_lit 2997240474) (nat_lit 0) D2M8K2.t5511 from rfl, allE_node, rows5510, irow5504, rows5511]
  all_goals rfl

theorem atot5504 : totK PD2M8K2 D2M8K2.u5504 = [250512087363, 805564892311, 643897487693, 99542086737, 1164319620, 0, 0, 0] := by
  rw [show D2M8K2.u5504 = KTree.node D2M8K2.t5510 (nat_lit 11952318) (nat_lit 2997240474) (nat_lit 0) D2M8K2.t5511 from rfl, totK_node, tot5510, tot5511]
  decide +kernel

theorem arows5507 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5507 = true := by
  rw [show D2M8K2.u5507 = KTree.node D2M8K2.t5512 (nat_lit 11954021) (nat_lit 2312267637) (nat_lit 0) D2M8K2.t5513 from rfl, allE_node, rows5512, irow5507, rows5513]
  all_goals rfl

theorem atot5507 : totK PD2M8K2 D2M8K2.u5507 = [139701926982, 635690310707, 768418839145, 220322185542, 11885407614, 0, 0, 0] := by
  rw [show D2M8K2.u5507 = KTree.node D2M8K2.t5512 (nat_lit 11954021) (nat_lit 2312267637) (nat_lit 0) D2M8K2.t5513 from rfl, totK_node, tot5512, tot5513]
  decide +kernel

theorem arows5508 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5508 = true := by
  rw [show D2M8K2.u5508 = KTree.node D2M8K2.t5514 (nat_lit 11955753) (nat_lit 1537733527) (nat_lit 0) D2M8K2.t5515 from rfl, allE_node, rows5514, irow5508, rows5515]
  all_goals rfl

theorem atot5508 : totK PD2M8K2 D2M8K2.u5508 = [260234955078, 787348463544, 626251192529, 98461731808, 1198073392, 0, 0, 0] := by
  rw [show D2M8K2.u5508 = KTree.node D2M8K2.t5514 (nat_lit 11955753) (nat_lit 1537733527) (nat_lit 0) D2M8K2.t5515 from rfl, totK_node, tot5514, tot5515]
  decide +kernel

theorem arows5510 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5510 = true := by
  rw [show D2M8K2.u5510 = KTree.node D2M8K2.t5516 (nat_lit 11957473) (nat_lit 1548102170) (nat_lit 0) D2M8K2.t5517 from rfl, allE_node, rows5516, irow5510, rows5517]
  all_goals rfl

theorem atot5510 : totK PD2M8K2 D2M8K2.u5510 = [153550581146, 633638782732, 732295363494, 230695699116, 12052611869, 0, 0, 0] := by
  rw [show D2M8K2.u5510 = KTree.node D2M8K2.t5516 (nat_lit 11957473) (nat_lit 1548102170) (nat_lit 0) D2M8K2.t5517 from rfl, totK_node, tot5516, tot5517]
  decide +kernel

theorem arows5511 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5511 = true := by
  rw [show D2M8K2.u5511 = KTree.node D2M8K2.t5518 (nat_lit 11958860) (nat_lit 3193257204) (nat_lit 0) D2M8K2.t5519 from rfl, allE_node, rows5518, irow5511, rows5519]
  all_goals rfl

theorem atot5511 : totK PD2M8K2 D2M8K2.u5511 = [260666961338, 798926439900, 618997538015, 89289031772, 1096505104, 0, 0, 0] := by
  rw [show D2M8K2.u5511 = KTree.node D2M8K2.t5518 (nat_lit 11958860) (nat_lit 3193257204) (nat_lit 0) D2M8K2.t5519 from rfl, totK_node, tot5518, tot5519]
  decide +kernel

theorem arows5515 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5515 = true := by
  rw [show D2M8K2.u5515 = KTree.node D2M8K2.t5520 (nat_lit 11960804) (nat_lit 3107438361) (nat_lit 0) D2M8K2.t5521 from rfl, allE_node, rows5520, irow5515, rows5521]
  all_goals rfl

theorem atot5515 : totK PD2M8K2 D2M8K2.u5515 = [155723744192, 708478613821, 775345359611, 153220635883, 3884009855, 0, 0, 0] := by
  rw [show D2M8K2.u5515 = KTree.node D2M8K2.t5520 (nat_lit 11960804) (nat_lit 3107438361) (nat_lit 0) D2M8K2.t5521 from rfl, totK_node, tot5520, tot5521]
  decide +kernel

theorem arows5516 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5516 = true := by
  rw [show D2M8K2.u5516 = KTree.node D2M8K2.t5522 (nat_lit 11962666) (nat_lit 4022249060) (nat_lit 0) D2M8K2.t5523 from rfl, allE_node, rows5522, irow5516, rows5523]
  all_goals rfl

theorem atot5516 : totK PD2M8K2 D2M8K2.u5516 = [263510597586, 791725954447, 630617641113, 110590877280, 1268739303, 0, 0, 0] := by
  rw [show D2M8K2.u5516 = KTree.node D2M8K2.t5522 (nat_lit 11962666) (nat_lit 4022249060) (nat_lit 0) D2M8K2.t5523 from rfl, totK_node, tot5522, tot5523]
  decide +kernel

theorem arows5518 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5518 = true := by
  rw [show D2M8K2.u5518 = KTree.node D2M8K2.t5524 (nat_lit 11964049) (nat_lit 1131086393) (nat_lit 0) D2M8K2.t5525 from rfl, allE_node, rows5524, irow5518, rows5525]
  all_goals rfl

theorem atot5518 : totK PD2M8K2 D2M8K2.u5518 = [0, 392327163543, 951050041862, 400723514873, 22149860293, 0, 0, 0] := by
  rw [show D2M8K2.u5518 = KTree.node D2M8K2.t5524 (nat_lit 11964049) (nat_lit 1131086393) (nat_lit 0) D2M8K2.t5525 from rfl, totK_node, tot5524, tot5525]
  decide +kernel

theorem arows5519 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5519 = true := by
  rw [show D2M8K2.u5519 = KTree.node D2M8K2.t5526 (nat_lit 11965830) (nat_lit 3743316732) (nat_lit 0) D2M8K2.t5527 from rfl, allE_node, rows5526, irow5519, rows5527]
  all_goals rfl

theorem atot5519 : totK PD2M8K2 D2M8K2.u5519 = [0, 348454617670, 913080024713, 466464057826, 35104168523, 0, 0, 0] := by
  rw [show D2M8K2.u5519 = KTree.node D2M8K2.t5526 (nat_lit 11965830) (nat_lit 3743316732) (nat_lit 0) D2M8K2.t5527 from rfl, totK_node, tot5526, tot5527]
  decide +kernel

theorem arows5522 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5522 = true := by
  rw [show D2M8K2.u5522 = KTree.node D2M8K2.t5528 (nat_lit 11967625) (nat_lit 1481302006) (nat_lit 0) D2M8K2.t5529 from rfl, allE_node, rows5528, irow5522, rows5529]
  all_goals rfl

theorem atot5522 : totK PD2M8K2 D2M8K2.u5522 = [0, 156103765308, 743317484400, 725367240713, 129381094191, 1369150432, 0, 0] := by
  rw [show D2M8K2.u5522 = KTree.node D2M8K2.t5528 (nat_lit 11967625) (nat_lit 1481302006) (nat_lit 0) D2M8K2.t5529 from rfl, totK_node, tot5528, tot5529]
  decide +kernel

theorem arows5523 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5523 = true := by
  rw [show D2M8K2.u5523 = KTree.node D2M8K2.t5530 (nat_lit 11972914) (nat_lit 2514441587) (nat_lit 0) D2M8K2.t5531 from rfl, allE_node, rows5530, irow5523, rows5531]
  all_goals rfl

theorem atot5523 : totK PD2M8K2 D2M8K2.u5523 = [0, 351481112683, 937427781395, 464497349296, 26515492062, 0, 0, 0] := by
  rw [show D2M8K2.u5523 = KTree.node D2M8K2.t5530 (nat_lit 11972914) (nat_lit 2514441587) (nat_lit 0) D2M8K2.t5531 from rfl, totK_node, tot5530, tot5531]
  decide +kernel

theorem arows5525 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5525 = true := by
  rw [show D2M8K2.u5525 = KTree.node D2M8K2.t5532 (nat_lit 11976266) (nat_lit 3925833918) (nat_lit 0) D2M8K2.t5533 from rfl, allE_node, rows5532, irow5525, rows5533]
  all_goals rfl

theorem atot5525 : totK PD2M8K2 D2M8K2.u5525 = [0, 387569256741, 924934152667, 424777165109, 25275037740, 0, 0, 0] := by
  rw [show D2M8K2.u5525 = KTree.node D2M8K2.t5532 (nat_lit 11976266) (nat_lit 3925833918) (nat_lit 0) D2M8K2.t5533 from rfl, totK_node, tot5532, tot5533]
  decide +kernel

theorem arows5526 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5526 = true := by
  rw [show D2M8K2.u5526 = KTree.node D2M8K2.t5534 (nat_lit 11979324) (nat_lit 2756610414) (nat_lit 0) D2M8K2.t5535 from rfl, allE_node, rows5534, irow5526, rows5535]
  all_goals rfl

theorem atot5526 : totK PD2M8K2 D2M8K2.u5526 = [0, 333310109971, 936247240488, 458089326527, 21804410294, 0, 0, 0] := by
  rw [show D2M8K2.u5526 = KTree.node D2M8K2.t5534 (nat_lit 11979324) (nat_lit 2756610414) (nat_lit 0) D2M8K2.t5535 from rfl, totK_node, tot5534, tot5535]
  decide +kernel

theorem arows5531 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5531 = true := by
  rw [show D2M8K2.u5531 = KTree.node D2M8K2.t5536 (nat_lit 11982598) (nat_lit 3816079831) (nat_lit 0) D2M8K2.t5537 from rfl, allE_node, rows5536, irow5531, rows5537]
  all_goals rfl

theorem atot5531 : totK PD2M8K2 D2M8K2.u5531 = [0, 410058667763, 954997288131, 411028941549, 16264871960, 0, 0, 0] := by
  rw [show D2M8K2.u5531 = KTree.node D2M8K2.t5536 (nat_lit 11982598) (nat_lit 3816079831) (nat_lit 0) D2M8K2.t5537 from rfl, totK_node, tot5536, tot5537]
  decide +kernel

theorem arows5532 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5532 = true := by
  rw [show D2M8K2.u5532 = KTree.node D2M8K2.t5538 (nat_lit 12027599) (nat_lit 2767962344) (nat_lit 0) D2M8K2.t5539 from rfl, allE_node, rows5538, irow5532, rows5539]
  all_goals rfl

theorem atot5532 : totK PD2M8K2 D2M8K2.u5532 = [334799102639, 823842934737, 477701357278, 139805852495, 13468148062, 0, 0, 0] := by
  rw [show D2M8K2.u5532 = KTree.node D2M8K2.t5538 (nat_lit 12027599) (nat_lit 2767962344) (nat_lit 0) D2M8K2.t5539 from rfl, totK_node, tot5538, tot5539]
  decide +kernel

theorem arows5534 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5534 = true := by
  rw [show D2M8K2.u5534 = KTree.node D2M8K2.t5540 (nat_lit 12028873) (nat_lit 1495594652) (nat_lit 0) D2M8K2.t5541 from rfl, allE_node, rows5540, irow5534, rows5541]
  all_goals rfl

theorem atot5534 : totK PD2M8K2 D2M8K2.u5534 = [86674881168, 671928649813, 893766634136, 150482114468, 1369150432, 0, 0, 0] := by
  rw [show D2M8K2.u5534 = KTree.node D2M8K2.t5540 (nat_lit 12028873) (nat_lit 1495594652) (nat_lit 0) D2M8K2.t5541 from rfl, totK_node, tot5540, tot5541]
  decide +kernel

theorem arows5535 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5535 = true := by
  rw [show D2M8K2.u5535 = KTree.node D2M8K2.t5542 (nat_lit 12031172) (nat_lit 3270063782) (nat_lit 0) D2M8K2.t5543 from rfl, allE_node, rows5542, irow5535, rows5543]
  all_goals rfl

theorem atot5535 : totK PD2M8K2 D2M8K2.u5535 = [347345618735, 914170038729, 540887613688, 51748400364, 0, 0, 0, 0] := by
  rw [show D2M8K2.u5535 = KTree.node D2M8K2.t5542 (nat_lit 12031172) (nat_lit 3270063782) (nat_lit 0) D2M8K2.t5543 from rfl, totK_node, tot5542, tot5543]
  decide +kernel

theorem arows5538 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5538 = true := by
  rw [show D2M8K2.u5538 = KTree.node D2M8K2.t5544 (nat_lit 12033242) (nat_lit 4241602830) (nat_lit 0) D2M8K2.t5545 from rfl, allE_node, rows5544, irow5538, rows5545]
  all_goals rfl

theorem atot5538 : totK PD2M8K2 D2M8K2.u5538 = [57586079575, 408691716527, 871390942663, 447697593904, 33318032364, 0, 0, 0] := by
  rw [show D2M8K2.u5538 = KTree.node D2M8K2.t5544 (nat_lit 12033242) (nat_lit 4241602830) (nat_lit 0) D2M8K2.t5545 from rfl, totK_node, tot5544, tot5545]
  decide +kernel

theorem arows5539 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5539 = true := by
  rw [show D2M8K2.u5539 = KTree.node D2M8K2.t5546 (nat_lit 12034485) (nat_lit 1734350842) (nat_lit 0) D2M8K2.t5547 from rfl, allE_node, rows5546, irow5539, rows5547]
  all_goals rfl

theorem atot5539 : totK PD2M8K2 D2M8K2.u5539 = [379506729198, 951821494910, 472770875713, 33861897489, 0, 0, 0, 0] := by
  rw [show D2M8K2.u5539 = KTree.node D2M8K2.t5546 (nat_lit 12034485) (nat_lit 1734350842) (nat_lit 0) D2M8K2.t5547 from rfl, totK_node, tot5546, tot5547]
  decide +kernel

theorem arows5541 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5541 = true := by
  rw [show D2M8K2.u5541 = KTree.node D2M8K2.t5548 (nat_lit 12036136) (nat_lit 3888878535) (nat_lit 0) D2M8K2.t5549 from rfl, allE_node, rows5548, irow5541, rows5549]
  all_goals rfl

theorem atot5541 : totK PD2M8K2 D2M8K2.u5541 = [0, 493641653270, 983116682731, 294929371191, 13049727234, 0, 0, 0] := by
  rw [show D2M8K2.u5541 = KTree.node D2M8K2.t5548 (nat_lit 12036136) (nat_lit 3888878535) (nat_lit 0) D2M8K2.t5549 from rfl, totK_node, tot5548, tot5549]
  decide +kernel

theorem arows5542 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5542 = true := by
  rw [show D2M8K2.u5542 = KTree.node D2M8K2.t5550 (nat_lit 12041258) (nat_lit 3992353879) (nat_lit 0) D2M8K2.t5551 from rfl, allE_node, rows5550, irow5542, rows5551]
  all_goals rfl

theorem atot5542 : totK PD2M8K2 D2M8K2.u5542 = [354966390490, 896848497761, 506276472679, 48900691898, 0, 0, 0, 0] := by
  rw [show D2M8K2.u5542 = KTree.node D2M8K2.t5550 (nat_lit 12041258) (nat_lit 3992353879) (nat_lit 0) D2M8K2.t5551 from rfl, totK_node, tot5550, tot5551]
  decide +kernel

theorem arows5546 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5546 = true := by
  rw [show D2M8K2.u5546 = KTree.node D2M8K2.t5552 (nat_lit 12042845) (nat_lit 2147466339) (nat_lit 0) D2M8K2.t5553 from rfl, allE_node, rows5552, irow5546, rows5553]
  all_goals rfl

theorem atot5546 : totK PD2M8K2 D2M8K2.u5546 = [73236950170, 616868756600, 887019050138, 204271919055, 4980514959, 0, 0, 0] := by
  rw [show D2M8K2.u5546 = KTree.node D2M8K2.t5552 (nat_lit 12042845) (nat_lit 2147466339) (nat_lit 0) D2M8K2.t5553 from rfl, totK_node, tot5552, tot5553]
  decide +kernel

theorem arows5547 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5547 = true := by
  rw [show D2M8K2.u5547 = KTree.node D2M8K2.t5554 (nat_lit 12044787) (nat_lit 3653736964) (nat_lit 0) D2M8K2.t5555 from rfl, allE_node, rows5554, irow5547, rows5555]
  all_goals rfl

theorem atot5547 : totK PD2M8K2 D2M8K2.u5547 = [392969997247, 934165922091, 462490395106, 35803915398, 0, 0, 0, 0] := by
  rw [show D2M8K2.u5547 = KTree.node D2M8K2.t5554 (nat_lit 12044787) (nat_lit 3653736964) (nat_lit 0) D2M8K2.t5555 from rfl, totK_node, tot5554, tot5555]
  decide +kernel

theorem arows5549 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5549 = true := by
  rw [show D2M8K2.u5549 = KTree.node D2M8K2.t5556 (nat_lit 12046493) (nat_lit 2309705924) (nat_lit 0) D2M8K2.t5557 from rfl, allE_node, rows5556, irow5549, rows5557]
  all_goals rfl

theorem atot5549 : totK PD2M8K2 D2M8K2.u5549 = [0, 502983443516, 972089147453, 296351973147, 8708200738, 0, 0, 0] := by
  rw [show D2M8K2.u5549 = KTree.node D2M8K2.t5556 (nat_lit 12046493) (nat_lit 2309705924) (nat_lit 0) D2M8K2.t5557 from rfl, totK_node, tot5556, tot5557]
  decide +kernel

theorem arows5550 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5550 = true := by
  rw [show D2M8K2.u5550 = KTree.node D2M8K2.t5558 (nat_lit 12048334) (nat_lit 3985331683) (nat_lit 0) D2M8K2.t5559 from rfl, allE_node, rows5558, irow5550, rows5559]
  all_goals rfl

theorem atot5550 : totK PD2M8K2 D2M8K2.u5550 = [0, 341022938753, 946713030985, 446626162107, 25439674165, 0, 0, 0] := by
  rw [show D2M8K2.u5550 = KTree.node D2M8K2.t5558 (nat_lit 12048334) (nat_lit 3985331683) (nat_lit 0) D2M8K2.t5559 from rfl, totK_node, tot5558, tot5559]
  decide +kernel

theorem arows5553 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5553 = true := by
  rw [show D2M8K2.u5553 = KTree.node D2M8K2.t5560 (nat_lit 12049954) (nat_lit 3727769886) (nat_lit 0) D2M8K2.t5561 from rfl, allE_node, rows5560, irow5553, rows5561]
  all_goals rfl

theorem atot5553 : totK PD2M8K2 D2M8K2.u5553 = [0, 157993691816, 727320640747, 769387605002, 108089697200, 1206465782, 0, 0] := by
  rw [show D2M8K2.u5553 = KTree.node D2M8K2.t5560 (nat_lit 12049954) (nat_lit 3727769886) (nat_lit 0) D2M8K2.t5561 from rfl, totK_node, tot5560, tot5561]
  decide +kernel

theorem arows5554 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5554 = true := by
  rw [show D2M8K2.u5554 = KTree.node D2M8K2.t5562 (nat_lit 12052308) (nat_lit 2312552117) (nat_lit 0) D2M8K2.t5563 from rfl, allE_node, rows5562, irow5554, rows5563]
  all_goals rfl

theorem atot5554 : totK PD2M8K2 D2M8K2.u5554 = [0, 361051342719, 933549414706, 489812405983, 43258189691, 0, 0, 0] := by
  rw [show D2M8K2.u5554 = KTree.node D2M8K2.t5562 (nat_lit 12052308) (nat_lit 2312552117) (nat_lit 0) D2M8K2.t5563 from rfl, totK_node, tot5562, tot5563]
  decide +kernel

theorem arows5556 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5556 = true := by
  rw [show D2M8K2.u5556 = KTree.node D2M8K2.t5564 (nat_lit 12055281) (nat_lit 1568821999) (nat_lit 0) D2M8K2.t5565 from rfl, allE_node, rows5564, irow5556, rows5565]
  all_goals rfl

theorem atot5556 : totK PD2M8K2 D2M8K2.u5556 = [0, 352420595784, 943140874102, 488556698276, 30547945836, 0, 0, 0] := by
  rw [show D2M8K2.u5556 = KTree.node D2M8K2.t5564 (nat_lit 12055281) (nat_lit 1568821999) (nat_lit 0) D2M8K2.t5565 from rfl, totK_node, tot5564, tot5565]
  decide +kernel

theorem arows5557 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5557 = true := by
  rw [show D2M8K2.u5557 = KTree.node D2M8K2.t5566 (nat_lit 12056970) (nat_lit 2232764494) (nat_lit 0) D2M8K2.t5567 from rfl, allE_node, rows5566, irow5557, rows5567]
  all_goals rfl

theorem atot5557 : totK PD2M8K2 D2M8K2.u5557 = [0, 36272210802, 512538960864, 896141963070, 276226739243, 13016197374, 0, 0] := by
  rw [show D2M8K2.u5557 = KTree.node D2M8K2.t5566 (nat_lit 12056970) (nat_lit 2232764494) (nat_lit 0) D2M8K2.t5567 from rfl, totK_node, tot5566, tot5567]
  decide +kernel

theorem arows5563 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5563 = true := by
  rw [show D2M8K2.u5563 = KTree.node D2M8K2.t5568 (nat_lit 12062137) (nat_lit 1398571785) (nat_lit 0) D2M8K2.t5569 from rfl, allE_node, rows5568, irow5563, rows5569]
  all_goals rfl

theorem atot5563 : totK PD2M8K2 D2M8K2.u5563 = [0, 371373426194, 939977204189, 446026973712, 24200525243, 0, 0, 0] := by
  rw [show D2M8K2.u5563 = KTree.node D2M8K2.t5568 (nat_lit 12062137) (nat_lit 1398571785) (nat_lit 0) D2M8K2.t5569 from rfl, totK_node, tot5568, tot5569]
  decide +kernel

theorem arows5564 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5564 = true := by
  rw [show D2M8K2.u5564 = KTree.node D2M8K2.t5570 (nat_lit 12064059) (nat_lit 3666330531) (nat_lit 0) D2M8K2.t5571 from rfl, allE_node, rows5570, irow5564, rows5571]
  all_goals rfl

theorem atot5564 : totK PD2M8K2 D2M8K2.u5564 = [0, 100329972706, 654649906071, 795299444550, 152838964140, 4574395652, 0, 0] := by
  rw [show D2M8K2.u5564 = KTree.node D2M8K2.t5570 (nat_lit 12064059) (nat_lit 3666330531) (nat_lit 0) D2M8K2.t5571 from rfl, totK_node, tot5570, tot5571]
  decide +kernel

theorem arows5566 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5566 = true := by
  rw [show D2M8K2.u5566 = KTree.node D2M8K2.t5572 (nat_lit 12065791) (nat_lit 1783249408) (nat_lit 0) D2M8K2.t5573 from rfl, allE_node, rows5572, irow5566, rows5573]
  all_goals rfl

theorem atot5566 : totK PD2M8K2 D2M8K2.u5566 = [54494369517, 396629251674, 847009757440, 483538678588, 42777965325, 0, 0, 0] := by
  rw [show D2M8K2.u5566 = KTree.node D2M8K2.t5572 (nat_lit 12065791) (nat_lit 1783249408) (nat_lit 0) D2M8K2.t5573 from rfl, totK_node, tot5572, tot5573]
  decide +kernel

theorem arows5567 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5567 = true := by
  rw [show D2M8K2.u5567 = KTree.node D2M8K2.t5574 (nat_lit 12069376) (nat_lit 1809862710) (nat_lit 0) D2M8K2.t5575 from rfl, allE_node, rows5574, irow5567, rows5575]
  all_goals rfl

theorem atot5567 : totK PD2M8K2 D2M8K2.u5567 = [362856749776, 949168227506, 453786650028, 23644192949, 0, 0, 0, 0] := by
  rw [show D2M8K2.u5567 = KTree.node D2M8K2.t5574 (nat_lit 12069376) (nat_lit 1809862710) (nat_lit 0) D2M8K2.t5575 from rfl, totK_node, tot5574, tot5575]
  decide +kernel

theorem arows5570 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5570 = true := by
  rw [show D2M8K2.u5570 = KTree.node D2M8K2.t5576 (nat_lit 12071066) (nat_lit 3759541253) (nat_lit 0) D2M8K2.t5577 from rfl, allE_node, rows5576, irow5570, rows5577]
  all_goals rfl

theorem atot5570 : totK PD2M8K2 D2M8K2.u5570 = [86950764009, 677754307531, 881309611189, 153641691228, 1369150432, 0, 0, 0] := by
  rw [show D2M8K2.u5570 = KTree.node D2M8K2.t5576 (nat_lit 12071066) (nat_lit 3759541253) (nat_lit 0) D2M8K2.t5577 from rfl, totK_node, tot5576, tot5577]
  decide +kernel

theorem arows5571 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5571 = true := by
  rw [show D2M8K2.u5571 = KTree.node D2M8K2.t5578 (nat_lit 12079894) (nat_lit 2655931384) (nat_lit 0) D2M8K2.t5579 from rfl, allE_node, rows5578, irow5571, rows5579]
  all_goals rfl

theorem atot5571 : totK PD2M8K2 D2M8K2.u5571 = [334532830801, 901405875178, 533302672235, 47403516683, 0, 0, 0, 0] := by
  rw [show D2M8K2.u5571 = KTree.node D2M8K2.t5578 (nat_lit 12079894) (nat_lit 2655931384) (nat_lit 0) D2M8K2.t5579 from rfl, totK_node, tot5578, tot5579]
  decide +kernel

theorem arows5573 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5573 = true := by
  rw [show D2M8K2.u5573 = KTree.node D2M8K2.t5580 (nat_lit 12081561) (nat_lit 1818964075) (nat_lit 0) D2M8K2.t5581 from rfl, allE_node, rows5580, irow5573, rows5581]
  all_goals rfl

theorem atot5573 : totK PD2M8K2 D2M8K2.u5573 = [84865244063, 504881894619, 878288026994, 298848805897, 13250685261, 0, 0, 0] := by
  rw [show D2M8K2.u5573 = KTree.node D2M8K2.t5580 (nat_lit 12081561) (nat_lit 1818964075) (nat_lit 0) D2M8K2.t5581 from rfl, totK_node, tot5580, tot5581]
  decide +kernel

theorem arows5574 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5574 = true := by
  rw [show D2M8K2.u5574 = KTree.node D2M8K2.t5582 (nat_lit 12083006) (nat_lit 2424849636) (nat_lit 0) D2M8K2.t5583 from rfl, allE_node, rows5582, irow5574, rows5583]
  all_goals rfl

theorem atot5574 : totK PD2M8K2 D2M8K2.u5574 = [313224663836, 916045688146, 520325472784, 39838082948, 0, 0, 0, 0] := by
  rw [show D2M8K2.u5574 = KTree.node D2M8K2.t5582 (nat_lit 12083006) (nat_lit 2424849636) (nat_lit 0) D2M8K2.t5583 from rfl, totK_node, tot5582, tot5583]
  decide +kernel

theorem arows5578 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5578 = true := by
  rw [show D2M8K2.u5578 = KTree.node D2M8K2.t5584 (nat_lit 12084888) (nat_lit 3318235157) (nat_lit 0) D2M8K2.t5585 from rfl, allE_node, rows5584, irow5578, rows5585]
  all_goals rfl

theorem atot5578 : totK PD2M8K2 D2M8K2.u5578 = [104705589965, 624263464975, 852868477516, 198890065250, 4980514959, 0, 0, 0] := by
  rw [show D2M8K2.u5578 = KTree.node D2M8K2.t5584 (nat_lit 12084888) (nat_lit 3318235157) (nat_lit 0) D2M8K2.t5585 from rfl, totK_node, tot5584, tot5585]
  decide +kernel

theorem arows5579 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5579 = true := by
  rw [show D2M8K2.u5579 = KTree.node D2M8K2.t5586 (nat_lit 12086632) (nat_lit 3214004656) (nat_lit 0) D2M8K2.t5587 from rfl, allE_node, rows5586, irow5579, rows5587]
  all_goals rfl

theorem atot5579 : totK PD2M8K2 D2M8K2.u5579 = [296679701545, 874533242793, 596500980365, 56865947751, 0, 0, 0, 0] := by
  rw [show D2M8K2.u5579 = KTree.node D2M8K2.t5586 (nat_lit 12086632) (nat_lit 3214004656) (nat_lit 0) D2M8K2.t5587 from rfl, totK_node, tot5586, tot5587]
  decide +kernel

theorem arows5581 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5581 = true := by
  rw [show D2M8K2.u5581 = KTree.node D2M8K2.t5588 (nat_lit 12088349) (nat_lit 1709231837) (nat_lit 0) D2M8K2.t5589 from rfl, allE_node, rows5588, irow5581, rows5589]
  all_goals rfl

theorem atot5581 : totK PD2M8K2 D2M8K2.u5581 = [0, 407018224530, 949864985548, 398383362778, 22042137240, 0, 0, 0] := by
  rw [show D2M8K2.u5581 = KTree.node D2M8K2.t5588 (nat_lit 12088349) (nat_lit 1709231837) (nat_lit 0) D2M8K2.t5589 from rfl, totK_node, tot5588, tot5589]
  decide +kernel

theorem arows5582 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5582 = true := by
  rw [show D2M8K2.u5582 = KTree.node D2M8K2.t5590 (nat_lit 12090212) (nat_lit 3262269730) (nat_lit 0) D2M8K2.t5591 from rfl, allE_node, rows5590, irow5582, rows5591]
  all_goals rfl

theorem atot5582 : totK PD2M8K2 D2M8K2.u5582 = [0, 328358414902, 950154535680, 464394122948, 23744477196, 0, 0, 0] := by
  rw [show D2M8K2.u5582 = KTree.node D2M8K2.t5590 (nat_lit 12090212) (nat_lit 3262269730) (nat_lit 0) D2M8K2.t5591 from rfl, totK_node, tot5590, tot5591]
  decide +kernel

theorem arows5585 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5585 = true := by
  rw [show D2M8K2.u5585 = KTree.node D2M8K2.t5592 (nat_lit 12092052) (nat_lit 3165344411) (nat_lit 0) D2M8K2.t5593 from rfl, allE_node, rows5592, irow5585, rows5593]
  all_goals rfl

theorem atot5585 : totK PD2M8K2 D2M8K2.u5585 = [0, 159547220069, 741481207262, 752809042786, 107197215511, 1239866073, 0, 0] := by
  rw [show D2M8K2.u5585 = KTree.node D2M8K2.t5592 (nat_lit 12092052) (nat_lit 3165344411) (nat_lit 0) D2M8K2.t5593 from rfl, totK_node, tot5592, tot5593]
  decide +kernel

theorem arows5586 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5586 = true := by
  rw [show D2M8K2.u5586 = KTree.node D2M8K2.t5594 (nat_lit 12100782) (nat_lit 3853418972) (nat_lit 0) D2M8K2.t5595 from rfl, allE_node, rows5594, irow5586, rows5595]
  all_goals rfl

theorem atot5586 : totK PD2M8K2 D2M8K2.u5586 = [0, 264153847147, 810831672922, 603757733147, 84833895593, 1171084559, 0, 0] := by
  rw [show D2M8K2.u5586 = KTree.node D2M8K2.t5594 (nat_lit 12100782) (nat_lit 3853418972) (nat_lit 0) D2M8K2.t5595 from rfl, totK_node, tot5594, tot5595]
  decide +kernel

theorem arows5588 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5588 = true := by
  rw [show D2M8K2.u5588 = KTree.node D2M8K2.t5596 (nat_lit 12102453) (nat_lit 1714552665) (nat_lit 0) D2M8K2.t5597 from rfl, allE_node, rows5596, irow5588, rows5597]
  all_goals rfl

theorem atot5588 : totK PD2M8K2 D2M8K2.u5588 = [0, 134621038025, 616395377605, 763193830310, 225186132323, 11934365838, 0, 0] := by
  rw [show D2M8K2.u5588 = KTree.node D2M8K2.t5596 (nat_lit 12102453) (nat_lit 1714552665) (nat_lit 0) D2M8K2.t5597 from rfl, totK_node, tot5596, tot5597]
  decide +kernel

theorem arows5589 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5589 = true := by
  rw [show D2M8K2.u5589 = KTree.node D2M8K2.t5598 (nat_lit 12104010) (nat_lit 3721418313) (nat_lit 0) D2M8K2.t5599 from rfl, allE_node, rows5598, irow5589, rows5599]
  all_goals rfl

theorem atot5589 : totK PD2M8K2 D2M8K2.u5589 = [0, 261575548674, 818307228377, 593442702666, 75354808578, 1053411165, 0, 0] := by
  rw [show D2M8K2.u5589 = KTree.node D2M8K2.t5598 (nat_lit 12104010) (nat_lit 3721418313) (nat_lit 0) D2M8K2.t5599 from rfl, totK_node, tot5598, tot5599]
  decide +kernel

theorem arows5594 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5594 = true := by
  rw [show D2M8K2.u5594 = KTree.node D2M8K2.t5600 (nat_lit 12106041) (nat_lit 1890163379) (nat_lit 0) D2M8K2.t5601 from rfl, allE_node, rows5600, irow5594, rows5601]
  all_goals rfl

theorem atot5594 : totK PD2M8K2 D2M8K2.u5594 = [0, 193539472607, 736102000613, 704971260554, 125768211272, 3667207281, 0, 0] := by
  rw [show D2M8K2.u5594 = KTree.node D2M8K2.t5600 (nat_lit 12106041) (nat_lit 1890163379) (nat_lit 0) D2M8K2.t5601 from rfl, totK_node, tot5600, tot5601]
  decide +kernel

theorem arows5595 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5595 = true := by
  rw [show D2M8K2.u5595 = KTree.node D2M8K2.t5602 (nat_lit 12107941) (nat_lit 1366036621) (nat_lit 0) D2M8K2.t5603 from rfl, allE_node, rows5602, irow5595, rows5603]
  all_goals rfl

theorem atot5595 : totK PD2M8K2 D2M8K2.u5595 = [176663725160, 577016253579, 692006820074, 337152689397, 25961640779, 0, 0, 0] := by
  rw [show D2M8K2.u5595 = KTree.node D2M8K2.t5602 (nat_lit 12107941) (nat_lit 1366036621) (nat_lit 0) D2M8K2.t5603 from rfl, totK_node, tot5602, tot5603]
  decide +kernel

theorem arows5597 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5597 = true := by
  rw [show D2M8K2.u5597 = KTree.node D2M8K2.t5604 (nat_lit 12111147) (nat_lit 3462129102) (nat_lit 0) D2M8K2.t5605 from rfl, allE_node, rows5604, irow5597, rows5605]
  all_goals rfl

theorem atot5597 : totK PD2M8K2 D2M8K2.u5597 = [242130998802, 780335089365, 635119425865, 105160474701, 1369150432, 0, 0, 0] := by
  rw [show D2M8K2.u5597 = KTree.node D2M8K2.t5604 (nat_lit 12111147) (nat_lit 3462129102) (nat_lit 0) D2M8K2.t5605 from rfl, totK_node, tot5604, tot5605]
  decide +kernel

theorem arows5598 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5598 = true := by
  rw [show D2M8K2.u5598 = KTree.node D2M8K2.t5606 (nat_lit 12113595) (nat_lit 3792201853) (nat_lit 0) D2M8K2.t5607 from rfl, allE_node, rows5606, irow5598, rows5607]
  all_goals rfl

theorem atot5598 : totK PD2M8K2 D2M8K2.u5598 = [173212757209, 771980028331, 787389384290, 96716609261, 0, 0, 0, 0] := by
  rw [show D2M8K2.u5598 = KTree.node D2M8K2.t5606 (nat_lit 12113595) (nat_lit 3792201853) (nat_lit 0) D2M8K2.t5607 from rfl, totK_node, tot5606, tot5607]
  decide +kernel

theorem arows5601 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5601 = true := by
  rw [show D2M8K2.u5601 = KTree.node D2M8K2.t5608 (nat_lit 12115382) (nat_lit 3998507065) (nat_lit 0) D2M8K2.t5609 from rfl, allE_node, rows5608, irow5601, rows5609]
  all_goals rfl

theorem atot5601 : totK PD2M8K2 D2M8K2.u5601 = [152868529535, 632302002387, 726106923969, 284800034085, 25269856785, 0, 0, 0] := by
  rw [show D2M8K2.u5601 = KTree.node D2M8K2.t5608 (nat_lit 12115382) (nat_lit 3998507065) (nat_lit 0) D2M8K2.t5609 from rfl, totK_node, tot5608, tot5609]
  decide +kernel

theorem arows5602 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5602 = true := by
  rw [show D2M8K2.u5602 = KTree.node D2M8K2.t5610 (nat_lit 12116978) (nat_lit 3170136446) (nat_lit 0) D2M8K2.t5611 from rfl, allE_node, rows5610, irow5602, rows5611]
  all_goals rfl

theorem atot5602 : totK PD2M8K2 D2M8K2.u5602 = [257037765869, 732679744489, 636916378118, 177143558268, 5430665091, 0, 0, 0] := by
  rw [show D2M8K2.u5602 = KTree.node D2M8K2.t5610 (nat_lit 12116978) (nat_lit 3170136446) (nat_lit 0) D2M8K2.t5611 from rfl, totK_node, tot5610, tot5611]
  decide +kernel

theorem arows5604 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5604 = true := by
  rw [show D2M8K2.u5604 = KTree.node D2M8K2.t5612 (nat_lit 12118528) (nat_lit 3735058750) (nat_lit 0) D2M8K2.t5613 from rfl, allE_node, rows5612, irow5604, rows5613]
  all_goals rfl

theorem atot5604 : totK PD2M8K2 D2M8K2.u5604 = [156854759878, 672755727849, 770295571361, 187085303117, 7166294683, 0, 0, 0] := by
  rw [show D2M8K2.u5604 = KTree.node D2M8K2.t5612 (nat_lit 12118528) (nat_lit 3735058750) (nat_lit 0) D2M8K2.t5613 from rfl, totK_node, tot5612, tot5613]
  decide +kernel

theorem arows5605 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5605 = true := by
  rw [show D2M8K2.u5605 = KTree.node D2M8K2.t5614 (nat_lit 12120348) (nat_lit 3509774347) (nat_lit 0) D2M8K2.t5615 from rfl, allE_node, rows5614, irow5605, rows5615]
  all_goals rfl

theorem atot5605 : totK PD2M8K2 D2M8K2.u5605 = [239754012038, 752175155209, 645770528132, 143635399324, 5883432551, 0, 0, 0] := by
  rw [show D2M8K2.u5605 = KTree.node D2M8K2.t5614 (nat_lit 12120348) (nat_lit 3509774347) (nat_lit 0) D2M8K2.t5615 from rfl, totK_node, tot5614, tot5615]
  decide +kernel

theorem arows5609 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5609 = true := by
  rw [show D2M8K2.u5609 = KTree.node D2M8K2.t5616 (nat_lit 12122025) (nat_lit 1888373647) (nat_lit 0) D2M8K2.t5617 from rfl, allE_node, rows5616, irow5609, rows5617]
  all_goals rfl

theorem atot5609 : totK PD2M8K2 D2M8K2.u5609 = [140433394095, 635727933597, 767359049295, 211289284459, 9668735432, 0, 0, 0] := by
  rw [show D2M8K2.u5609 = KTree.node D2M8K2.t5616 (nat_lit 12122025) (nat_lit 1888373647) (nat_lit 0) D2M8K2.t5617 from rfl, totK_node, tot5616, tot5617]
  decide +kernel

theorem arows5610 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5610 = true := by
  rw [show D2M8K2.u5610 = KTree.node D2M8K2.t5618 (nat_lit 12123970) (nat_lit 3631754906) (nat_lit 0) D2M8K2.t5619 from rfl, allE_node, rows5618, irow5610, rows5619]
  all_goals rfl

theorem atot5610 : totK PD2M8K2 D2M8K2.u5610 = [274943330944, 777652719709, 617095551477, 119399220432, 3581949829, 0, 0, 0] := by
  rw [show D2M8K2.u5610 = KTree.node D2M8K2.t5618 (nat_lit 12123970) (nat_lit 3631754906) (nat_lit 0) D2M8K2.t5619 from rfl, totK_node, tot5618, tot5619]
  decide +kernel

theorem arows5612 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5612 = true := by
  rw [show D2M8K2.u5612 = KTree.node D2M8K2.t5620 (nat_lit 12125434) (nat_lit 3469584850) (nat_lit 0) D2M8K2.t5621 from rfl, allE_node, rows5620, irow5612, rows5621]
  all_goals rfl

theorem atot5612 : totK PD2M8K2 D2M8K2.u5612 = [160403090464, 750497766794, 775760472174, 119430254234, 1096505104, 0, 0, 0] := by
  rw [show D2M8K2.u5612 = KTree.node D2M8K2.t5620 (nat_lit 12125434) (nat_lit 3469584850) (nat_lit 0) D2M8K2.t5621 from rfl, totK_node, tot5620, tot5621]
  decide +kernel

theorem arows5613 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5613 = true := by
  rw [show D2M8K2.u5613 = KTree.node D2M8K2.t5622 (nat_lit 12130834) (nat_lit 4006951394) (nat_lit 0) D2M8K2.t5623 from rfl, allE_node, rows5622, irow5613, rows5623]
  all_goals rfl

theorem atot5613 : totK PD2M8K2 D2M8K2.u5613 = [0, 395173664423, 942803648228, 391695223080, 22145572651, 0, 0, 0] := by
  rw [show D2M8K2.u5613 = KTree.node D2M8K2.t5622 (nat_lit 12130834) (nat_lit 4006951394) (nat_lit 0) D2M8K2.t5623 from rfl, totK_node, tot5622, tot5623]
  decide +kernel

theorem arows5616 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5616 = true := by
  rw [show D2M8K2.u5616 = KTree.node D2M8K2.t5624 (nat_lit 12132411) (nat_lit 662084082) (nat_lit 0) D2M8K2.t5625 from rfl, allE_node, rows5624, irow5616, rows5625]
  all_goals rfl

theorem atot5616 : totK PD2M8K2 D2M8K2.u5616 = [0, 140046100198, 783895303369, 718157218504, 92846287508, 1138244013, 0, 0] := by
  rw [show D2M8K2.u5616 = KTree.node D2M8K2.t5624 (nat_lit 12132411) (nat_lit 662084082) (nat_lit 0) D2M8K2.t5625 from rfl, totK_node, tot5624, tot5625]
  decide +kernel

theorem arows5617 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5617 = true := by
  rw [show D2M8K2.u5617 = KTree.node D2M8K2.t5626 (nat_lit 12134887) (nat_lit 2370556663) (nat_lit 0) D2M8K2.t5627 from rfl, allE_node, rows5626, irow5617, rows5627]
  all_goals rfl

theorem atot5617 : totK PD2M8K2 D2M8K2.u5617 = [0, 396864336873, 933385058365, 451868930517, 39256425416, 0, 0, 0] := by
  rw [show D2M8K2.u5617 = KTree.node D2M8K2.t5626 (nat_lit 12134887) (nat_lit 2370556663) (nat_lit 0) D2M8K2.t5627 from rfl, totK_node, tot5626, tot5627]
  decide +kernel

theorem arows5619 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5619 = true := by
  rw [show D2M8K2.u5619 = KTree.node D2M8K2.t5628 (nat_lit 12138203) (nat_lit 2265706628) (nat_lit 0) D2M8K2.t5629 from rfl, allE_node, rows5628, irow5619, rows5629]
  all_goals rfl

theorem atot5619 : totK PD2M8K2 D2M8K2.u5619 = [0, 344163345675, 939758359700, 482908241926, 27177940449, 0, 0, 0] := by
  rw [show D2M8K2.u5619 = KTree.node D2M8K2.t5628 (nat_lit 12138203) (nat_lit 2265706628) (nat_lit 0) D2M8K2.t5629 from rfl, totK_node, tot5628, tot5629]
  decide +kernel

theorem arows5620 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5620 = true := by
  rw [show D2M8K2.u5620 = KTree.node D2M8K2.t5630 (nat_lit 12141885) (nat_lit 1561811045) (nat_lit 0) D2M8K2.t5631 from rfl, allE_node, rows5630, irow5620, rows5631]
  all_goals rfl

theorem atot5620 : totK PD2M8K2 D2M8K2.u5620 = [0, 378480817657, 938377542928, 437627452961, 24663448840, 0, 0, 0] := by
  rw [show D2M8K2.u5620 = KTree.node D2M8K2.t5630 (nat_lit 12141885) (nat_lit 1561811045) (nat_lit 0) D2M8K2.t5631 from rfl, totK_node, tot5630, tot5631]
  decide +kernel

theorem arows5629 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5629 = true := by
  rw [show D2M8K2.u5629 = KTree.node D2M8K2.t5632 (nat_lit 12144938) (nat_lit 3959644861) (nat_lit 0) D2M8K2.t5633 from rfl, allE_node, rows5632, irow5629, rows5633]
  all_goals rfl

theorem atot5629 : totK PD2M8K2 D2M8K2.u5629 = [0, 351605214847, 904594542167, 476054879330, 35187629387, 0, 0, 0] := by
  rw [show D2M8K2.u5629 = KTree.node D2M8K2.t5632 (nat_lit 12144938) (nat_lit 3959644861) (nat_lit 0) D2M8K2.t5633 from rfl, totK_node, tot5632, tot5633]
  decide +kernel

theorem arows5630 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5630 = true := by
  rw [show D2M8K2.u5630 = KTree.node D2M8K2.t5634 (nat_lit 12146483) (nat_lit 1353073914) (nat_lit 0) D2M8K2.t5635 from rfl, allE_node, rows5634, irow5630, rows5635]
  all_goals rfl

theorem atot5630 : totK PD2M8K2 D2M8K2.u5630 = [0, 81287500427, 648369811362, 838025638074, 172965331359, 2162517376, 0, 0] := by
  rw [show D2M8K2.u5630 = KTree.node D2M8K2.t5634 (nat_lit 12146483) (nat_lit 1353073914) (nat_lit 0) D2M8K2.t5635 from rfl, totK_node, tot5634, tot5635]
  decide +kernel

theorem arows5632 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5632 = true := by
  rw [show D2M8K2.u5632 = KTree.node D2M8K2.t5636 (nat_lit 12152176) (nat_lit 2715599525) (nat_lit 0) D2M8K2.t5637 from rfl, allE_node, rows5636, irow5632, rows5637]
  all_goals rfl

theorem atot5632 : totK PD2M8K2 D2M8K2.u5632 = [393085608799, 929503798512, 411469400544, 26270542605, 19249816803, 2814597007, 0, 0] := by
  rw [show D2M8K2.u5632 = KTree.node D2M8K2.t5636 (nat_lit 12152176) (nat_lit 2715599525) (nat_lit 0) D2M8K2.t5637 from rfl, totK_node, tot5636, tot5637]
  decide +kernel

theorem arows5633 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5633 = true := by
  rw [show D2M8K2.u5633 = KTree.node D2M8K2.t5638 (nat_lit 12153730) (nat_lit 4099250225) (nat_lit 0) D2M8K2.t5639 from rfl, allE_node, rows5638, irow5633, rows5639]
  all_goals rfl

theorem atot5633 : totK PD2M8K2 D2M8K2.u5633 = [104906017136, 676007980506, 875953767082, 154729851303, 1369150432, 0, 0, 0] := by
  rw [show D2M8K2.u5633 = KTree.node D2M8K2.t5638 (nat_lit 12153730) (nat_lit 4099250225) (nat_lit 0) D2M8K2.t5639 from rfl, totK_node, tot5638, tot5639]
  decide +kernel

theorem arows5636 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5636 = true := by
  rw [show D2M8K2.u5636 = KTree.node D2M8K2.t5640 (nat_lit 12155769) (nat_lit 1314973421) (nat_lit 0) D2M8K2.t5641 from rfl, allE_node, rows5640, irow5636, rows5641]
  all_goals rfl

theorem atot5636 : totK PD2M8K2 D2M8K2.u5636 = [247553607194, 829081453088, 657807588696, 108637480703, 10435995766, 0, 0, 0] := by
  rw [show D2M8K2.u5636 = KTree.node D2M8K2.t5640 (nat_lit 12155769) (nat_lit 1314973421) (nat_lit 0) D2M8K2.t5641 from rfl, totK_node, tot5640, tot5641]
  decide +kernel

theorem arows5637 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5637 = true := by
  rw [show D2M8K2.u5637 = KTree.node D2M8K2.t5642 (nat_lit 12157927) (nat_lit 1851182081) (nat_lit 0) D2M8K2.t5643 from rfl, allE_node, rows5642, irow5637, rows5643]
  all_goals rfl

theorem atot5637 : totK PD2M8K2 D2M8K2.u5637 = [123019054145, 513094873185, 766136970709, 380155014019, 24397703974, 0, 0, 0] := by
  rw [show D2M8K2.u5637 = KTree.node D2M8K2.t5642 (nat_lit 12157927) (nat_lit 1851182081) (nat_lit 0) D2M8K2.t5643 from rfl, totK_node, tot5642, tot5643]
  decide +kernel

theorem arows5639 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5639 = true := by
  rw [show D2M8K2.u5639 = KTree.node D2M8K2.t5644 (nat_lit 12159412) (nat_lit 4012785417) (nat_lit 0) D2M8K2.t5645 from rfl, allE_node, rows5644, irow5639, rows5645]
  all_goals rfl

theorem atot5639 : totK PD2M8K2 D2M8K2.u5639 = [292044685813, 879492801388, 596172199977, 57793450387, 0, 0, 0, 0] := by
  rw [show D2M8K2.u5639 = KTree.node D2M8K2.t5644 (nat_lit 12159412) (nat_lit 4012785417) (nat_lit 0) D2M8K2.t5645 from rfl, totK_node, tot5644, tot5645]
  decide +kernel

theorem arows5640 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5640 = true := by
  rw [show D2M8K2.u5640 = KTree.node D2M8K2.t5646 (nat_lit 12161133) (nat_lit 1440503225) (nat_lit 0) D2M8K2.t5647 from rfl, allE_node, rows5646, irow5640, rows5647]
  all_goals rfl

theorem atot5640 : totK PD2M8K2 D2M8K2.u5640 = [103392314000, 550626519671, 838367680240, 274552072296, 13043783340, 0, 0, 0] := by
  rw [show D2M8K2.u5640 = KTree.node D2M8K2.t5646 (nat_lit 12161133) (nat_lit 1440503225) (nat_lit 0) D2M8K2.t5647 from rfl, totK_node, tot5646, tot5647]
  decide +kernel

theorem arows5644 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5644 = true := by
  rw [show D2M8K2.u5644 = KTree.node D2M8K2.t5648 (nat_lit 12162916) (nat_lit 2895020083) (nat_lit 0) D2M8K2.t5649 from rfl, allE_node, rows5648, irow5644, rows5649]
  all_goals rfl

theorem atot5644 : totK PD2M8K2 D2M8K2.u5644 = [278572038280, 838054840472, 605247169412, 84554318824, 1198073392, 0, 0, 0] := by
  rw [show D2M8K2.u5644 = KTree.node D2M8K2.t5648 (nat_lit 12162916) (nat_lit 2895020083) (nat_lit 0) D2M8K2.t5649 from rfl, totK_node, tot5648, tot5649]
  decide +kernel

theorem arows5645 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5645 = true := by
  rw [show D2M8K2.u5645 = KTree.node D2M8K2.t5650 (nat_lit 12164706) (nat_lit 2341292110) (nat_lit 0) D2M8K2.t5651 from rfl, allE_node, rows5650, irow5645, rows5651]
  all_goals rfl

theorem atot5645 : totK PD2M8K2 D2M8K2.u5645 = [153082395507, 622793290700, 755068304921, 241948558390, 12045711471, 0, 0, 0] := by
  rw [show D2M8K2.u5645 = KTree.node D2M8K2.t5650 (nat_lit 12164706) (nat_lit 2341292110) (nat_lit 0) D2M8K2.t5651 from rfl, totK_node, tot5650, tot5651]
  decide +kernel

theorem arows5647 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5647 = true := by
  rw [show D2M8K2.u5647 = KTree.node D2M8K2.t5652 (nat_lit 12169557) (nat_lit 1286100788) (nat_lit 0) D2M8K2.t5653 from rfl, allE_node, rows5652, irow5647, rows5653]
  all_goals rfl

theorem atot5647 : totK PD2M8K2 D2M8K2.u5647 = [283591591116, 869237279627, 616822254591, 58352406008, 0, 0, 0, 0] := by
  rw [show D2M8K2.u5647 = KTree.node D2M8K2.t5652 (nat_lit 12169557) (nat_lit 1286100788) (nat_lit 0) D2M8K2.t5653 from rfl, totK_node, tot5652, tot5653]
  decide +kernel

theorem arows5648 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5648 = true := by
  rw [show D2M8K2.u5648 = KTree.node D2M8K2.t5654 (nat_lit 12171197) (nat_lit 1537364299) (nat_lit 0) D2M8K2.t5655 from rfl, allE_node, rows5654, irow5648, rows5655]
  all_goals rfl

theorem atot5648 : totK PD2M8K2 D2M8K2.u5648 = [0, 402451428735, 955207135213, 396945072836, 22048779143, 0, 0, 0] := by
  rw [show D2M8K2.u5648 = KTree.node D2M8K2.t5654 (nat_lit 12171197) (nat_lit 1537364299) (nat_lit 0) D2M8K2.t5655 from rfl, totK_node, tot5654, tot5655]
  decide +kernel

theorem arows5651 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5651 = true := by
  rw [show D2M8K2.u5651 = KTree.node D2M8K2.t5656 (nat_lit 12173000) (nat_lit 3769823620) (nat_lit 0) D2M8K2.t5657 from rfl, allE_node, rows5656, irow5651, rows5657]
  all_goals rfl

theorem atot5651 : totK PD2M8K2 D2M8K2.u5651 = [0, 380928668764, 976609394850, 409145327774, 11696221213, 0, 0, 0] := by
  rw [show D2M8K2.u5651 = KTree.node D2M8K2.t5656 (nat_lit 12173000) (nat_lit 3769823620) (nat_lit 0) D2M8K2.t5657 from rfl, totK_node, tot5656, tot5657]
  decide +kernel

theorem arows5652 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5652 = true := by
  rw [show D2M8K2.u5652 = KTree.node D2M8K2.t5658 (nat_lit 12174733) (nat_lit 1048674558) (nat_lit 0) D2M8K2.t5659 from rfl, allE_node, rows5658, irow5652, rows5659]
  all_goals rfl

theorem atot5652 : totK PD2M8K2 D2M8K2.u5652 = [0, 89415162224, 662745141788, 892321617740, 136854895796, 1310285577, 0, 0] := by
  rw [show D2M8K2.u5652 = KTree.node D2M8K2.t5658 (nat_lit 12174733) (nat_lit 1048674558) (nat_lit 0) D2M8K2.t5659 from rfl, totK_node, tot5658, tot5659]
  decide +kernel

theorem arows5654 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5654 = true := by
  rw [show D2M8K2.u5654 = KTree.node D2M8K2.t5660 (nat_lit 12176974) (nat_lit 4014680920) (nat_lit 0) D2M8K2.t5661 from rfl, allE_node, rows5660, irow5654, rows5661]
  all_goals rfl

theorem atot5654 : totK PD2M8K2 D2M8K2.u5654 = [0, 378152797339, 938817096844, 476226707347, 32717351716, 0, 0, 0] := by
  rw [show D2M8K2.u5654 = KTree.node D2M8K2.t5660 (nat_lit 12176974) (nat_lit 4014680920) (nat_lit 0) D2M8K2.t5661 from rfl, totK_node, tot5660, tot5661]
  decide +kernel

theorem arows5655 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5655 = true := by
  rw [show D2M8K2.u5655 = KTree.node D2M8K2.t5662 (nat_lit 12180195) (nat_lit 3384975456) (nat_lit 0) D2M8K2.t5663 from rfl, allE_node, rows5662, irow5655, rows5663]
  all_goals rfl

theorem atot5655 : totK PD2M8K2 D2M8K2.u5655 = [0, 273766285201, 845674142226, 605840687632, 69781198705, 1075657031, 0, 0] := by
  rw [show D2M8K2.u5655 = KTree.node D2M8K2.t5662 (nat_lit 12180195) (nat_lit 3384975456) (nat_lit 0) D2M8K2.t5663 from rfl, totK_node, tot5662, tot5663]
  decide +kernel

theorem arows5660 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5660 = true := by
  rw [show D2M8K2.u5660 = KTree.node D2M8K2.t5664 (nat_lit 12182144) (nat_lit 1875801427) (nat_lit 0) D2M8K2.t5665 from rfl, allE_node, rows5664, irow5660, rows5665]
  all_goals rfl

theorem atot5660 : totK PD2M8K2 D2M8K2.u5660 = [0, 151320461696, 703779669065, 771977028299, 155641075827, 3804183361, 0, 0] := by
  rw [show D2M8K2.u5660 = KTree.node D2M8K2.t5664 (nat_lit 12182144) (nat_lit 1875801427) (nat_lit 0) D2M8K2.t5665 from rfl, totK_node, tot5664, tot5665]
  decide +kernel

theorem arows5661 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5661 = true := by
  rw [show D2M8K2.u5661 = KTree.node D2M8K2.t5666 (nat_lit 12183919) (nat_lit 2428462014) (nat_lit 0) D2M8K2.t5667 from rfl, allE_node, rows5666, irow5661, rows5667]
  all_goals rfl

theorem atot5661 : totK PD2M8K2 D2M8K2.u5661 = [0, 229319394490, 772177419264, 667865742353, 95429116947, 1107157161, 0, 0] := by
  rw [show D2M8K2.u5661 = KTree.node D2M8K2.t5666 (nat_lit 12183919) (nat_lit 2428462014) (nat_lit 0) D2M8K2.t5667 from rfl, totK_node, tot5666, tot5667]
  decide +kernel

theorem arows5663 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5663 = true := by
  rw [show D2M8K2.u5663 = KTree.node D2M8K2.t5668 (nat_lit 12189446) (nat_lit 3472872992) (nat_lit 0) D2M8K2.t5669 from rfl, allE_node, rows5668, irow5663, rows5669]
  all_goals rfl

theorem atot5663 : totK PD2M8K2 D2M8K2.u5663 = [0, 258931515829, 782883450184, 622010465319, 123050854788, 3824247485, 0, 0] := by
  rw [show D2M8K2.u5663 = KTree.node D2M8K2.t5668 (nat_lit 12189446) (nat_lit 3472872992) (nat_lit 0) D2M8K2.t5669 from rfl, totK_node, tot5668, tot5669]
  decide +kernel

theorem arows5664 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5664 = true := by
  rw [show D2M8K2.u5664 = KTree.node D2M8K2.t5670 (nat_lit 12190925) (nat_lit 2163394227) (nat_lit 0) D2M8K2.t5671 from rfl, allE_node, rows5670, irow5664, rows5671]
  all_goals rfl

theorem atot5664 : totK PD2M8K2 D2M8K2.u5664 = [0, 179163009487, 750864457190, 738669519141, 120502419206, 1242138600, 0, 0] := by
  rw [show D2M8K2.u5664 = KTree.node D2M8K2.t5670 (nat_lit 12190925) (nat_lit 2163394227) (nat_lit 0) D2M8K2.t5671 from rfl, totK_node, tot5670, tot5671]
  decide +kernel

theorem arows5667 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5667 = true := by
  rw [show D2M8K2.u5667 = KTree.node D2M8K2.t5672 (nat_lit 12192630) (nat_lit 3503843671) (nat_lit 0) D2M8K2.t5673 from rfl, allE_node, rows5672, irow5667, rows5673]
  all_goals rfl

theorem atot5667 : totK PD2M8K2 D2M8K2.u5667 = [0, 179733180668, 598722139885, 685297606622, 277101523867, 20509029466, 0, 0] := by
  rw [show D2M8K2.u5667 = KTree.node D2M8K2.t5672 (nat_lit 12192630) (nat_lit 3503843671) (nat_lit 0) D2M8K2.t5673 from rfl, totK_node, tot5672, tot5673]
  decide +kernel

theorem arows5668 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5668 = true := by
  rw [show D2M8K2.u5668 = KTree.node D2M8K2.t5674 (nat_lit 12194117) (nat_lit 2344319587) (nat_lit 0) D2M8K2.t5675 from rfl, allE_node, rows5674, irow5668, rows5675]
  all_goals rfl

theorem atot5668 : totK PD2M8K2 D2M8K2.u5668 = [0, 261679133484, 824390621136, 611987530453, 95165573533, 1369150432, 0, 0] := by
  rw [show D2M8K2.u5668 = KTree.node D2M8K2.t5674 (nat_lit 12194117) (nat_lit 2344319587) (nat_lit 0) D2M8K2.t5675 from rfl, totK_node, tot5674, tot5675]
  decide +kernel

theorem arows5670 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5670 = true := by
  rw [show D2M8K2.u5670 = KTree.node D2M8K2.t5676 (nat_lit 12196021) (nat_lit 1170635255) (nat_lit 0) D2M8K2.t5677 from rfl, allE_node, rows5676, irow5670, rows5677]
  all_goals rfl

theorem atot5670 : totK PD2M8K2 D2M8K2.u5670 = [0, 191546648453, 782390520862, 757169387704, 92406684448, 0, 0, 0] := by
  rw [show D2M8K2.u5670 = KTree.node D2M8K2.t5676 (nat_lit 12196021) (nat_lit 1170635255) (nat_lit 0) D2M8K2.t5677 from rfl, totK_node, tot5676, tot5677]
  decide +kernel

theorem arows5671 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5671 = true := by
  rw [show D2M8K2.u5671 = KTree.node D2M8K2.t5678 (nat_lit 12201171) (nat_lit 3549389337) (nat_lit 0) D2M8K2.t5679 from rfl, allE_node, rows5678, irow5671, rows5679]
  all_goals rfl

theorem atot5671 : totK PD2M8K2 D2M8K2.u5671 = [0, 226870681396, 786058311890, 671130848824, 98293119573, 1164319620, 0, 0] := by
  rw [show D2M8K2.u5671 = KTree.node D2M8K2.t5678 (nat_lit 12201171) (nat_lit 3549389337) (nat_lit 0) D2M8K2.t5679 from rfl, totK_node, tot5678, tot5679]
  decide +kernel

theorem arows5675 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5675 = true := by
  rw [show D2M8K2.u5675 = KTree.node D2M8K2.t5680 (nat_lit 12202892) (nat_lit 1938837318) (nat_lit 0) D2M8K2.t5681 from rfl, allE_node, rows5680, irow5675, rows5681]
  all_goals rfl

theorem atot5675 : totK PD2M8K2 D2M8K2.u5675 = [0, 173468932483, 647588306359, 728681240025, 191090354319, 11727338389, 0, 0] := by
  rw [show D2M8K2.u5675 = KTree.node D2M8K2.t5680 (nat_lit 12202892) (nat_lit 1938837318) (nat_lit 0) D2M8K2.t5681 from rfl, totK_node, tot5680, tot5681]
  decide +kernel

theorem arows5676 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5676 = true := by
  rw [show D2M8K2.u5676 = KTree.node D2M8K2.t5682 (nat_lit 12204627) (nat_lit 2636101769) (nat_lit 0) D2M8K2.t5683 from rfl, allE_node, rows5682, irow5676, rows5683]
  all_goals rfl

theorem atot5676 : totK PD2M8K2 D2M8K2.u5676 = [0, 224557982520, 776367774962, 662586538389, 99110460613, 1198073392, 0, 0] := by
  rw [show D2M8K2.u5676 = KTree.node D2M8K2.t5682 (nat_lit 12204627) (nat_lit 2636101769) (nat_lit 0) D2M8K2.t5683 from rfl, totK_node, tot5682, tot5683]
  decide +kernel

theorem arows5678 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5678 = true := by
  rw [show D2M8K2.u5678 = KTree.node D2M8K2.t5684 (nat_lit 12206364) (nat_lit 2904511579) (nat_lit 0) D2M8K2.t5685 from rfl, allE_node, rows5684, irow5678, rows5685]
  all_goals rfl

theorem atot5678 : totK PD2M8K2 D2M8K2.u5678 = [0, 170657820507, 637882253601, 725600177359, 197562526721, 11894306413, 0, 0] := by
  rw [show D2M8K2.u5678 = KTree.node D2M8K2.t5684 (nat_lit 12206364) (nat_lit 2904511579) (nat_lit 0) D2M8K2.t5685 from rfl, totK_node, tot5684, tot5685]
  decide +kernel

theorem arows5679 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5679 = true := by
  rw [show D2M8K2.u5679 = KTree.node D2M8K2.t5686 (nat_lit 12207775) (nat_lit 2316602404) (nat_lit 0) D2M8K2.t5687 from rfl, allE_node, rows5686, irow5679, rows5687]
  all_goals rfl

theorem atot5679 : totK PD2M8K2 D2M8K2.u5679 = [0, 241352487710, 796986616246, 636367310520, 84652118552, 1096505104, 0, 0] := by
  rw [show D2M8K2.u5679 = KTree.node D2M8K2.t5686 (nat_lit 12207775) (nat_lit 2316602404) (nat_lit 0) D2M8K2.t5687 from rfl, totK_node, tot5686, tot5687]
  decide +kernel

theorem arows5682 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5682 = true := by
  rw [show D2M8K2.u5682 = KTree.node D2M8K2.t5688 (nat_lit 12210060) (nat_lit 3603878545) (nat_lit 0) D2M8K2.t5689 from rfl, allE_node, rows5688, irow5682, rows5689]
  all_goals rfl

theorem atot5682 : totK PD2M8K2 D2M8K2.u5682 = [0, 218536155546, 742798318756, 693529633404, 125107817829, 3838026431, 0, 0] := by
  rw [show D2M8K2.u5682 = KTree.node D2M8K2.t5688 (nat_lit 12210060) (nat_lit 3603878545) (nat_lit 0) D2M8K2.t5689 from rfl, totK_node, tot5688, tot5689]
  decide +kernel

theorem arows5683 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5683 = true := by
  rw [show D2M8K2.u5683 = KTree.node D2M8K2.t5690 (nat_lit 12211581) (nat_lit 1316072388) (nat_lit 0) D2M8K2.t5691 from rfl, allE_node, rows5690, irow5683, rows5691]
  all_goals rfl

theorem atot5683 : totK PD2M8K2 D2M8K2.u5683 = [0, 198973252844, 760524917422, 713268993309, 114481951785, 1268739303, 0, 0] := by
  rw [show D2M8K2.u5683 = KTree.node D2M8K2.t5690 (nat_lit 12211581) (nat_lit 1316072388) (nat_lit 0) D2M8K2.t5691 from rfl, totK_node, tot5690, tot5691]
  decide +kernel

theorem arows5685 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5685 = true := by
  rw [show D2M8K2.u5685 = KTree.node D2M8K2.t5692 (nat_lit 12213299) (nat_lit 2907377834) (nat_lit 0) D2M8K2.t5693 from rfl, allE_node, rows5692, irow5685, rows5693]
  all_goals rfl

theorem atot5685 : totK PD2M8K2 D2M8K2.u5685 = [0, 0, 404817541988, 948778222904, 370861837908, 21873045024, 0, 0] := by
  rw [show D2M8K2.u5685 = KTree.node D2M8K2.t5692 (nat_lit 12213299) (nat_lit 2907377834) (nat_lit 0) D2M8K2.t5693 from rfl, totK_node, tot5692, tot5693]
  decide +kernel

theorem arows5686 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5686 = true := by
  rw [show D2M8K2.u5686 = KTree.node D2M8K2.t5694 (nat_lit 12214808) (nat_lit 3602913706) (nat_lit 0) D2M8K2.t5695 from rfl, allE_node, rows5694, irow5686, rows5695]
  all_goals rfl

theorem atot5686 : totK PD2M8K2 D2M8K2.u5686 = [0, 0, 260386920144, 836128525914, 555772653609, 80616805945, 1369150432, 0] := by
  rw [show D2M8K2.u5686 = KTree.node D2M8K2.t5694 (nat_lit 12214808) (nat_lit 3602913706) (nat_lit 0) D2M8K2.t5695 from rfl, totK_node, tot5694, tot5695]
  decide +kernel

theorem arows5692 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5692 = true := by
  rw [show D2M8K2.u5692 = KTree.node D2M8K2.t5696 (nat_lit 12216795) (nat_lit 2279065536) (nat_lit 0) D2M8K2.t5697 from rfl, allE_node, rows5696, irow5692, rows5697]
  all_goals rfl

theorem atot5692 : totK PD2M8K2 D2M8K2.u5692 = [0, 0, 244623093625, 817628746341, 605862889802, 83868456769, 0, 0] := by
  rw [show D2M8K2.u5692 = KTree.node D2M8K2.t5696 (nat_lit 12216795) (nat_lit 2279065536) (nat_lit 0) D2M8K2.t5697 from rfl, totK_node, tot5696, tot5697]
  decide +kernel

theorem arows5693 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5693 = true := by
  rw [show D2M8K2.u5693 = KTree.node D2M8K2.t5698 (nat_lit 12222068) (nat_lit 1804825909) (nat_lit 0) D2M8K2.t5699 from rfl, allE_node, rows5698, irow5693, rows5699]
  all_goals rfl

theorem atot5693 : totK PD2M8K2 D2M8K2.u5693 = [0, 0, 395724745598, 947289391740, 377220418026, 23303047345, 0, 0] := by
  rw [show D2M8K2.u5693 = KTree.node D2M8K2.t5698 (nat_lit 12222068) (nat_lit 1804825909) (nat_lit 0) D2M8K2.t5699 from rfl, totK_node, tot5698, tot5699]
  decide +kernel

theorem arows5695 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5695 = true := by
  rw [show D2M8K2.u5695 = KTree.node D2M8K2.t5700 (nat_lit 12225542) (nat_lit 1845542770) (nat_lit 0) D2M8K2.t5701 from rfl, allE_node, rows5700, irow5695, rows5701]
  all_goals rfl

theorem atot5695 : totK PD2M8K2 D2M8K2.u5695 = [0, 0, 401558084659, 948019655623, 365558995598, 21057410093, 0, 0] := by
  rw [show D2M8K2.u5695 = KTree.node D2M8K2.t5700 (nat_lit 12225542) (nat_lit 1845542770) (nat_lit 0) D2M8K2.t5701 from rfl, totK_node, tot5700, tot5701]
  decide +kernel

theorem arows5696 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5696 = true := by
  rw [show D2M8K2.u5696 = KTree.node D2M8K2.t5702 (nat_lit 12228677) (nat_lit 2334897469) (nat_lit 0) D2M8K2.t5703 from rfl, allE_node, rows5702, irow5696, rows5703]
  all_goals rfl

theorem atot5696 : totK PD2M8K2 D2M8K2.u5696 = [0, 0, 410374151117, 954981303302, 361969804605, 21852174825, 0, 0] := by
  rw [show D2M8K2.u5696 = KTree.node D2M8K2.t5702 (nat_lit 12228677) (nat_lit 2334897469) (nat_lit 0) D2M8K2.t5703 from rfl, totK_node, tot5702, tot5703]
  decide +kernel

theorem arows5699 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5699 = true := by
  rw [show D2M8K2.u5699 = KTree.node D2M8K2.t5704 (nat_lit 12232427) (nat_lit 2898299648) (nat_lit 0) D2M8K2.t5705 from rfl, allE_node, rows5704, irow5699, rows5705]
  all_goals rfl

theorem atot5699 : totK PD2M8K2 D2M8K2.u5699 = [0, 179595312347, 606764254107, 690418446290, 278934413421, 21055313582, 0, 0] := by
  rw [show D2M8K2.u5699 = KTree.node D2M8K2.t5704 (nat_lit 12232427) (nat_lit 2898299648) (nat_lit 0) D2M8K2.t5705 from rfl, totK_node, tot5704, tot5705]
  decide +kernel

theorem arows5700 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5700 = true := by
  rw [show D2M8K2.u5700 = KTree.node D2M8K2.t5706 (nat_lit 12277186) (nat_lit 4040198186) (nat_lit 0) D2M8K2.t5707 from rfl, allE_node, rows5706, irow5700, rows5707]
  all_goals rfl

theorem atot5700 : totK PD2M8K2 D2M8K2.u5700 = [0, 240110420655, 777333901480, 637432793241, 107538351972, 1369150432, 0, 0] := by
  rw [show D2M8K2.u5700 = KTree.node D2M8K2.t5706 (nat_lit 12277186) (nat_lit 4040198186) (nat_lit 0) D2M8K2.t5707 from rfl, totK_node, tot5706, tot5707]
  decide +kernel

theorem arows5702 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5702 = true := by
  rw [show D2M8K2.u5702 = KTree.node D2M8K2.t5708 (nat_lit 12279538) (nat_lit 3806341146) (nat_lit 0) D2M8K2.t5709 from rfl, allE_node, rows5708, irow5702, rows5709]
  all_goals rfl

theorem atot5702 : totK PD2M8K2 D2M8K2.u5702 = [0, 218751181190, 790239581184, 736139353101, 89201722713, 0, 0, 0] := by
  rw [show D2M8K2.u5702 = KTree.node D2M8K2.t5708 (nat_lit 12279538) (nat_lit 3806341146) (nat_lit 0) D2M8K2.t5709 from rfl, totK_node, tot5708, tot5709]
  decide +kernel

theorem arows5703 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5703 = true := by
  rw [show D2M8K2.u5703 = KTree.node D2M8K2.t5710 (nat_lit 12281294) (nat_lit 3882570931) (nat_lit 0) D2M8K2.t5711 from rfl, allE_node, rows5710, irow5703, rows5711]
  all_goals rfl

theorem atot5703 : totK PD2M8K2 D2M8K2.u5703 = [0, 123666052243, 666143314366, 821783106837, 198035629079, 5284349065, 0, 0] := by
  rw [show D2M8K2.u5703 = KTree.node D2M8K2.t5710 (nat_lit 12281294) (nat_lit 3882570931) (nat_lit 0) D2M8K2.t5711 from rfl, totK_node, tot5710, tot5711]
  decide +kernel

theorem arows5707 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5707 = true := by
  rw [show D2M8K2.u5707 = KTree.node D2M8K2.t5712 (nat_lit 12283142) (nat_lit 3793953017) (nat_lit 0) D2M8K2.t5713 from rfl, allE_node, rows5712, irow5707, rows5713]
  all_goals rfl

theorem atot5707 : totK PD2M8K2 D2M8K2.u5707 = [0, 352063365265, 919455406183, 517277390514, 47895961329, 0, 0, 0] := by
  rw [show D2M8K2.u5707 = KTree.node D2M8K2.t5712 (nat_lit 12283142) (nat_lit 3793953017) (nat_lit 0) D2M8K2.t5713 from rfl, totK_node, tot5712, tot5713]
  decide +kernel

theorem arows5708 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5708 = true := by
  rw [show D2M8K2.u5708 = KTree.node D2M8K2.t5714 (nat_lit 12284668) (nat_lit 3936565346) (nat_lit 0) D2M8K2.t5715 from rfl, allE_node, rows5714, irow5708, rows5715]
  all_goals rfl

theorem atot5708 : totK PD2M8K2 D2M8K2.u5708 = [0, 88063885426, 602758564247, 879948693968, 220916061216, 9587713104, 0, 0] := by
  rw [show D2M8K2.u5708 = KTree.node D2M8K2.t5714 (nat_lit 12284668) (nat_lit 3936565346) (nat_lit 0) D2M8K2.t5715 from rfl, totK_node, tot5714, tot5715]
  decide +kernel

theorem arows5710 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5710 = true := by
  rw [show D2M8K2.u5710 = KTree.node D2M8K2.t5716 (nat_lit 12289905) (nat_lit 1824404709) (nat_lit 0) D2M8K2.t5717 from rfl, allE_node, rows5716, irow5710, rows5717]
  all_goals rfl

theorem atot5710 : totK PD2M8K2 D2M8K2.u5710 = [0, 310654526904, 816445701231, 565253309861, 102960138412, 3462014130, 0, 0] := by
  rw [show D2M8K2.u5710 = KTree.node D2M8K2.t5716 (nat_lit 12289905) (nat_lit 1824404709) (nat_lit 0) D2M8K2.t5717 from rfl, totK_node, tot5716, tot5717]
  decide +kernel

theorem arows5711 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5711 = true := by
  rw [show D2M8K2.u5711 = KTree.node D2M8K2.t5718 (nat_lit 12291457) (nat_lit 1410860412) (nat_lit 0) D2M8K2.t5719 from rfl, allE_node, rows5718, irow5711, rows5719]
  all_goals rfl

theorem atot5711 : totK PD2M8K2 D2M8K2.u5711 = [0, 94402016517, 698105128550, 852948199277, 125792738378, 1096505104, 0, 0] := by
  rw [show D2M8K2.u5711 = KTree.node D2M8K2.t5718 (nat_lit 12291457) (nat_lit 1410860412) (nat_lit 0) D2M8K2.t5719 from rfl, totK_node, tot5718, tot5719]
  decide +kernel

theorem arows5714 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5714 = true := by
  rw [show D2M8K2.u5714 = KTree.node D2M8K2.t5720 (nat_lit 12293481) (nat_lit 1644362983) (nat_lit 0) D2M8K2.t5721 from rfl, allE_node, rows5720, irow5714, rows5721]
  all_goals rfl

theorem atot5714 : totK PD2M8K2 D2M8K2.u5714 = [0, 322380613821, 841800922302, 541199193550, 98657039185, 3820764243, 0, 0] := by
  rw [show D2M8K2.u5714 = KTree.node D2M8K2.t5720 (nat_lit 12293481) (nat_lit 1644362983) (nat_lit 0) D2M8K2.t5721 from rfl, totK_node, tot5720, tot5721]
  decide +kernel

theorem arows5715 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5715 = true := by
  rw [show D2M8K2.u5715 = KTree.node D2M8K2.t5722 (nat_lit 12295051) (nat_lit 1351608442) (nat_lit 0) D2M8K2.t5723 from rfl, allE_node, rows5722, irow5715, rows5723]
  all_goals rfl

theorem atot5715 : totK PD2M8K2 D2M8K2.u5715 = [0, 92037872509, 615196053592, 877435610608, 211124627490, 4931655035, 0, 0] := by
  rw [show D2M8K2.u5715 = KTree.node D2M8K2.t5722 (nat_lit 12295051) (nat_lit 1351608442) (nat_lit 0) D2M8K2.t5723 from rfl, totK_node, tot5722, tot5723]
  decide +kernel

theorem arows5717 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5717 = true := by
  rw [show D2M8K2.u5717 = KTree.node D2M8K2.t5724 (nat_lit 12317899) (nat_lit 1441100721) (nat_lit 0) D2M8K2.t5725 from rfl, allE_node, rows5724, irow5717, rows5725]
  all_goals rfl

theorem atot5717 : totK PD2M8K2 D2M8K2.u5717 = [0, 333152629557, 819281743555, 499462707413, 116723529403, 8752647282, 0, 0] := by
  rw [show D2M8K2.u5717 = KTree.node D2M8K2.t5724 (nat_lit 12317899) (nat_lit 1441100721) (nat_lit 0) D2M8K2.t5725 from rfl, totK_node, tot5724, tot5725]
  decide +kernel

theorem arows5718 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5718 = true := by
  rw [show D2M8K2.u5718 = KTree.node D2M8K2.t5726 (nat_lit 12319128) (nat_lit 3570892849) (nat_lit 0) D2M8K2.t5727 from rfl, allE_node, rows5726, irow5718, rows5727]
  all_goals rfl

theorem atot5718 : totK PD2M8K2 D2M8K2.u5718 = [0, 85785976425, 678360025522, 867636078115, 145506311297, 1369150432, 0, 0] := by
  rw [show D2M8K2.u5718 = KTree.node D2M8K2.t5726 (nat_lit 12319128) (nat_lit 3570892849) (nat_lit 0) D2M8K2.t5727 from rfl, totK_node, tot5726, tot5727]
  decide +kernel

theorem arows5723 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5723 = true := by
  rw [show D2M8K2.u5723 = KTree.node D2M8K2.t5728 (nat_lit 12328438) (nat_lit 3488724157) (nat_lit 0) D2M8K2.t5729 from rfl, allE_node, rows5728, irow5723, rows5729]
  all_goals rfl

theorem atot5723 : totK PD2M8K2 D2M8K2.u5723 = [0, 373409849585, 925960456199, 482678601586, 40920656138, 0, 0, 0] := by
  rw [show D2M8K2.u5723 = KTree.node D2M8K2.t5728 (nat_lit 12328438) (nat_lit 3488724157) (nat_lit 0) D2M8K2.t5729 from rfl, totK_node, tot5728, tot5729]
  decide +kernel

theorem arows5724 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5724 = true := by
  rw [show D2M8K2.u5724 = KTree.node D2M8K2.t5730 (nat_lit 12329689) (nat_lit 1219466748) (nat_lit 0) D2M8K2.t5731 from rfl, allE_node, rows5730, irow5724, rows5731]
  all_goals rfl

theorem atot5724 : totK PD2M8K2 D2M8K2.u5724 = [0, 51673496249, 520716937856, 896038910390, 281447470130, 13170675918, 0, 0] := by
  rw [show D2M8K2.u5724 = KTree.node D2M8K2.t5730 (nat_lit 12329689) (nat_lit 1219466748) (nat_lit 0) D2M8K2.t5731 from rfl, totK_node, tot5730, tot5731]
  decide +kernel

theorem arows5726 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5726 = true := by
  rw [show D2M8K2.u5726 = KTree.node D2M8K2.t5732 (nat_lit 12331508) (nat_lit 3232667843) (nat_lit 0) D2M8K2.t5733 from rfl, allE_node, rows5732, irow5726, rows5733]
  all_goals rfl

theorem atot5726 : totK PD2M8K2 D2M8K2.u5726 = [0, 321854507947, 866483214959, 549601505395, 57584958213, 0, 0, 0] := by
  rw [show D2M8K2.u5726 = KTree.node D2M8K2.t5732 (nat_lit 12331508) (nat_lit 3232667843) (nat_lit 0) D2M8K2.t5733 from rfl, totK_node, tot5732, tot5733]
  decide +kernel

theorem arows5727 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5727 = true := by
  rw [show D2M8K2.u5727 = KTree.node D2M8K2.t5734 (nat_lit 12333120) (nat_lit 2688163010) (nat_lit 0) D2M8K2.t5735 from rfl, allE_node, rows5734, irow5727, rows5735]
  all_goals rfl

theorem atot5727 : totK PD2M8K2 D2M8K2.u5727 = [0, 90797758495, 629526971781, 863362869128, 181154942939, 4917684815, 0, 0] := by
  rw [show D2M8K2.u5727 = KTree.node D2M8K2.t5734 (nat_lit 12333120) (nat_lit 2688163010) (nat_lit 0) D2M8K2.t5735 from rfl, totK_node, tot5734, tot5735]
  decide +kernel

theorem arows5730 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5730 = true := by
  rw [show D2M8K2.u5730 = KTree.node D2M8K2.t5736 (nat_lit 12335171) (nat_lit 2964435455) (nat_lit 0) D2M8K2.t5737 from rfl, allE_node, rows5736, irow5730, rows5737]
  all_goals rfl

theorem atot5730 : totK PD2M8K2 D2M8K2.u5730 = [0, 384200531241, 942619394681, 462023171446, 33784692186, 0, 0, 0] := by
  rw [show D2M8K2.u5730 = KTree.node D2M8K2.t5736 (nat_lit 12335171) (nat_lit 2964435455) (nat_lit 0) D2M8K2.t5737 from rfl, totK_node, tot5736, tot5737]
  decide +kernel

theorem arows5731 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5731 = true := by
  rw [show D2M8K2.u5731 = KTree.node D2M8K2.t5738 (nat_lit 12336892) (nat_lit 3936201233) (nat_lit 0) D2M8K2.t5739 from rfl, allE_node, rows5738, irow5731, rows5739]
  all_goals rfl

theorem atot5731 : totK PD2M8K2 D2M8K2.u5731 = [0, 11364832707, 478968796722, 967707390219, 306958702515, 13714665880, 0, 0] := by
  rw [show D2M8K2.u5731 = KTree.node D2M8K2.t5738 (nat_lit 12336892) (nat_lit 3936201233) (nat_lit 0) D2M8K2.t5739 from rfl, totK_node, tot5738, tot5739]
  decide +kernel

theorem arows5733 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5733 = true := by
  rw [show D2M8K2.u5733 = KTree.node D2M8K2.t5740 (nat_lit 12359565) (nat_lit 1446806380) (nat_lit 0) D2M8K2.t5741 from rfl, allE_node, rows5740, irow5733, rows5741]
  all_goals rfl

theorem atot5733 : totK PD2M8K2 D2M8K2.u5733 = [0, 383785088728, 950077123119, 423057787181, 22386190152, 0, 0, 0] := by
  rw [show D2M8K2.u5733 = KTree.node D2M8K2.t5740 (nat_lit 12359565) (nat_lit 1446806380) (nat_lit 0) D2M8K2.t5741 from rfl, totK_node, tot5740, tot5741]
  decide +kernel

theorem arows5734 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5734 = true := by
  rw [show D2M8K2.u5734 = KTree.node D2M8K2.t5742 (nat_lit 12361257) (nat_lit 1805969297) (nat_lit 0) D2M8K2.t5743 from rfl, allE_node, rows5742, irow5734, rows5743]
  all_goals rfl

theorem atot5734 : totK PD2M8K2 D2M8K2.u5734 = [0, 107230901701, 667998389438, 857564495521, 151412109147, 1369150432, 0, 0] := by
  rw [show D2M8K2.u5734 = KTree.node D2M8K2.t5742 (nat_lit 12361257) (nat_lit 1805969297) (nat_lit 0) D2M8K2.t5743 from rfl, totK_node, tot5742, tot5743]
  decide +kernel

theorem arows5738 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5738 = true := by
  rw [show D2M8K2.u5738 = KTree.node D2M8K2.t5744 (nat_lit 12363195) (nat_lit 3452925158) (nat_lit 0) D2M8K2.t5745 from rfl, allE_node, rows5744, irow5738, rows5745]
  all_goals rfl

theorem atot5738 : totK PD2M8K2 D2M8K2.u5738 = [0, 240269807898, 841952608623, 670614325828, 78683148789, 0, 0, 0] := by
  rw [show D2M8K2.u5738 = KTree.node D2M8K2.t5744 (nat_lit 12363195) (nat_lit 3452925158) (nat_lit 0) D2M8K2.t5745 from rfl, totK_node, tot5744, tot5745]
  decide +kernel

theorem arows5739 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5739 = true := by
  rw [show D2M8K2.u5739 = KTree.node D2M8K2.t5746 (nat_lit 12365728) (nat_lit 2821506518) (nat_lit 0) D2M8K2.t5747 from rfl, allE_node, rows5746, irow5739, rows5747]
  all_goals rfl

theorem atot5739 : totK PD2M8K2 D2M8K2.u5739 = [0, 256259430498, 779623796661, 658707722182, 118767874574, 1409560813, 0, 0] := by
  rw [show D2M8K2.u5739 = KTree.node D2M8K2.t5746 (nat_lit 12365728) (nat_lit 2821506518) (nat_lit 0) D2M8K2.t5747 from rfl, totK_node, tot5746, tot5747]
  decide +kernel

theorem arows5741 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5741 = true := by
  rw [show D2M8K2.u5741 = KTree.node D2M8K2.t5748 (nat_lit 12367307) (nat_lit 2842907725) (nat_lit 0) D2M8K2.t5749 from rfl, allE_node, rows5748, irow5741, rows5749]
  all_goals rfl

theorem atot5741 : totK PD2M8K2 D2M8K2.u5741 = [0, 156627329152, 694423841918, 776070612134, 155286175754, 3499003824, 0, 0] := by
  rw [show D2M8K2.u5741 = KTree.node D2M8K2.t5748 (nat_lit 12367307) (nat_lit 2842907725) (nat_lit 0) D2M8K2.t5749 from rfl, totK_node, tot5748, tot5749]
  decide +kernel

theorem arows5742 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5742 = true := by
  rw [show D2M8K2.u5742 = KTree.node D2M8K2.t5750 (nat_lit 12369168) (nat_lit 3736152580) (nat_lit 0) D2M8K2.t5751 from rfl, allE_node, rows5750, irow5742, rows5751]
  all_goals rfl

theorem atot5742 : totK PD2M8K2 D2M8K2.u5742 = [0, 239618105133, 740176605829, 642560020386, 147505112479, 9484445972, 0, 0] := by
  rw [show D2M8K2.u5742 = KTree.node D2M8K2.t5750 (nat_lit 12369168) (nat_lit 3736152580) (nat_lit 0) D2M8K2.t5751 from rfl, totK_node, tot5750, tot5751]
  decide +kernel

theorem arows5745 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5745 = true := by
  rw [show D2M8K2.u5745 = KTree.node D2M8K2.t5752 (nat_lit 12370849) (nat_lit 1503344942) (nat_lit 0) D2M8K2.t5753 from rfl, allE_node, rows5752, irow5745, rows5753]
  all_goals rfl

theorem atot5745 : totK PD2M8K2 D2M8K2.u5745 = [0, 140206794479, 648511290025, 771217137368, 191392908781, 9602367571, 0, 0] := by
  rw [show D2M8K2.u5745 = KTree.node D2M8K2.t5752 (nat_lit 12370849) (nat_lit 1503344942) (nat_lit 0) D2M8K2.t5753 from rfl, totK_node, tot5752, tot5753]
  decide +kernel

theorem arows5746 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5746 = true := by
  rw [show D2M8K2.u5746 = KTree.node D2M8K2.t5754 (nat_lit 12372807) (nat_lit 3638013176) (nat_lit 0) D2M8K2.t5755 from rfl, allE_node, rows5754, irow5746, rows5755]
  all_goals rfl

theorem atot5746 : totK PD2M8K2 D2M8K2.u5746 = [0, 274609792326, 781874386829, 612372888686, 114545491442, 3581949829, 0, 0] := by
  rw [show D2M8K2.u5746 = KTree.node D2M8K2.t5754 (nat_lit 12372807) (nat_lit 3638013176) (nat_lit 0) D2M8K2.t5755 from rfl, totK_node, tot5754, tot5755]
  decide +kernel

theorem arows5748 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5748 = true := by
  rw [show D2M8K2.u5748 = KTree.node D2M8K2.t5756 (nat_lit 12374268) (nat_lit 3200093449) (nat_lit 0) D2M8K2.t5757 from rfl, allE_node, rows5756, irow5748, rows5757]
  all_goals rfl

theorem atot5748 : totK PD2M8K2 D2M8K2.u5748 = [0, 160334737954, 753668991663, 772978691219, 114297444255, 1096505104, 0, 0] := by
  rw [show D2M8K2.u5748 = KTree.node D2M8K2.t5756 (nat_lit 12374268) (nat_lit 3200093449) (nat_lit 0) D2M8K2.t5757 from rfl, totK_node, tot5756, tot5757]
  decide +kernel

theorem arows5749 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5749 = true := by
  rw [show D2M8K2.u5749 = KTree.node D2M8K2.t5758 (nat_lit 12400709) (nat_lit 2344549366) (nat_lit 0) D2M8K2.t5759 from rfl, allE_node, rows5758, irow5749, rows5759]
  all_goals rfl

theorem atot5749 : totK PD2M8K2 D2M8K2.u5749 = [0, 277610372114, 795819581121, 581866949282, 113998459608, 3884009855, 0, 0] := by
  rw [show D2M8K2.u5749 = KTree.node D2M8K2.t5758 (nat_lit 12400709) (nat_lit 2344549366) (nat_lit 0) D2M8K2.t5759 from rfl, totK_node, tot5758, tot5759]
  decide +kernel

theorem arows5756 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5756 = true := by
  rw [show D2M8K2.u5756 = KTree.node D2M8K2.t5760 (nat_lit 12401949) (nat_lit 1454570564) (nat_lit 0) D2M8K2.t5761 from rfl, allE_node, rows5760, irow5756, rows5761]
  all_goals rfl

theorem atot5756 : totK PD2M8K2 D2M8K2.u5756 = [0, 140655743322, 702512672054, 796788457296, 135070918487, 1369150432, 0, 0] := by
  rw [show D2M8K2.u5756 = KTree.node D2M8K2.t5760 (nat_lit 12401949) (nat_lit 1454570564) (nat_lit 0) D2M8K2.t5761 from rfl, totK_node, tot5760, tot5761]
  decide +kernel

theorem arows5757 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5757 = true := by
  rw [show D2M8K2.u5757 = KTree.node D2M8K2.t5762 (nat_lit 12404276) (nat_lit 3498727004) (nat_lit 0) D2M8K2.t5763 from rfl, allE_node, rows5762, irow5757, rows5763]
  all_goals rfl

theorem atot5757 : totK PD2M8K2 D2M8K2.u5757 = [0, 332346884769, 898402896461, 575105670997, 55786530533, 0, 0, 0] := by
  rw [show D2M8K2.u5757 = KTree.node D2M8K2.t5762 (nat_lit 12404276) (nat_lit 3498727004) (nat_lit 0) D2M8K2.t5763 from rfl, totK_node, tot5762, tot5763]
  decide +kernel

theorem arows5759 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5759 = true := by
  rw [show D2M8K2.u5759 = KTree.node D2M8K2.t5764 (nat_lit 12406299) (nat_lit 3638395622) (nat_lit 0) D2M8K2.t5765 from rfl, allE_node, rows5764, irow5759, rows5765]
  all_goals rfl

theorem atot5759 : totK PD2M8K2 D2M8K2.u5759 = [0, 84969655104, 545257569857, 877119934623, 285141118787, 9575627623, 0, 0] := by
  rw [show D2M8K2.u5759 = KTree.node D2M8K2.t5764 (nat_lit 12406299) (nat_lit 3638395622) (nat_lit 0) D2M8K2.t5765 from rfl, totK_node, tot5764, tot5765]
  decide +kernel

theorem arows5760 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5760 = true := by
  rw [show D2M8K2.u5760 = KTree.node D2M8K2.t5766 (nat_lit 12407859) (nat_lit 2503787390) (nat_lit 0) D2M8K2.t5767 from rfl, allE_node, rows5766, irow5760, rows5767]
  all_goals rfl

theorem atot5760 : totK PD2M8K2 D2M8K2.u5760 = [0, 328998826794, 908792763804, 541658435430, 46984755187, 0, 0, 0] := by
  rw [show D2M8K2.u5760 = KTree.node D2M8K2.t5766 (nat_lit 12407859) (nat_lit 2503787390) (nat_lit 0) D2M8K2.t5767 from rfl, totK_node, tot5766, tot5767]
  decide +kernel

theorem arows5763 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5763 = true := by
  rw [show D2M8K2.u5763 = KTree.node D2M8K2.t5768 (nat_lit 12409588) (nat_lit 3769913827) (nat_lit 0) D2M8K2.t5769 from rfl, allE_node, rows5768, irow5763, rows5769]
  all_goals rfl

theorem atot5763 : totK PD2M8K2 D2M8K2.u5763 = [0, 103392314000, 626814609054, 863679569900, 199565447875, 5138457373, 0, 0] := by
  rw [show D2M8K2.u5763 = KTree.node D2M8K2.t5768 (nat_lit 12409588) (nat_lit 3769913827) (nat_lit 0) D2M8K2.t5769 from rfl, totK_node, tot5768, tot5769]
  decide +kernel

theorem arows5764 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5764 = true := by
  rw [show D2M8K2.u5764 = KTree.node D2M8K2.t5770 (nat_lit 12411757) (nat_lit 1116440054) (nat_lit 0) D2M8K2.t5771 from rfl, allE_node, rows5770, irow5764, rows5771]
  all_goals rfl

theorem atot5764 : totK PD2M8K2 D2M8K2.u5764 = [0, 278163170994, 822192973306, 610971025079, 85732928036, 1162515529, 0, 0] := by
  rw [show D2M8K2.u5764 = KTree.node D2M8K2.t5770 (nat_lit 12411757) (nat_lit 1116440054) (nat_lit 0) D2M8K2.t5771 from rfl, totK_node, tot5770, tot5771]
  decide +kernel

theorem arows5766 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5766 = true := by
  rw [show D2M8K2.u5766 = KTree.node D2M8K2.t5772 (nat_lit 12413711) (nat_lit 2139737122) (nat_lit 0) D2M8K2.t5773 from rfl, allE_node, rows5772, irow5766, rows5773]
  all_goals rfl

theorem atot5766 : totK PD2M8K2 D2M8K2.u5766 = [0, 172096877105, 707532141420, 761459028704, 172567186175, 4030866388, 0, 0] := by
  rw [show D2M8K2.u5766 = KTree.node D2M8K2.t5772 (nat_lit 12413711) (nat_lit 2139737122) (nat_lit 0) D2M8K2.t5773 from rfl, totK_node, tot5772, tot5773]
  decide +kernel

theorem arows5767 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5767 = true := by
  rw [show D2M8K2.u5767 = KTree.node D2M8K2.t5774 (nat_lit 12418513) (nat_lit 1354481161) (nat_lit 0) D2M8K2.t5775 from rfl, allE_node, rows5774, irow5767, rows5775]
  all_goals rfl

theorem atot5767 : totK PD2M8K2 D2M8K2.u5767 = [0, 267188702392, 801777232901, 641602845762, 93874980569, 1249641317, 0, 0] := by
  rw [show D2M8K2.u5767 = KTree.node D2M8K2.t5774 (nat_lit 12418513) (nat_lit 1354481161) (nat_lit 0) D2M8K2.t5775 from rfl, totK_node, tot5774, tot5775]
  decide +kernel

theorem arows5771 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5771 = true := by
  rw [show D2M8K2.u5771 = KTree.node D2M8K2.t5776 (nat_lit 12420149) (nat_lit 1073410905) (nat_lit 0) D2M8K2.t5777 from rfl, allE_node, rows5776, irow5771, rows5777]
  all_goals rfl

theorem atot5771 : totK PD2M8K2 D2M8K2.u5771 = [94445126902, 166666727072, 387770865523, 801579093747, 327913004993, 20647649770, 0, 0] := by
  rw [show D2M8K2.u5771 = KTree.node D2M8K2.t5776 (nat_lit 12420149) (nat_lit 1073410905) (nat_lit 0) D2M8K2.t5777 from rfl, totK_node, tot5776, tot5777]
  decide +kernel

theorem arows5772 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5772 = true := by
  rw [show D2M8K2.u5772 = KTree.node D2M8K2.t5778 (nat_lit 12487534) (nat_lit 4004759754) (nat_lit 0) D2M8K2.t5779 from rfl, allE_node, rows5778, irow5772, rows5779]
  all_goals rfl

theorem atot5772 : totK PD2M8K2 D2M8K2.u5772 = [354984806307, 921688645685, 521136038723, 42959671483, 0, 0, 0, 0] := by
  rw [show D2M8K2.u5772 = KTree.node D2M8K2.t5778 (nat_lit 12487534) (nat_lit 4004759754) (nat_lit 0) D2M8K2.t5779 from rfl, totK_node, tot5778, tot5779]
  decide +kernel

theorem arows5774 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5774 = true := by
  rw [show D2M8K2.u5774 = KTree.node D2M8K2.t5780 (nat_lit 12488970) (nat_lit 3128450060) (nat_lit 0) D2M8K2.t5781 from rfl, allE_node, rows5780, irow5774, rows5781]
  all_goals rfl

theorem atot5774 : totK PD2M8K2 D2M8K2.u5774 = [0, 420518501719, 953106997024, 420588747982, 29394892645, 0, 0, 0] := by
  rw [show D2M8K2.u5774 = KTree.node D2M8K2.t5780 (nat_lit 12488970) (nat_lit 3128450060) (nat_lit 0) D2M8K2.t5781 from rfl, totK_node, tot5780, tot5781]
  decide +kernel

theorem arows5775 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5775 = true := by
  rw [show D2M8K2.u5775 = KTree.node D2M8K2.t5782 (nat_lit 12490331) (nat_lit 2843911894) (nat_lit 0) D2M8K2.t5783 from rfl, allE_node, rows5782, irow5775, rows5783]
  all_goals rfl

theorem atot5775 : totK PD2M8K2 D2M8K2.u5775 = [265623211152, 755002759657, 618031970769, 182553939617, 8214505460, 0, 0, 0] := by
  rw [show D2M8K2.u5775 = KTree.node D2M8K2.t5782 (nat_lit 12490331) (nat_lit 2843911894) (nat_lit 0) D2M8K2.t5783 from rfl, totK_node, tot5782, tot5783]
  decide +kernel

theorem arows5778 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5778 = true := by
  rw [show D2M8K2.u5778 = KTree.node D2M8K2.t5784 (nat_lit 12491780) (nat_lit 3261210366) (nat_lit 0) D2M8K2.t5785 from rfl, allE_node, rows5784, irow5778, rows5785]
  all_goals rfl

theorem atot5778 : totK PD2M8K2 D2M8K2.u5778 = [153605049212, 669387572682, 773022223360, 201027094627, 9561477370, 0, 0, 0] := by
  rw [show D2M8K2.u5778 = KTree.node D2M8K2.t5784 (nat_lit 12491780) (nat_lit 3261210366) (nat_lit 0) D2M8K2.t5785 from rfl, totK_node, tot5784, tot5785]
  decide +kernel

theorem arows5779 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5779 = true := by
  rw [show D2M8K2.u5779 = KTree.node D2M8K2.t5786 (nat_lit 12493766) (nat_lit 4180272124) (nat_lit 0) D2M8K2.t5787 from rfl, allE_node, rows5786, irow5779, rows5787]
  all_goals rfl

theorem atot5779 : totK PD2M8K2 D2M8K2.u5779 = [233166955739, 769629553251, 674372326162, 128204478374, 3434488093, 0, 0, 0] := by
  rw [show D2M8K2.u5779 = KTree.node D2M8K2.t5786 (nat_lit 12493766) (nat_lit 4180272124) (nat_lit 0) D2M8K2.t5787 from rfl, totK_node, tot5786, tot5787]
  decide +kernel

theorem arows5781 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5781 = true := by
  rw [show D2M8K2.u5781 = KTree.node D2M8K2.t5788 (nat_lit 12495251) (nat_lit 2725783747) (nat_lit 0) D2M8K2.t5789 from rfl, allE_node, rows5788, irow5781, rows5789]
  all_goals rfl

theorem atot5781 : totK PD2M8K2 D2M8K2.u5781 = [171196667555, 680652672889, 736341846564, 187400831468, 8354962430, 0, 0, 0] := by
  rw [show D2M8K2.u5781 = KTree.node D2M8K2.t5788 (nat_lit 12495251) (nat_lit 2725783747) (nat_lit 0) D2M8K2.t5789 from rfl, totK_node, tot5788, tot5789]
  decide +kernel

theorem arows5782 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5782 = true := by
  rw [show D2M8K2.u5782 = KTree.node D2M8K2.t5790 (nat_lit 12497121) (nat_lit 1744413445) (nat_lit 0) D2M8K2.t5791 from rfl, allE_node, rows5790, irow5782, rows5791]
  all_goals rfl

theorem atot5782 : totK PD2M8K2 D2M8K2.u5782 = [241563486977, 764781205008, 657640930853, 129719547776, 3476815345, 0, 0, 0] := by
  rw [show D2M8K2.u5782 = KTree.node D2M8K2.t5790 (nat_lit 12497121) (nat_lit 1744413445) (nat_lit 0) D2M8K2.t5791 from rfl, totK_node, tot5790, tot5791]
  decide +kernel

theorem arows5787 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5787 = true := by
  rw [show D2M8K2.u5787 = KTree.node D2M8K2.t5792 (nat_lit 12498302) (nat_lit 2978853002) (nat_lit 0) D2M8K2.t5793 from rfl, allE_node, rows5792, irow5787, rows5793]
  all_goals rfl

theorem atot5787 : totK PD2M8K2 D2M8K2.u5787 = [176029280355, 762503688441, 741338460289, 112482398254, 1092001298, 0, 0, 0] := by
  rw [show D2M8K2.u5787 = KTree.node D2M8K2.t5792 (nat_lit 12498302) (nat_lit 2978853002) (nat_lit 0) D2M8K2.t5793 from rfl, totK_node, tot5792, tot5793]
  decide +kernel

theorem arows5788 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5788 = true := by
  rw [show D2M8K2.u5788 = KTree.node D2M8K2.t5794 (nat_lit 12500690) (nat_lit 4113146737) (nat_lit 0) D2M8K2.t5795 from rfl, allE_node, rows5794, irow5788, rows5795]
  all_goals rfl

theorem atot5788 : totK PD2M8K2 D2M8K2.u5788 = [259449790941, 771726042620, 640983465547, 131030793657, 3867150671, 0, 0, 0] := by
  rw [show D2M8K2.u5788 = KTree.node D2M8K2.t5794 (nat_lit 12500690) (nat_lit 4113146737) (nat_lit 0) D2M8K2.t5795 from rfl, totK_node, tot5794, tot5795]
  decide +kernel

theorem arows5790 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5790 = true := by
  rw [show D2M8K2.u5790 = KTree.node D2M8K2.t5796 (nat_lit 12502102) (nat_lit 3542039026) (nat_lit 0) D2M8K2.t5797 from rfl, allE_node, rows5796, irow5790, rows5797]
  all_goals rfl

theorem atot5790 : totK PD2M8K2 D2M8K2.u5790 = [163433783747, 678797254219, 771528941420, 183560191472, 4929677829, 0, 0, 0] := by
  rw [show D2M8K2.u5790 = KTree.node D2M8K2.t5796 (nat_lit 12502102) (nat_lit 3542039026) (nat_lit 0) D2M8K2.t5797 from rfl, totK_node, tot5796, tot5797]
  decide +kernel

theorem arows5791 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5791 = true := by
  rw [show D2M8K2.u5791 = KTree.node D2M8K2.t5798 (nat_lit 12503807) (nat_lit 2760641158) (nat_lit 0) D2M8K2.t5799 from rfl, allE_node, rows5798, irow5791, rows5799]
  all_goals rfl

theorem atot5791 : totK PD2M8K2 D2M8K2.u5791 = [0, 360017547959, 909982559742, 496958481820, 44015152629, 0, 0, 0] := by
  rw [show D2M8K2.u5791 = KTree.node D2M8K2.t5798 (nat_lit 12503807) (nat_lit 2760641158) (nat_lit 0) D2M8K2.t5799 from rfl, totK_node, tot5798, tot5799]
  decide +kernel

theorem arows5794 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5794 = true := by
  rw [show D2M8K2.u5794 = KTree.node D2M8K2.t5800 (nat_lit 12508730) (nat_lit 4243551115) (nat_lit 0) D2M8K2.t5801 from rfl, allE_node, rows5800, irow5794, rows5801]
  all_goals rfl

theorem atot5794 : totK PD2M8K2 D2M8K2.u5794 = [0, 265171907440, 790193541308, 604249115843, 166948425476, 17176948997, 0, 0] := by
  rw [show D2M8K2.u5794 = KTree.node D2M8K2.t5800 (nat_lit 12508730) (nat_lit 4243551115) (nat_lit 0) D2M8K2.t5801 from rfl, totK_node, tot5800, tot5801]
  decide +kernel

theorem arows5795 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5795 = true := by
  rw [show D2M8K2.u5795 = KTree.node D2M8K2.t5802 (nat_lit 12510186) (nat_lit 3788746598) (nat_lit 0) D2M8K2.t5803 from rfl, allE_node, rows5802, irow5795, rows5803]
  all_goals rfl

theorem atot5795 : totK PD2M8K2 D2M8K2.u5795 = [0, 66905027861, 438416513006, 871094598116, 381467759752, 19744924857, 0, 0] := by
  rw [show D2M8K2.u5795 = KTree.node D2M8K2.t5802 (nat_lit 12510186) (nat_lit 3788746598) (nat_lit 0) D2M8K2.t5803 from rfl, totK_node, tot5802, tot5803]
  decide +kernel

theorem arows5797 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5797 = true := by
  rw [show D2M8K2.u5797 = KTree.node D2M8K2.t5804 (nat_lit 12511451) (nat_lit 2325265244) (nat_lit 0) D2M8K2.t5805 from rfl, allE_node, rows5804, irow5797, rows5805]
  all_goals rfl

theorem atot5797 : totK PD2M8K2 D2M8K2.u5797 = [0, 354610372802, 938231194558, 495059055298, 36519752258, 0, 0, 0] := by
  rw [show D2M8K2.u5797 = KTree.node D2M8K2.t5804 (nat_lit 12511451) (nat_lit 2325265244) (nat_lit 0) D2M8K2.t5805 from rfl, totK_node, tot5804, tot5805]
  decide +kernel

theorem arows5798 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5798 = true := by
  rw [show D2M8K2.u5798 = KTree.node D2M8K2.t5806 (nat_lit 12513273) (nat_lit 1796369254) (nat_lit 0) D2M8K2.t5807 from rfl, allE_node, rows5806, irow5798, rows5807]
  all_goals rfl

theorem atot5798 : totK PD2M8K2 D2M8K2.u5798 = [0, 70597915048, 607260236224, 892416763489, 208116353424, 5159868635, 0, 0] := by
  rw [show D2M8K2.u5798 = KTree.node D2M8K2.t5806 (nat_lit 12513273) (nat_lit 1796369254) (nat_lit 0) D2M8K2.t5807 from rfl, totK_node, tot5806, tot5807]
  decide +kernel

theorem arows5802 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5802 = true := by
  rw [show D2M8K2.u5802 = KTree.node D2M8K2.t5808 (nat_lit 12515315) (nat_lit 2930954439) (nat_lit 0) D2M8K2.t5809 from rfl, allE_node, rows5808, irow5802, rows5809]
  all_goals rfl

theorem atot5802 : totK PD2M8K2 D2M8K2.u5802 = [0, 331849252851, 906960919982, 526767644893, 45553987983, 0, 0, 0] := by
  rw [show D2M8K2.u5802 = KTree.node D2M8K2.t5808 (nat_lit 12515315) (nat_lit 2930954439) (nat_lit 0) D2M8K2.t5809 from rfl, totK_node, tot5808, tot5809]
  decide +kernel

theorem arows5803 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5803 = true := by
  rw [show D2M8K2.u5803 = KTree.node D2M8K2.t5810 (nat_lit 12517148) (nat_lit 3403163711) (nat_lit 0) D2M8K2.t5811 from rfl, allE_node, rows5810, irow5803, rows5811]
  all_goals rfl

theorem atot5803 : totK PD2M8K2 D2M8K2.u5803 = [0, 131009799203, 625097131371, 801075728534, 202639432225, 5218872685, 0, 0] := by
  rw [show D2M8K2.u5803 = KTree.node D2M8K2.t5810 (nat_lit 12517148) (nat_lit 3403163711) (nat_lit 0) D2M8K2.t5811 from rfl, totK_node, tot5810, tot5811]
  decide +kernel

theorem arows5805 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5805 = true := by
  rw [show D2M8K2.u5805 = KTree.node D2M8K2.t5812 (nat_lit 12518593) (nat_lit 1443453041) (nat_lit 0) D2M8K2.t5813 from rfl, allE_node, rows5812, irow5805, rows5813]
  all_goals rfl

theorem atot5805 : totK PD2M8K2 D2M8K2.u5805 = [0, 284682994581, 882323818324, 580057712331, 47080077190, 0, 0, 0] := by
  rw [show D2M8K2.u5805 = KTree.node D2M8K2.t5812 (nat_lit 12518593) (nat_lit 1443453041) (nat_lit 0) D2M8K2.t5813 from rfl, totK_node, tot5812, tot5813]
  decide +kernel

theorem arows5806 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5806 = true := by
  rw [show D2M8K2.u5806 = KTree.node D2M8K2.t5814 (nat_lit 12520617) (nat_lit 1920798711) (nat_lit 0) D2M8K2.t5815 from rfl, allE_node, rows5814, irow5806, rows5815]
  all_goals rfl

theorem atot5806 : totK PD2M8K2 D2M8K2.u5806 = [0, 156764870116, 711588364422, 808286074810, 149147217934, 1415142070, 0, 0] := by
  rw [show D2M8K2.u5806 = KTree.node D2M8K2.t5814 (nat_lit 12520617) (nat_lit 1920798711) (nat_lit 0) D2M8K2.t5815 from rfl, totK_node, tot5814, tot5815]
  decide +kernel

theorem arows5809 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5809 = true := by
  rw [show D2M8K2.u5809 = KTree.node D2M8K2.t5816 (nat_lit 12522221) (nat_lit 1613097036) (nat_lit 0) D2M8K2.t5817 from rfl, allE_node, rows5816, irow5809, rows5817]
  all_goals rfl

theorem atot5809 : totK PD2M8K2 D2M8K2.u5809 = [0, 264148052636, 871927498400, 614538618654, 61318094164, 0, 0, 0] := by
  rw [show D2M8K2.u5809 = KTree.node D2M8K2.t5816 (nat_lit 12522221) (nat_lit 1613097036) (nat_lit 0) D2M8K2.t5817 from rfl, totK_node, tot5816, tot5817]
  decide +kernel

theorem arows5810 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5810 = true := by
  rw [show D2M8K2.u5810 = KTree.node D2M8K2.t5818 (nat_lit 12524382) (nat_lit 3909765239) (nat_lit 0) D2M8K2.t5819 from rfl, allE_node, rows5818, irow5810, rows5819]
  all_goals rfl

theorem atot5810 : totK PD2M8K2 D2M8K2.u5810 = [175368045151, 376548395843, 361036186522, 608756896790, 243051069083, 9302370699, 0, 0] := by
  rw [show D2M8K2.u5810 = KTree.node D2M8K2.t5818 (nat_lit 12524382) (nat_lit 3909765239) (nat_lit 0) D2M8K2.t5819 from rfl, totK_node, tot5818, tot5819]
  decide +kernel

theorem arows5812 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5812 = true := by
  rw [show D2M8K2.u5812 = KTree.node D2M8K2.t5820 (nat_lit 12526202) (nat_lit 3231869818) (nat_lit 0) D2M8K2.t5821 from rfl, allE_node, rows5820, irow5812, rows5821]
  all_goals rfl

theorem atot5812 : totK PD2M8K2 D2M8K2.u5812 = [166181834610, 749903286154, 752491051606, 128392037575, 1369150432, 0, 0, 0] := by
  rw [show D2M8K2.u5812 = KTree.node D2M8K2.t5820 (nat_lit 12526202) (nat_lit 3231869818) (nat_lit 0) D2M8K2.t5821 from rfl, totK_node, tot5820, tot5821]
  decide +kernel

theorem arows5813 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5813 = true := by
  rw [show D2M8K2.u5813 = KTree.node D2M8K2.t5822 (nat_lit 12528673) (nat_lit 1372958134) (nat_lit 0) D2M8K2.t5823 from rfl, allE_node, rows5822, irow5813, rows5823]
  all_goals rfl

theorem atot5813 : totK PD2M8K2 D2M8K2.u5813 = [342323677183, 885353523145, 561826037308, 58465253014, 0, 0, 0, 0] := by
  rw [show D2M8K2.u5813 = KTree.node D2M8K2.t5822 (nat_lit 12528673) (nat_lit 1372958134) (nat_lit 0) D2M8K2.t5823 from rfl, totK_node, tot5822, tot5823]
  decide +kernel

theorem arows5819 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5819 = true := by
  rw [show D2M8K2.u5819 = KTree.node D2M8K2.t5824 (nat_lit 12530195) (nat_lit 2709383176) (nat_lit 0) D2M8K2.t5825 from rfl, allE_node, rows5824, irow5819, rows5825]
  all_goals rfl

theorem atot5819 : totK PD2M8K2 D2M8K2.u5819 = [88183717169, 561141768005, 823104330237, 328893707566, 25368447013, 0, 0, 0] := by
  rw [show D2M8K2.u5819 = KTree.node D2M8K2.t5824 (nat_lit 12530195) (nat_lit 2709383176) (nat_lit 0) D2M8K2.t5825 from rfl, totK_node, tot5824, tot5825]
  decide +kernel

theorem arows5820 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5820 = true := by
  rw [show D2M8K2.u5820 = KTree.node D2M8K2.t5826 (nat_lit 12531450) (nat_lit 3209684429) (nat_lit 0) D2M8K2.t5827 from rfl, allE_node, rows5826, irow5820, rows5827]
  all_goals rfl

theorem atot5820 : totK PD2M8K2 D2M8K2.u5820 = [190501719738, 631391882156, 718315795360, 263000118394, 12228669804, 0, 0, 0] := by
  rw [show D2M8K2.u5820 = KTree.node D2M8K2.t5826 (nat_lit 12531450) (nat_lit 3209684429) (nat_lit 0) D2M8K2.t5827 from rfl, totK_node, tot5826, tot5827]
  decide +kernel

theorem arows5822 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5822 = true := by
  rw [show D2M8K2.u5822 = KTree.node D2M8K2.t5828 (nat_lit 12532931) (nat_lit 2891196513) (nat_lit 0) D2M8K2.t5829 from rfl, allE_node, rows5828, irow5822, rows5829]
  all_goals rfl

theorem atot5822 : totK PD2M8K2 D2M8K2.u5822 = [250962557083, 814285290302, 649409273128, 103658929873, 1164319620, 0, 0, 0] := by
  rw [show D2M8K2.u5822 = KTree.node D2M8K2.t5828 (nat_lit 12532931) (nat_lit 2891196513) (nat_lit 0) D2M8K2.t5829 from rfl, totK_node, tot5828, tot5829]
  decide +kernel

theorem arows5823 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5823 = true := by
  rw [show D2M8K2.u5823 = KTree.node D2M8K2.t5830 (nat_lit 12534588) (nat_lit 2648671983) (nat_lit 0) D2M8K2.t5831 from rfl, allE_node, rows5830, irow5823, rows5831]
  all_goals rfl

theorem atot5823 : totK PD2M8K2 D2M8K2.u5823 = [165819165509, 649026042579, 752244272018, 219751171330, 11885407614, 0, 0, 0] := by
  rw [show D2M8K2.u5823 = KTree.node D2M8K2.t5830 (nat_lit 12534588) (nat_lit 2648671983) (nat_lit 0) D2M8K2.t5831 from rfl, totK_node, tot5830, tot5831]
  decide +kernel

theorem arows5826 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5826 = true := by
  rw [show D2M8K2.u5826 = KTree.node D2M8K2.t5832 (nat_lit 12539451) (nat_lit 3405981614) (nat_lit 0) D2M8K2.t5833 from rfl, allE_node, rows5832, irow5826, rows5833]
  all_goals rfl

theorem atot5826 : totK PD2M8K2 D2M8K2.u5826 = [245890294727, 791149505845, 644712521028, 101443298711, 1096505104, 0, 0, 0] := by
  rw [show D2M8K2.u5826 = KTree.node D2M8K2.t5832 (nat_lit 12539451) (nat_lit 3405981614) (nat_lit 0) D2M8K2.t5833 from rfl, totK_node, tot5832, tot5833]
  decide +kernel

theorem arows5827 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5827 = true := by
  rw [show D2M8K2.u5827 = KTree.node D2M8K2.t5834 (nat_lit 12541414) (nat_lit 956019026) (nat_lit 0) D2M8K2.t5835 from rfl, allE_node, rows5834, irow5827, rows5835]
  all_goals rfl

theorem atot5827 : totK PD2M8K2 D2M8K2.u5827 = [167868472426, 720264044029, 771269080717, 156117536684, 3884009855, 0, 0, 0] := by
  rw [show D2M8K2.u5827 = KTree.node D2M8K2.t5834 (nat_lit 12541414) (nat_lit 956019026) (nat_lit 0) D2M8K2.t5835 from rfl, totK_node, tot5834, tot5835]
  decide +kernel

theorem arows5829 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5829 = true := by
  rw [show D2M8K2.u5829 = KTree.node D2M8K2.t5836 (nat_lit 12543295) (nat_lit 2225933713) (nat_lit 0) D2M8K2.t5837 from rfl, allE_node, rows5836, irow5829, rows5837]
  all_goals rfl

theorem atot5829 : totK PD2M8K2 D2M8K2.u5829 = [249247453021, 788969809769, 659363939485, 113682440914, 1268739303, 0, 0, 0] := by
  rw [show D2M8K2.u5829 = KTree.node D2M8K2.t5836 (nat_lit 12543295) (nat_lit 2225933713) (nat_lit 0) D2M8K2.t5837 from rfl, totK_node, tot5836, tot5837]
  decide +kernel

theorem arows5830 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5830 = true := by
  rw [show D2M8K2.u5830 = KTree.node D2M8K2.t5838 (nat_lit 12545018) (nat_lit 4228345622) (nat_lit 0) D2M8K2.t5839 from rfl, allE_node, rows5838, irow5830, rows5839]
  all_goals rfl

theorem atot5830 : totK PD2M8K2 D2M8K2.u5830 = [0, 401275240369, 962021581985, 398266797735, 21979466022, 0, 0, 0] := by
  rw [show D2M8K2.u5830 = KTree.node D2M8K2.t5838 (nat_lit 12545018) (nat_lit 4228345622) (nat_lit 0) D2M8K2.t5839 from rfl, totK_node, tot5838, tot5839]
  decide +kernel

theorem arows5834 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5834 = true := by
  rw [show D2M8K2.u5834 = KTree.node D2M8K2.t5840 (nat_lit 12546799) (nat_lit 1842093190) (nat_lit 0) D2M8K2.t5841 from rfl, allE_node, rows5840, irow5834, rows5841]
  all_goals rfl

theorem atot5834 : totK PD2M8K2 D2M8K2.u5834 = [0, 220171665006, 783318325047, 657692083612, 96165865519, 1206465782, 0, 0] := by
  rw [show D2M8K2.u5834 = KTree.node D2M8K2.t5840 (nat_lit 12546799) (nat_lit 1842093190) (nat_lit 0) D2M8K2.t5841 from rfl, totK_node, tot5840, tot5841]
  decide +kernel

theorem arows5835 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5835 = true := by
  rw [show D2M8K2.u5835 = KTree.node D2M8K2.t5842 (nat_lit 12549328) (nat_lit 3422012555) (nat_lit 0) D2M8K2.t5843 from rfl, allE_node, rows5842, irow5835, rows5843]
  all_goals rfl

theorem atot5835 : totK PD2M8K2 D2M8K2.u5835 = [0, 312013978751, 885477004384, 578511176260, 52379668463, 0, 0, 0] := by
  rw [show D2M8K2.u5835 = KTree.node D2M8K2.t5842 (nat_lit 12549328) (nat_lit 3422012555) (nat_lit 0) D2M8K2.t5843 from rfl, totK_node, tot5842, tot5843]
  decide +kernel

theorem arows5837 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5837 = true := by
  rw [show D2M8K2.u5837 = KTree.node D2M8K2.t5844 (nat_lit 12552326) (nat_lit 3293395900) (nat_lit 0) D2M8K2.t5845 from rfl, allE_node, rows5844, irow5837, rows5845]
  all_goals rfl

theorem atot5837 : totK PD2M8K2 D2M8K2.u5837 = [0, 378636336428, 960631029825, 457424371221, 30410436257, 0, 0, 0] := by
  rw [show D2M8K2.u5837 = KTree.node D2M8K2.t5844 (nat_lit 12552326) (nat_lit 3293395900) (nat_lit 0) D2M8K2.t5845 from rfl, totK_node, tot5844, tot5845]
  decide +kernel

theorem arows5838 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5838 = true := by
  rw [show D2M8K2.u5838 = KTree.node D2M8K2.t5846 (nat_lit 12553810) (nat_lit 4052776618) (nat_lit 0) D2M8K2.t5847 from rfl, allE_node, rows5846, irow5838, rows5847]
  all_goals rfl

theorem atot5838 : totK PD2M8K2 D2M8K2.u5838 = [0, 174790829062, 766400391953, 721499668038, 113562589630, 1162935789, 0, 0] := by
  rw [show D2M8K2.u5838 = KTree.node D2M8K2.t5846 (nat_lit 12553810) (nat_lit 4052776618) (nat_lit 0) D2M8K2.t5847 from rfl, totK_node, tot5846, tot5847]
  decide +kernel

theorem arows5841 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5841 = true := by
  rw [show D2M8K2.u5841 = KTree.node D2M8K2.t5848 (nat_lit 12559157) (nat_lit 2373513152) (nat_lit 0) D2M8K2.t5849 from rfl, allE_node, rows5848, irow5841, rows5849]
  all_goals rfl

theorem atot5841 : totK PD2M8K2 D2M8K2.u5841 = [0, 227750707357, 694547034414, 641910434791, 189464388750, 11853261585, 0, 0] := by
  rw [show D2M8K2.u5841 = KTree.node D2M8K2.t5848 (nat_lit 12559157) (nat_lit 2373513152) (nat_lit 0) D2M8K2.t5849 from rfl, totK_node, tot5848, tot5849]
  decide +kernel

theorem arows5842 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5842 = true := by
  rw [show D2M8K2.u5842 = KTree.node D2M8K2.t5850 (nat_lit 12560429) (nat_lit 2015909635) (nat_lit 0) D2M8K2.t5851 from rfl, allE_node, rows5850, irow5842, rows5851]
  all_goals rfl

theorem atot5842 : totK PD2M8K2 D2M8K2.u5842 = [0, 179018588661, 788329273538, 684166229037, 89513658538, 1021600638, 0, 0] := by
  rw [show D2M8K2.u5842 = KTree.node D2M8K2.t5850 (nat_lit 12560429) (nat_lit 2015909635) (nat_lit 0) D2M8K2.t5851 from rfl, totK_node, tot5850, tot5851]
  decide +kernel

theorem arows5844 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5844 = true := by
  rw [show D2M8K2.u5844 = KTree.node D2M8K2.t5852 (nat_lit 12562889) (nat_lit 1796373502) (nat_lit 0) D2M8K2.t5853 from rfl, allE_node, rows5852, irow5844, rows5853]
  all_goals rfl

theorem atot5844 : totK PD2M8K2 D2M8K2.u5844 = [0, 269484718680, 810467540115, 592430079457, 101657664380, 3552795014, 0, 0] := by
  rw [show D2M8K2.u5844 = KTree.node D2M8K2.t5852 (nat_lit 12562889) (nat_lit 1796373502) (nat_lit 0) D2M8K2.t5853 from rfl, totK_node, tot5852, tot5853]
  decide +kernel

theorem arows5845 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5845 = true := by
  rw [show D2M8K2.u5845 = KTree.node D2M8K2.t5854 (nat_lit 12569840) (nat_lit 3731953676) (nat_lit 0) D2M8K2.t5855 from rfl, allE_node, rows5854, irow5845, rows5855]
  all_goals rfl

theorem atot5845 : totK PD2M8K2 D2M8K2.u5845 = [229587690250, 662261174126, 674768941363, 254864820358, 17297076766, 0, 0, 0] := by
  rw [show D2M8K2.u5845 = KTree.node D2M8K2.t5854 (nat_lit 12569840) (nat_lit 3731953676) (nat_lit 0) D2M8K2.t5855 from rfl, totK_node, tot5854, tot5855]
  decide +kernel

theorem arows5850 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5850 = true := by
  rw [show D2M8K2.u5850 = KTree.node D2M8K2.t5856 (nat_lit 12571042) (nat_lit 4194847968) (nat_lit 0) D2M8K2.t5857 from rfl, allE_node, rows5856, irow5850, rows5857]
  all_goals rfl

theorem atot5850 : totK PD2M8K2 D2M8K2.u5850 = [199975207350, 732907093368, 663751162898, 205617268195, 21393864572, 0, 0, 0] := by
  rw [show D2M8K2.u5850 = KTree.node D2M8K2.t5856 (nat_lit 12571042) (nat_lit 4194847968) (nat_lit 0) D2M8K2.t5857 from rfl, totK_node, tot5856, tot5857]
  decide +kernel

theorem arows5851 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5851 = true := by
  rw [show D2M8K2.u5851 = KTree.node D2M8K2.t5858 (nat_lit 12572530) (nat_lit 3396548944) (nat_lit 0) D2M8K2.t5859 from rfl, allE_node, rows5858, irow5851, rows5859]
  all_goals rfl

theorem atot5851 : totK PD2M8K2 D2M8K2.u5851 = [91239674996, 482730847547, 836611809321, 373048129922, 16201225427, 0, 0, 0] := by
  rw [show D2M8K2.u5851 = KTree.node D2M8K2.t5858 (nat_lit 12572530) (nat_lit 3396548944) (nat_lit 0) D2M8K2.t5859 from rfl, totK_node, tot5858, tot5859]
  decide +kernel

theorem arows5853 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5853 = true := by
  rw [show D2M8K2.u5853 = KTree.node D2M8K2.t5860 (nat_lit 12577540) (nat_lit 2534104025) (nat_lit 0) D2M8K2.t5861 from rfl, allE_node, rows5860, irow5853, rows5861]
  all_goals rfl

theorem atot5853 : totK PD2M8K2 D2M8K2.u5853 = [335628077081, 907050966900, 536832490883, 48950994841, 0, 0, 0, 0] := by
  rw [show D2M8K2.u5853 = KTree.node D2M8K2.t5860 (nat_lit 12577540) (nat_lit 2534104025) (nat_lit 0) D2M8K2.t5861 from rfl, totK_node, tot5860, tot5861]
  decide +kernel

theorem arows5854 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5854 = true := by
  rw [show D2M8K2.u5854 = KTree.node D2M8K2.t5862 (nat_lit 12579217) (nat_lit 1360543781) (nat_lit 0) D2M8K2.t5863 from rfl, allE_node, rows5862, irow5854, rows5863]
  all_goals rfl

theorem atot5854 : totK PD2M8K2 D2M8K2.u5854 = [66525107661, 511773418658, 893034629043, 296781992616, 13250685261, 0, 0, 0] := by
  rw [show D2M8K2.u5854 = KTree.node D2M8K2.t5862 (nat_lit 12579217) (nat_lit 1360543781) (nat_lit 0) D2M8K2.t5863 from rfl, totK_node, tot5862, tot5863]
  decide +kernel

theorem arows5857 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5857 = true := by
  rw [show D2M8K2.u5857 = KTree.node D2M8K2.t5864 (nat_lit 12580629) (nat_lit 1461964138) (nat_lit 0) D2M8K2.t5865 from rfl, allE_node, rows5864, irow5857, rows5865]
  all_goals rfl

theorem atot5857 : totK PD2M8K2 D2M8K2.u5857 = [333550136219, 914315471249, 519734574847, 42500859061, 0, 0, 0, 0] := by
  rw [show D2M8K2.u5857 = KTree.node D2M8K2.t5864 (nat_lit 12580629) (nat_lit 1461964138) (nat_lit 0) D2M8K2.t5865 from rfl, totK_node, tot5864, tot5865]
  decide +kernel

theorem arows5858 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5858 = true := by
  rw [show D2M8K2.u5858 = KTree.node D2M8K2.t5866 (nat_lit 12582534) (nat_lit 3878967719) (nat_lit 0) D2M8K2.t5867 from rfl, allE_node, rows5866, irow5858, rows5867]
  all_goals rfl

theorem atot5858 : totK PD2M8K2 D2M8K2.u5858 = [104907210977, 626946426704, 857366749366, 201705840583, 4980514959, 0, 0, 0] := by
  rw [show D2M8K2.u5858 = KTree.node D2M8K2.t5866 (nat_lit 12582534) (nat_lit 3878967719) (nat_lit 0) D2M8K2.t5867 from rfl, totK_node, tot5866, tot5867]
  decide +kernel

theorem arows5860 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5860 = true := by
  rw [show D2M8K2.u5860 = KTree.node D2M8K2.t5868 (nat_lit 12584274) (nat_lit 3473171918) (nat_lit 0) D2M8K2.t5869 from rfl, allE_node, rows5868, irow5860, rows5869]
  all_goals rfl

theorem atot5860 : totK PD2M8K2 D2M8K2.u5860 = [300928237669, 878894263239, 598680855361, 58178289480, 0, 0, 0, 0] := by
  rw [show D2M8K2.u5860 = KTree.node D2M8K2.t5868 (nat_lit 12584274) (nat_lit 3473171918) (nat_lit 0) D2M8K2.t5869 from rfl, totK_node, tot5868, tot5869]
  decide +kernel

theorem arows5861 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5861 = true := by
  rw [show D2M8K2.u5861 = KTree.node D2M8K2.t5870 (nat_lit 12586004) (nat_lit 3335756601) (nat_lit 0) D2M8K2.t5871 from rfl, allE_node, rows5870, irow5861, rows5871]
  all_goals rfl

theorem atot5861 : totK PD2M8K2 D2M8K2.u5861 = [0, 413693100546, 956780342321, 397712885886, 22006723946, 0, 0, 0] := by
  rw [show D2M8K2.u5861 = KTree.node D2M8K2.t5870 (nat_lit 12586004) (nat_lit 3335756601) (nat_lit 0) D2M8K2.t5871 from rfl, totK_node, tot5870, tot5871]
  decide +kernel

theorem arows5865 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5865 = true := by
  rw [show D2M8K2.u5865 = KTree.node D2M8K2.t5872 (nat_lit 12591224) (nat_lit 3284862567) (nat_lit 0) D2M8K2.t5873 from rfl, allE_node, rows5872, irow5865, rows5873]
  all_goals rfl

theorem atot5865 : totK PD2M8K2 D2M8K2.u5865 = [0, 350687910729, 936621531428, 509752287163, 38243938749, 0, 0, 0] := by
  rw [show D2M8K2.u5865 = KTree.node D2M8K2.t5872 (nat_lit 12591224) (nat_lit 3284862567) (nat_lit 0) D2M8K2.t5873 from rfl, totK_node, tot5872, tot5873]
  decide +kernel

theorem arows5866 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5866 = true := by
  rw [show D2M8K2.u5866 = KTree.node D2M8K2.t5874 (nat_lit 12597677) (nat_lit 1814424662) (nat_lit 0) D2M8K2.t5875 from rfl, allE_node, rows5874, irow5866, rows5875]
  all_goals rfl

theorem atot5866 : totK PD2M8K2 D2M8K2.u5866 = [0, 342274218111, 905646769386, 514790035914, 42759550011, 0, 0, 0] := by
  rw [show D2M8K2.u5866 = KTree.node D2M8K2.t5874 (nat_lit 12597677) (nat_lit 1814424662) (nat_lit 0) D2M8K2.t5875 from rfl, totK_node, tot5874, tot5875]
  decide +kernel

theorem arows5868 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5868 = true := by
  rw [show D2M8K2.u5868 = KTree.node D2M8K2.t5876 (nat_lit 12599237) (nat_lit 1311951113) (nat_lit 0) D2M8K2.t5877 from rfl, allE_node, rows5876, irow5868, rows5877]
  all_goals rfl

theorem atot5868 : totK PD2M8K2 D2M8K2.u5868 = [0, 83317562688, 551625564934, 837653235345, 257319718280, 11596263393, 0, 0] := by
  rw [show D2M8K2.u5868 = KTree.node D2M8K2.t5876 (nat_lit 12599237) (nat_lit 1311951113) (nat_lit 0) D2M8K2.t5877 from rfl, totK_node, tot5876, tot5877]
  decide +kernel

theorem arows5869 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5869 = true := by
  rw [show D2M8K2.u5869 = KTree.node D2M8K2.t5878 (nat_lit 12601102) (nat_lit 3038693825) (nat_lit 0) D2M8K2.t5879 from rfl, allE_node, rows5878, irow5869, rows5879]
  all_goals rfl

theorem atot5869 : totK PD2M8K2 D2M8K2.u5869 = [0, 344463960805, 910264310052, 502146035060, 44683943502, 1509187004, 0, 0] := by
  rw [show D2M8K2.u5869 = KTree.node D2M8K2.t5878 (nat_lit 12601102) (nat_lit 3038693825) (nat_lit 0) D2M8K2.t5879 from rfl, totK_node, tot5878, tot5879]
  decide +kernel

theorem arows5872 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5872 = true := by
  rw [show D2M8K2.u5872 = KTree.node D2M8K2.t5880 (nat_lit 12602931) (nat_lit 3042409412) (nat_lit 0) D2M8K2.t5881 from rfl, allE_node, rows5880, irow5872, rows5881]
  all_goals rfl

theorem atot5872 : totK PD2M8K2 D2M8K2.u5872 = [0, 122637762367, 674151275162, 773041379038, 156610133046, 4720618446, 0, 0] := by
  rw [show D2M8K2.u5872 = KTree.node D2M8K2.t5880 (nat_lit 12602931) (nat_lit 3042409412) (nat_lit 0) D2M8K2.t5881 from rfl, totK_node, tot5880, tot5881]
  decide +kernel

theorem arows5873 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5873 = true := by
  rw [show D2M8K2.u5873 = KTree.node D2M8K2.t5882 (nat_lit 12604811) (nat_lit 2422604085) (nat_lit 0) D2M8K2.t5883 from rfl, allE_node, rows5882, irow5873, rows5883]
  all_goals rfl

theorem atot5873 : totK PD2M8K2 D2M8K2.u5873 = [0, 336806486382, 916816437615, 525865237426, 38008773397, 0, 0, 0] := by
  rw [show D2M8K2.u5873 = KTree.node D2M8K2.t5882 (nat_lit 12604811) (nat_lit 2422604085) (nat_lit 0) D2M8K2.t5883 from rfl, totK_node, tot5882, tot5883]
  decide +kernel

theorem arows5875 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5875 = true := by
  rw [show D2M8K2.u5875 = KTree.node D2M8K2.t5884 (nat_lit 12608365) (nat_lit 1386241413) (nat_lit 0) D2M8K2.t5885 from rfl, allE_node, rows5884, irow5875, rows5885]
  all_goals rfl

theorem atot5875 : totK PD2M8K2 D2M8K2.u5875 = [323576573617, 888382694253, 499781562666, 67552741503, 7093611788, 0, 0, 0] := by
  rw [show D2M8K2.u5875 = KTree.node D2M8K2.t5884 (nat_lit 12608365) (nat_lit 1386241413) (nat_lit 0) D2M8K2.t5885 from rfl, totK_node, tot5884, tot5885]
  decide +kernel

theorem arows5876 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5876 = true := by
  rw [show D2M8K2.u5876 = KTree.node D2M8K2.t5886 (nat_lit 12611278) (nat_lit 3948055517) (nat_lit 0) D2M8K2.t5887 from rfl, allE_node, rows5886, irow5876, rows5887]
  all_goals rfl

theorem atot5876 : totK PD2M8K2 D2M8K2.u5876 = [187237284202, 719348709585, 771444706549, 138235190325, 1369150432, 0, 0, 0] := by
  rw [show D2M8K2.u5876 = KTree.node D2M8K2.t5886 (nat_lit 12611278) (nat_lit 3948055517) (nat_lit 0) D2M8K2.t5887 from rfl, totK_node, tot5886, tot5887]
  decide +kernel

theorem arows5884 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5884 = true := by
  rw [show D2M8K2.u5884 = KTree.node D2M8K2.t5888 (nat_lit 12612437) (nat_lit 2365059334) (nat_lit 0) D2M8K2.t5889 from rfl, allE_node, rows5888, irow5884, rows5889]
  all_goals rfl

theorem atot5884 : totK PD2M8K2 D2M8K2.u5884 = [237791597242, 759257660235, 613051346081, 194340990521, 21396654552, 0, 0, 0] := by
  rw [show D2M8K2.u5884 = KTree.node D2M8K2.t5888 (nat_lit 12612437) (nat_lit 2365059334) (nat_lit 0) D2M8K2.t5889 from rfl, totK_node, tot5888, tot5889]
  decide +kernel

theorem arows5885 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5885 = true := by
  rw [show D2M8K2.u5885 = KTree.node D2M8K2.t5890 (nat_lit 12613903) (nat_lit 2418492676) (nat_lit 0) D2M8K2.t5891 from rfl, allE_node, rows5890, irow5885, rows5891]
  all_goals rfl

theorem atot5885 : totK PD2M8K2 D2M8K2.u5885 = [77790425953, 453121186811, 855801318465, 384508583561, 16205053670, 0, 0, 0] := by
  rw [show D2M8K2.u5885 = KTree.node D2M8K2.t5890 (nat_lit 12613903) (nat_lit 2418492676) (nat_lit 0) D2M8K2.t5891 from rfl, totK_node, tot5890, tot5891]
  decide +kernel

theorem arows5887 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5887 = true := by
  rw [show D2M8K2.u5887 = KTree.node D2M8K2.t5892 (nat_lit 12615177) (nat_lit 1757933004) (nat_lit 0) D2M8K2.t5893 from rfl, allE_node, rows5892, irow5887, rows5893]
  all_goals rfl

theorem atot5887 : totK PD2M8K2 D2M8K2.u5887 = [337643725751, 922099134943, 524144562881, 45033887990, 0, 0, 0, 0] := by
  rw [show D2M8K2.u5887 = KTree.node D2M8K2.t5892 (nat_lit 12615177) (nat_lit 1757933004) (nat_lit 0) D2M8K2.t5893 from rfl, totK_node, tot5892, tot5893]
  decide +kernel

theorem arows5888 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5888 = true := by
  rw [show D2M8K2.u5888 = KTree.node D2M8K2.t5894 (nat_lit 12616901) (nat_lit 2379248141) (nat_lit 0) D2M8K2.t5895 from rfl, allE_node, rows5894, irow5888, rows5895]
  all_goals rfl

theorem atot5888 : totK PD2M8K2 D2M8K2.u5888 = [63578106465, 510961747804, 896657887346, 289500140978, 13049727234, 0, 0, 0] := by
  rw [show D2M8K2.u5888 = KTree.node D2M8K2.t5894 (nat_lit 12616901) (nat_lit 2379248141) (nat_lit 0) D2M8K2.t5895 from rfl, totK_node, tot5894, tot5895]
  decide +kernel

theorem arows5891 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5891 = true := by
  rw [show D2M8K2.u5891 = KTree.node D2M8K2.t5896 (nat_lit 12618937) (nat_lit 1438466239) (nat_lit 0) D2M8K2.t5897 from rfl, allE_node, rows5896, irow5891, rows5897]
  all_goals rfl

theorem atot5891 : totK PD2M8K2 D2M8K2.u5891 = [319963588434, 900958433710, 547050705603, 47671363416, 0, 0, 0, 0] := by
  rw [show D2M8K2.u5891 = KTree.node D2M8K2.t5896 (nat_lit 12618937) (nat_lit 1438466239) (nat_lit 0) D2M8K2.t5897 from rfl, totK_node, tot5896, tot5897]
  decide +kernel

theorem arows5892 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5892 = true := by
  rw [show D2M8K2.u5892 = KTree.node D2M8K2.t5898 (nat_lit 12620723) (nat_lit 2374052666) (nat_lit 0) D2M8K2.t5899 from rfl, allE_node, rows5898, irow5892, rows5899]
  all_goals rfl

theorem atot5892 : totK PD2M8K2 D2M8K2.u5892 = [81042165927, 535772495815, 840971400220, 285744907647, 13250685261, 0, 0, 0] := by
  rw [show D2M8K2.u5892 = KTree.node D2M8K2.t5898 (nat_lit 12620723) (nat_lit 2374052666) (nat_lit 0) D2M8K2.t5899 from rfl, totK_node, tot5898, tot5899]
  decide +kernel

theorem arows5894 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5894 = true := by
  rw [show D2M8K2.u5894 = KTree.node D2M8K2.t5900 (nat_lit 12622136) (nat_lit 3883369881) (nat_lit 0) D2M8K2.t5901 from rfl, allE_node, rows5900, irow5894, rows5901]
  all_goals rfl

theorem atot5894 : totK PD2M8K2 D2M8K2.u5894 = [355265117471, 927234006645, 505208360335, 41144307911, 0, 0, 0, 0] := by
  rw [show D2M8K2.u5894 = KTree.node D2M8K2.t5900 (nat_lit 12622136) (nat_lit 3883369881) (nat_lit 0) D2M8K2.t5901 from rfl, totK_node, tot5900, tot5901]
  decide +kernel

theorem arows5895 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5895 = true := by
  rw [show D2M8K2.u5895 = KTree.node D2M8K2.t5902 (nat_lit 12623939) (nat_lit 2505671132) (nat_lit 0) D2M8K2.t5903 from rfl, allE_node, rows5902, irow5895, rows5903]
  all_goals rfl

theorem atot5895 : totK PD2M8K2 D2M8K2.u5895 = [0, 516193463828, 1003758868277, 264797018658, 6350335412, 0, 0, 0] := by
  rw [show D2M8K2.u5895 = KTree.node D2M8K2.t5902 (nat_lit 12623939) (nat_lit 2505671132) (nat_lit 0) D2M8K2.t5903 from rfl, totK_node, tot5902, tot5903]
  decide +kernel

theorem arows5899 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5899 = true := by
  rw [show D2M8K2.u5899 = KTree.node D2M8K2.t5904 (nat_lit 12629409) (nat_lit 1848497439) (nat_lit 0) D2M8K2.t5905 from rfl, allE_node, rows5904, irow5899, rows5905]
  all_goals rfl

theorem atot5899 : totK PD2M8K2 D2M8K2.u5899 = [0, 237685888945, 808655996074, 606552846521, 83192899818, 1138244013, 0, 0] := by
  rw [show D2M8K2.u5899 = KTree.node D2M8K2.t5904 (nat_lit 12629409) (nat_lit 1848497439) (nat_lit 0) D2M8K2.t5905 from rfl, totK_node, tot5904, tot5905]
  decide +kernel

theorem arows5900 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5900 = true := by
  rw [show D2M8K2.u5900 = KTree.node D2M8K2.t5906 (nat_lit 12632261) (nat_lit 2319155486) (nat_lit 0) D2M8K2.t5907 from rfl, allE_node, rows5906, irow5900, rows5907]
  all_goals rfl

theorem atot5900 : totK PD2M8K2 D2M8K2.u5900 = [0, 299638885864, 861743431408, 581151742686, 60515198416, 0, 0, 0] := by
  rw [show D2M8K2.u5900 = KTree.node D2M8K2.t5906 (nat_lit 12632261) (nat_lit 2319155486) (nat_lit 0) D2M8K2.t5907 from rfl, totK_node, tot5906, tot5907]
  decide +kernel

theorem arows5902 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5902 = true := by
  rw [show D2M8K2.u5902 = KTree.node D2M8K2.t5908 (nat_lit 12635267) (nat_lit 2884618266) (nat_lit 0) D2M8K2.t5909 from rfl, allE_node, rows5908, irow5902, rows5909]
  all_goals rfl

theorem atot5902 : totK PD2M8K2 D2M8K2.u5902 = [0, 386004300568, 962389670098, 444979370406, 21991531313, 0, 0, 0] := by
  rw [show D2M8K2.u5902 = KTree.node D2M8K2.t5908 (nat_lit 12635267) (nat_lit 2884618266) (nat_lit 0) D2M8K2.t5909 from rfl, totK_node, tot5908, tot5909]
  decide +kernel

theorem arows5903 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5903 = true := by
  rw [show D2M8K2.u5903 = KTree.node D2M8K2.t5910 (nat_lit 12636851) (nat_lit 2959544203) (nat_lit 0) D2M8K2.t5911 from rfl, allE_node, rows5910, irow5903, rows5911]
  all_goals rfl

theorem atot5903 : totK PD2M8K2 D2M8K2.u5903 = [0, 370718328112, 947660825108, 465102765766, 26021076400, 0, 0, 0] := by
  rw [show D2M8K2.u5903 = KTree.node D2M8K2.t5910 (nat_lit 12636851) (nat_lit 2959544203) (nat_lit 0) D2M8K2.t5911 from rfl, totK_node, tot5910, tot5911]
  decide +kernel

theorem arows5906 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5906 = true := by
  rw [show D2M8K2.u5906 = KTree.node D2M8K2.t5912 (nat_lit 12640255) (nat_lit 2414965113) (nat_lit 0) D2M8K2.t5913 from rfl, allE_node, rows5912, irow5906, rows5913]
  all_goals rfl

theorem atot5906 : totK PD2M8K2 D2M8K2.u5906 = [0, 340157272650, 935103237982, 486541643182, 30846604236, 0, 0, 0] := by
  rw [show D2M8K2.u5906 = KTree.node D2M8K2.t5912 (nat_lit 12640255) (nat_lit 2414965113) (nat_lit 0) D2M8K2.t5913 from rfl, totK_node, tot5912, tot5913]
  decide +kernel

theorem arows5907 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5907 = true := by
  rw [show D2M8K2.u5907 = KTree.node D2M8K2.t5914 (nat_lit 12643216) (nat_lit 3315343775) (nat_lit 0) D2M8K2.t5915 from rfl, allE_node, rows5914, irow5907, rows5915]
  all_goals rfl

theorem atot5907 : totK PD2M8K2 D2M8K2.u5907 = [0, 261500617688, 808946295661, 584167910679, 88829810235, 1095107716, 0, 0] := by
  rw [show D2M8K2.u5907 = KTree.node D2M8K2.t5914 (nat_lit 12643216) (nat_lit 3315343775) (nat_lit 0) D2M8K2.t5915 from rfl, totK_node, tot5914, tot5915]
  decide +kernel

theorem arows5909 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5909 = true := by
  rw [show D2M8K2.u5909 = KTree.node D2M8K2.t5916 (nat_lit 12648960) (nat_lit 3766812078) (nat_lit 0) D2M8K2.t5917 from rfl, allE_node, rows5916, irow5909, rows5917]
  all_goals rfl

theorem atot5909 : totK PD2M8K2 D2M8K2.u5909 = [204574233286, 483080765663, 488137168731, 480123278365, 119982879582, 3882006667, 0, 0] := by
  rw [show D2M8K2.u5909 = KTree.node D2M8K2.t5916 (nat_lit 12648960) (nat_lit 3766812078) (nat_lit 0) D2M8K2.t5917 from rfl, totK_node, tot5916, tot5917]
  decide +kernel

theorem arows5910 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5910 = true := by
  rw [show D2M8K2.u5910 = KTree.node D2M8K2.t5918 (nat_lit 12650811) (nat_lit 2593689553) (nat_lit 0) D2M8K2.t5919 from rfl, allE_node, rows5918, irow5910, rows5919]
  all_goals rfl

theorem atot5910 : totK PD2M8K2 D2M8K2.u5910 = [149102787199, 715288725042, 819055052088, 143499490076, 1369150432, 0, 0, 0] := by
  rw [show D2M8K2.u5910 = KTree.node D2M8K2.t5918 (nat_lit 12650811) (nat_lit 2593689553) (nat_lit 0) D2M8K2.t5919 from rfl, totK_node, tot5918, tot5919]
  decide +kernel

theorem arows5915 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5915 = true := by
  rw [show D2M8K2.u5915 = KTree.node D2M8K2.t5920 (nat_lit 12653300) (nat_lit 1919359017) (nat_lit 0) D2M8K2.t5921 from rfl, allE_node, rows5920, irow5915, rows5921]
  all_goals rfl

theorem atot5915 : totK PD2M8K2 D2M8K2.u5915 = [372018101113, 925912038198, 485420272010, 40685975731, 0, 0, 0, 0] := by
  rw [show D2M8K2.u5915 = KTree.node D2M8K2.t5920 (nat_lit 12653300) (nat_lit 1919359017) (nat_lit 0) D2M8K2.t5921 from rfl, totK_node, tot5920, tot5921]
  decide +kernel

theorem arows5916 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5916 = true := by
  rw [show D2M8K2.u5916 = KTree.node D2M8K2.t5922 (nat_lit 12654769) (nat_lit 1389355025) (nat_lit 0) D2M8K2.t5923 from rfl, allE_node, rows5922, irow5916, rows5923]
  all_goals rfl

theorem atot5916 : totK PD2M8K2 D2M8K2.u5916 = [23524547868, 472629898651, 891688414541, 391079689516, 29375735501, 0, 0, 0] := by
  rw [show D2M8K2.u5916 = KTree.node D2M8K2.t5922 (nat_lit 12654769) (nat_lit 1389355025) (nat_lit 0) D2M8K2.t5923 from rfl, totK_node, tot5922, tot5923]
  decide +kernel

theorem arows5918 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5918 = true := by
  rw [show D2M8K2.u5918 = KTree.node D2M8K2.t5924 (nat_lit 12656114) (nat_lit 2486520921) (nat_lit 0) D2M8K2.t5925 from rfl, allE_node, rows5924, irow5918, rows5925]
  all_goals rfl

theorem atot5918 : totK PD2M8K2 D2M8K2.u5918 = [258846982003, 722121206047, 642285172566, 199740337096, 8213711289, 0, 0, 0] := by
  rw [show D2M8K2.u5918 = KTree.node D2M8K2.t5924 (nat_lit 12656114) (nat_lit 2486520921) (nat_lit 0) D2M8K2.t5925 from rfl, totK_node, tot5924, tot5925]
  decide +kernel

theorem arows5919 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5919 = true := by
  rw [show D2M8K2.u5919 = KTree.node D2M8K2.t5926 (nat_lit 12657613) (nat_lit 1389735202) (nat_lit 0) D2M8K2.t5927 from rfl, allE_node, rows5926, irow5919, rows5927]
  all_goals rfl

theorem atot5919 : totK PD2M8K2 D2M8K2.u5919 = [157895864527, 697552587108, 785590627841, 168213029402, 2309606161, 0, 0, 0] := by
  rw [show D2M8K2.u5919 = KTree.node D2M8K2.t5926 (nat_lit 12657613) (nat_lit 1389735202) (nat_lit 0) D2M8K2.t5927 from rfl, totK_node, tot5926, tot5927]
  decide +kernel

theorem arows5922 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5922 = true := by
  rw [show D2M8K2.u5922 = KTree.node D2M8K2.t5928 (nat_lit 12659547) (nat_lit 1706199962) (nat_lit 0) D2M8K2.t5929 from rfl, allE_node, rows5928, irow5922, rows5929]
  all_goals rfl

theorem atot5922 : totK PD2M8K2 D2M8K2.u5922 = [242794517466, 746588902645, 655326200495, 160621333532, 9511901980, 0, 0, 0] := by
  rw [show D2M8K2.u5922 = KTree.node D2M8K2.t5928 (nat_lit 12659547) (nat_lit 1706199962) (nat_lit 0) D2M8K2.t5929 from rfl, totK_node, tot5928, tot5929]
  decide +kernel

theorem arows5923 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5923 = true := by
  rw [show D2M8K2.u5923 = KTree.node D2M8K2.t5930 (nat_lit 12661140) (nat_lit 3260124361) (nat_lit 0) D2M8K2.t5931 from rfl, allE_node, rows5930, irow5923, rows5931]
  all_goals rfl

theorem atot5923 : totK PD2M8K2 D2M8K2.u5923 = [142778969255, 662999960168, 775236069879, 205883211164, 9565108570, 0, 0, 0] := by
  rw [show D2M8K2.u5923 = KTree.node D2M8K2.t5930 (nat_lit 12661140) (nat_lit 3260124361) (nat_lit 0) D2M8K2.t5931 from rfl, totK_node, tot5930, tot5931]
  decide +kernel

theorem arows5925 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5925 = true := by
  rw [show D2M8K2.u5925 = KTree.node D2M8K2.t5932 (nat_lit 12666580) (nat_lit 4018806574) (nat_lit 0) D2M8K2.t5933 from rfl, allE_node, rows5932, irow5925, rows5933]
  all_goals rfl

theorem atot5925 : totK PD2M8K2 D2M8K2.u5925 = [281304550224, 816638131804, 620822273498, 107318203330, 2490375975, 0, 0, 0] := by
  rw [show D2M8K2.u5925 = KTree.node D2M8K2.t5932 (nat_lit 12666580) (nat_lit 4018806574) (nat_lit 0) D2M8K2.t5933 from rfl, totK_node, tot5932, tot5933]
  decide +kernel

theorem arows5926 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5926 = true := by
  rw [show D2M8K2.u5926 = KTree.node D2M8K2.t5934 (nat_lit 12667986) (nat_lit 3301074087) (nat_lit 0) D2M8K2.t5935 from rfl, allE_node, rows5934, irow5926, rows5935]
  all_goals rfl

theorem atot5926 : totK PD2M8K2 D2M8K2.u5926 = [159457569863, 692971508072, 783693244254, 170323924466, 2304167554, 0, 0, 0] := by
  rw [show D2M8K2.u5926 = KTree.node D2M8K2.t5934 (nat_lit 12667986) (nat_lit 3301074087) (nat_lit 0) D2M8K2.t5935 from rfl, totK_node, tot5934, tot5935]
  decide +kernel

theorem arows5930 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5930 = true := by
  rw [show D2M8K2.u5930 = KTree.node D2M8K2.t5936 (nat_lit 12669644) (nat_lit 912564667) (nat_lit 0) D2M8K2.t5937 from rfl, allE_node, rows5936, irow5930, rows5937]
  all_goals rfl

theorem atot5930 : totK PD2M8K2 D2M8K2.u5930 = [0, 372836606652, 944205649740, 435540276744, 25080681604, 0, 0, 0] := by
  rw [show D2M8K2.u5930 = KTree.node D2M8K2.t5936 (nat_lit 12669644) (nat_lit 912564667) (nat_lit 0) D2M8K2.t5937 from rfl, totK_node, tot5936, tot5937]
  decide +kernel

theorem arows5931 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5931 = true := by
  rw [show D2M8K2.u5931 = KTree.node D2M8K2.t5938 (nat_lit 12671528) (nat_lit 3680521940) (nat_lit 0) D2M8K2.t5939 from rfl, allE_node, rows5938, irow5931, rows5939]
  all_goals rfl

theorem atot5931 : totK PD2M8K2 D2M8K2.u5931 = [0, 151685377356, 725041355561, 800766173284, 120211371516, 1310285577, 0, 0] := by
  rw [show D2M8K2.u5931 = KTree.node D2M8K2.t5938 (nat_lit 12671528) (nat_lit 3680521940) (nat_lit 0) D2M8K2.t5939 from rfl, totK_node, tot5938, tot5939]
  decide +kernel

theorem arows5933 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5933 = true := by
  rw [show D2M8K2.u5933 = KTree.node D2M8K2.t5940 (nat_lit 12674028) (nat_lit 2680041667) (nat_lit 0) D2M8K2.t5941 from rfl, allE_node, rows5940, irow5933, rows5941]
  all_goals rfl

theorem atot5933 : totK PD2M8K2 D2M8K2.u5933 = [0, 388143077255, 926169911677, 477989013758, 36470799261, 0, 0, 0] := by
  rw [show D2M8K2.u5933 = KTree.node D2M8K2.t5940 (nat_lit 12674028) (nat_lit 2680041667) (nat_lit 0) D2M8K2.t5941 from rfl, totK_node, tot5940, tot5941]
  decide +kernel

theorem arows5934 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5934 = true := by
  rw [show D2M8K2.u5934 = KTree.node D2M8K2.t5942 (nat_lit 12677068) (nat_lit 3862111635) (nat_lit 0) D2M8K2.t5943 from rfl, allE_node, rows5942, irow5934, rows5943]
  all_goals rfl

theorem atot5934 : totK PD2M8K2 D2M8K2.u5934 = [0, 345759653885, 916236744495, 509152391214, 43752990607, 0, 0, 0] := by
  rw [show D2M8K2.u5934 = KTree.node D2M8K2.t5942 (nat_lit 12677068) (nat_lit 3862111635) (nat_lit 0) D2M8K2.t5943 from rfl, totK_node, tot5942, tot5943]
  decide +kernel

theorem arows5937 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5937 = true := by
  rw [show D2M8K2.u5937 = KTree.node D2M8K2.t5944 (nat_lit 12678652) (nat_lit 3926295752) (nat_lit 0) D2M8K2.t5945 from rfl, allE_node, rows5944, irow5937, rows5945]
  all_goals rfl

theorem atot5937 : totK PD2M8K2 D2M8K2.u5937 = [0, 89165724567, 660263443306, 843202598942, 172516258866, 4879840392, 0, 0] := by
  rw [show D2M8K2.u5937 = KTree.node D2M8K2.t5944 (nat_lit 12678652) (nat_lit 3926295752) (nat_lit 0) D2M8K2.t5945 from rfl, totK_node, tot5944, tot5945]
  decide +kernel

theorem arows5938 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5938 = true := by
  rw [show D2M8K2.u5938 = KTree.node D2M8K2.t5946 (nat_lit 12680955) (nat_lit 3755701842) (nat_lit 0) D2M8K2.t5947 from rfl, allE_node, rows5946, irow5938, rows5947]
  all_goals rfl

theorem atot5938 : totK PD2M8K2 D2M8K2.u5938 = [0, 384521480503, 920158965259, 475681315262, 41828180758, 0, 0, 0] := by
  rw [show D2M8K2.u5938 = KTree.node D2M8K2.t5946 (nat_lit 12680955) (nat_lit 3755701842) (nat_lit 0) D2M8K2.t5947 from rfl, totK_node, tot5946, tot5947]
  decide +kernel

theorem arows5940 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5940 = true := by
  rw [show D2M8K2.u5940 = KTree.node D2M8K2.t5948 (nat_lit 12682790) (nat_lit 3640216742) (nat_lit 0) D2M8K2.t5949 from rfl, allE_node, rows5948, irow5940, rows5949]
  all_goals rfl

theorem atot5940 : totK PD2M8K2 D2M8K2.u5940 = [0, 90448202333, 665908043658, 829508873851, 175910860187, 4931404646, 0, 0] := by
  rw [show D2M8K2.u5940 = KTree.node D2M8K2.t5948 (nat_lit 12682790) (nat_lit 3640216742) (nat_lit 0) D2M8K2.t5949 from rfl, totK_node, tot5948, tot5949]
  decide +kernel

theorem arows5941 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5941 = true := by
  rw [show D2M8K2.u5941 = KTree.node D2M8K2.t5950 (nat_lit 12687827) (nat_lit 2941866908) (nat_lit 0) D2M8K2.t5951 from rfl, allE_node, rows5950, irow5941, rows5951]
  all_goals rfl

theorem atot5941 : totK PD2M8K2 D2M8K2.u5941 = [0, 348776167773, 910937352013, 527788055139, 40535789977, 0, 0, 0] := by
  rw [show D2M8K2.u5941 = KTree.node D2M8K2.t5950 (nat_lit 12687827) (nat_lit 2941866908) (nat_lit 0) D2M8K2.t5951 from rfl, totK_node, tot5950, tot5951]
  decide +kernel

theorem arows5947 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5947 = true := by
  rw [show D2M8K2.u5947 = KTree.node D2M8K2.t5952 (nat_lit 12689477) (nat_lit 2240598073) (nat_lit 0) D2M8K2.t5953 from rfl, allE_node, rows5952, irow5947, rows5953]
  all_goals rfl

theorem atot5947 : totK PD2M8K2 D2M8K2.u5947 = [0, 0, 429516129501, 945178986977, 346360961581, 14674109264, 0, 0] := by
  rw [show D2M8K2.u5947 = KTree.node D2M8K2.t5952 (nat_lit 12689477) (nat_lit 2240598073) (nat_lit 0) D2M8K2.t5953 from rfl, totK_node, tot5952, tot5953]
  decide +kernel

theorem arows5948 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5948 = true := by
  rw [show D2M8K2.u5948 = KTree.node D2M8K2.t5954 (nat_lit 12736150) (nat_lit 2981990818) (nat_lit 0) D2M8K2.t5955 from rfl, allE_node, rows5954, irow5948, rows5955]
  all_goals rfl

theorem atot5948 : totK PD2M8K2 D2M8K2.u5948 = [0, 359781790945, 922790570675, 497185751341, 60419589644, 7077058802, 0, 0] := by
  rw [show D2M8K2.u5948 = KTree.node D2M8K2.t5954 (nat_lit 12736150) (nat_lit 2981990818) (nat_lit 0) D2M8K2.t5955 from rfl, totK_node, tot5954, tot5955]
  decide +kernel

theorem arows5950 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5950 = true := by
  rw [show D2M8K2.u5950 = KTree.node D2M8K2.t5956 (nat_lit 12737620) (nat_lit 3638271824) (nat_lit 0) D2M8K2.t5957 from rfl, allE_node, rows5956, irow5950, rows5957]
  all_goals rfl

theorem atot5950 : totK PD2M8K2 D2M8K2.u5950 = [0, 89648142264, 501428431998, 834269544571, 372826601592, 29394892645, 0, 0] := by
  rw [show D2M8K2.u5950 = KTree.node D2M8K2.t5956 (nat_lit 12737620) (nat_lit 3638271824) (nat_lit 0) D2M8K2.t5957 from rfl, totK_node, tot5956, tot5957]
  decide +kernel

theorem arows5951 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5951 = true := by
  rw [show D2M8K2.u5951 = KTree.node D2M8K2.t5958 (nat_lit 12738880) (nat_lit 3744896351) (nat_lit 0) D2M8K2.t5959 from rfl, allE_node, rows5958, irow5951, rows5959]
  all_goals rfl

theorem atot5951 : totK PD2M8K2 D2M8K2.u5951 = [0, 231524243989, 694153908876, 682342427996, 222131792151, 8214505460, 0, 0] := by
  rw [show D2M8K2.u5951 = KTree.node D2M8K2.t5958 (nat_lit 12738880) (nat_lit 3744896351) (nat_lit 0) D2M8K2.t5959 from rfl, totK_node, tot5958, tot5959]
  decide +kernel

theorem arows5954 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5954 = true := by
  rw [show D2M8K2.u5954 = KTree.node D2M8K2.t5960 (nat_lit 12740394) (nat_lit 3616291416) (nat_lit 0) D2M8K2.t5961 from rfl, allE_node, rows5960, irow5954, rows5961]
  all_goals rfl

theorem atot5954 : totK PD2M8K2 D2M8K2.u5954 = [0, 191914153703, 776033337074, 729177223739, 106803229047, 0, 0, 0] := by
  rw [show D2M8K2.u5954 = KTree.node D2M8K2.t5960 (nat_lit 12740394) (nat_lit 3616291416) (nat_lit 0) D2M8K2.t5961 from rfl, totK_node, tot5960, tot5961]
  decide +kernel

theorem arows5955 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5955 = true := by
  rw [show D2M8K2.u5955 = KTree.node D2M8K2.t5962 (nat_lit 12742118) (nat_lit 3974640573) (nat_lit 0) D2M8K2.t5963 from rfl, allE_node, rows5962, irow5955, rows5963]
  all_goals rfl

theorem atot5955 : totK PD2M8K2 D2M8K2.u5955 = [0, 203826198170, 660298062129, 714251521441, 208910897406, 8706415949, 0, 0] := by
  rw [show D2M8K2.u5955 = KTree.node D2M8K2.t5962 (nat_lit 12742118) (nat_lit 3974640573) (nat_lit 0) D2M8K2.t5963 from rfl, totK_node, tot5962, tot5963]
  decide +kernel

theorem arows5957 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5957 = true := by
  rw [show D2M8K2.u5957 = KTree.node D2M8K2.t5964 (nat_lit 12743835) (nat_lit 3642326178) (nat_lit 0) D2M8K2.t5965 from rfl, allE_node, rows5964, irow5957, rows5965]
  all_goals rfl

theorem atot5957 : totK PD2M8K2 D2M8K2.u5957 = [0, 200537425124, 790505638099, 698760806499, 101582035645, 0, 0, 0] := by
  rw [show D2M8K2.u5957 = KTree.node D2M8K2.t5964 (nat_lit 12743835) (nat_lit 3642326178) (nat_lit 0) D2M8K2.t5965 from rfl, totK_node, tot5964, tot5965]
  decide +kernel

theorem arows5958 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5958 = true := by
  rw [show D2M8K2.u5958 = KTree.node D2M8K2.t5966 (nat_lit 12745579) (nat_lit 1614994545) (nat_lit 0) D2M8K2.t5967 from rfl, allE_node, rows5966, irow5958, rows5967]
  all_goals rfl

theorem atot5958 : totK PD2M8K2 D2M8K2.u5958 = [0, 201307096399, 651213003825, 704608692698, 213701880421, 8824320960, 0, 0] := by
  rw [show D2M8K2.u5958 = KTree.node D2M8K2.t5966 (nat_lit 12745579) (nat_lit 1614994545) (nat_lit 0) D2M8K2.t5967 from rfl, totK_node, tot5966, tot5967]
  decide +kernel

theorem arows5962 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5962 = true := by
  rw [show D2M8K2.u5962 = KTree.node D2M8K2.t5968 (nat_lit 12746950) (nat_lit 2928996748) (nat_lit 0) D2M8K2.t5969 from rfl, allE_node, rows5968, irow5962, rows5969]
  all_goals rfl

theorem atot5962 : totK PD2M8K2 D2M8K2.u5962 = [0, 216285670933, 803944709576, 673383274247, 90567357405, 0, 0, 0] := by
  rw [show D2M8K2.u5962 = KTree.node D2M8K2.t5968 (nat_lit 12746950) (nat_lit 2928996748) (nat_lit 0) D2M8K2.t5969 from rfl, totK_node, tot5968, tot5969]
  decide +kernel

theorem arows5963 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5963 = true := by
  rw [show D2M8K2.u5963 = KTree.node D2M8K2.t5970 (nat_lit 12749275) (nat_lit 2185651424) (nat_lit 0) D2M8K2.t5971 from rfl, allE_node, rows5970, irow5963, rows5971]
  all_goals rfl

theorem atot5963 : totK PD2M8K2 D2M8K2.u5963 = [0, 244600658717, 761915537241, 676947771211, 137514778639, 2498823382, 0, 0] := by
  rw [show D2M8K2.u5963 = KTree.node D2M8K2.t5970 (nat_lit 12749275) (nat_lit 2185651424) (nat_lit 0) D2M8K2.t5971 from rfl, totK_node, tot5970, tot5971]
  decide +kernel

theorem arows5965 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5965 = true := by
  rw [show D2M8K2.u5965 = KTree.node D2M8K2.t5972 (nat_lit 12750778) (nat_lit 3946002751) (nat_lit 0) D2M8K2.t5973 from rfl, allE_node, rows5972, irow5965, rows5973]
  all_goals rfl

theorem atot5965 : totK PD2M8K2 D2M8K2.u5965 = [0, 178282915971, 757298298664, 745702866199, 117269514399, 0, 0, 0] := by
  rw [show D2M8K2.u5965 = KTree.node D2M8K2.t5972 (nat_lit 12750778) (nat_lit 3946002751) (nat_lit 0) D2M8K2.t5973 from rfl, totK_node, tot5972, tot5973]
  decide +kernel

theorem arows5966 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5966 = true := by
  rw [show D2M8K2.u5966 = KTree.node D2M8K2.t5974 (nat_lit 12752497) (nat_lit 1446348108) (nat_lit 0) D2M8K2.t5975 from rfl, allE_node, rows5974, irow5966, rows5975]
  all_goals rfl

theorem atot5966 : totK PD2M8K2 D2M8K2.u5966 = [0, 0, 363590239636, 918947883986, 471609732913, 37675614470, 0, 0] := by
  rw [show D2M8K2.u5966 = KTree.node D2M8K2.t5974 (nat_lit 12752497) (nat_lit 1446348108) (nat_lit 0) D2M8K2.t5975 from rfl, totK_node, tot5974, tot5975]
  decide +kernel

theorem arows5969 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5969 = true := by
  rw [show D2M8K2.u5969 = KTree.node D2M8K2.t5976 (nat_lit 12757360) (nat_lit 3412104454) (nat_lit 0) D2M8K2.t5977 from rfl, allE_node, rows5976, irow5969, rows5977]
  all_goals rfl

theorem atot5969 : totK PD2M8K2 D2M8K2.u5969 = [0, 0, 282075261720, 882010228429, 601367008885, 60150495801, 0, 0] := by
  rw [show D2M8K2.u5969 = KTree.node D2M8K2.t5976 (nat_lit 12757360) (nat_lit 3412104454) (nat_lit 0) D2M8K2.t5977 from rfl, totK_node, tot5976, tot5977]
  decide +kernel

theorem arows5970 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5970 = true := by
  rw [show D2M8K2.u5970 = KTree.node D2M8K2.t5978 (nat_lit 12758861) (nat_lit 1631596836) (nat_lit 0) D2M8K2.t5979 from rfl, allE_node, rows5978, irow5970, rows5979]
  all_goals rfl

theorem atot5970 : totK PD2M8K2 D2M8K2.u5970 = [0, 0, 0, 345523079484, 917601998622, 469982158765, 32664942840, 0] := by
  rw [show D2M8K2.u5970 = KTree.node D2M8K2.t5978 (nat_lit 12758861) (nat_lit 1631596836) (nat_lit 0) D2M8K2.t5979 from rfl, totK_node, tot5978, tot5979]
  decide +kernel

theorem arows5972 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5972 = true := by
  rw [show D2M8K2.u5972 = KTree.node D2M8K2.t5980 (nat_lit 12760176) (nat_lit 3525249791) (nat_lit 0) D2M8K2.t5981 from rfl, allE_node, rows5980, irow5972, rows5981]
  all_goals rfl

theorem atot5972 : totK PD2M8K2 D2M8K2.u5972 = [0, 0, 384404061228, 909919468771, 448407345409, 55933488520, 4256931014, 0] := by
  rw [show D2M8K2.u5972 = KTree.node D2M8K2.t5980 (nat_lit 12760176) (nat_lit 3525249791) (nat_lit 0) D2M8K2.t5981 from rfl, totK_node, tot5980, tot5981]
  decide +kernel

theorem arows5973 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5973 = true := by
  rw [show D2M8K2.u5973 = KTree.node D2M8K2.t5982 (nat_lit 12761992) (nat_lit 3841453300) (nat_lit 0) D2M8K2.t5983 from rfl, allE_node, rows5982, irow5973, rows5983]
  all_goals rfl

theorem atot5973 : totK PD2M8K2 D2M8K2.u5973 = [0, 0, 81221884840, 614515262514, 869619281696, 188143965628, 5067863418, 0] := by
  rw [show D2M8K2.u5973 = KTree.node D2M8K2.t5982 (nat_lit 12761992) (nat_lit 3841453300) (nat_lit 0) D2M8K2.t5983 from rfl, totK_node, tot5982, tot5983]
  decide +kernel

theorem arows5978 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5978 = true := by
  rw [show D2M8K2.u5978 = KTree.node D2M8K2.t5984 (nat_lit 12764089) (nat_lit 1431430858) (nat_lit 0) D2M8K2.t5985 from rfl, allE_node, rows5984, irow5978, rows5985]
  all_goals rfl

theorem atot5978 : totK PD2M8K2 D2M8K2.u5978 = [0, 0, 349842359454, 928285935709, 493374441372, 32181744240, 0, 0] := by
  rw [show D2M8K2.u5978 = KTree.node D2M8K2.t5984 (nat_lit 12764089) (nat_lit 1431430858) (nat_lit 0) D2M8K2.t5985 from rfl, totK_node, tot5984, tot5985]
  decide +kernel

theorem arows5979 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5979 = true := by
  rw [show D2M8K2.u5979 = KTree.node D2M8K2.t5986 (nat_lit 12765927) (nat_lit 2441574386) (nat_lit 0) D2M8K2.t5987 from rfl, allE_node, rows5986, irow5979, rows5987]
  all_goals rfl

theorem atot5979 : totK PD2M8K2 D2M8K2.u5979 = [0, 0, 101353593170, 612436810788, 826774457137, 193908973627, 5126512042, 0] := by
  rw [show D2M8K2.u5979 = KTree.node D2M8K2.t5986 (nat_lit 12765927) (nat_lit 2441574386) (nat_lit 0) D2M8K2.t5987 from rfl, totK_node, tot5986, tot5987]
  decide +kernel

theorem arows5981 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5981 = true := by
  rw [show D2M8K2.u5981 = KTree.node D2M8K2.t5988 (nat_lit 12767375) (nat_lit 2037102979) (nat_lit 0) D2M8K2.t5989 from rfl, allE_node, rows5988, irow5981, rows5989]
  all_goals rfl

theorem atot5981 : totK PD2M8K2 D2M8K2.u5981 = [0, 0, 309044063945, 892725514607, 542911420457, 37605010197, 0, 0] := by
  rw [show D2M8K2.u5981 = KTree.node D2M8K2.t5988 (nat_lit 12767375) (nat_lit 2037102979) (nat_lit 0) D2M8K2.t5989 from rfl, totK_node, tot5988, tot5989]
  decide +kernel

theorem arows5982 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5982 = true := by
  rw [show D2M8K2.u5982 = KTree.node D2M8K2.t5990 (nat_lit 12769442) (nat_lit 4067590321) (nat_lit 0) D2M8K2.t5991 from rfl, allE_node, rows5990, irow5982, rows5991]
  all_goals rfl

theorem atot5982 : totK PD2M8K2 D2M8K2.u5982 = [0, 0, 155931650124, 720272674749, 804593688392, 138236141550, 1392055030, 0] := by
  rw [show D2M8K2.u5982 = KTree.node D2M8K2.t5990 (nat_lit 12769442) (nat_lit 4067590321) (nat_lit 0) D2M8K2.t5991 from rfl, totK_node, tot5990, tot5991]
  decide +kernel

theorem arows5985 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5985 = true := by
  rw [show D2M8K2.u5985 = KTree.node D2M8K2.t5992 (nat_lit 12771370) (nat_lit 4022249060) (nat_lit 0) D2M8K2.t5993 from rfl, allE_node, rows5992, irow5985, rows5993]
  all_goals rfl

theorem atot5985 : totK PD2M8K2 D2M8K2.u5985 = [0, 0, 262002907442, 860698984159, 608380965146, 61939985674, 0, 0] := by
  rw [show D2M8K2.u5985 = KTree.node D2M8K2.t5992 (nat_lit 12771370) (nat_lit 4022249060) (nat_lit 0) D2M8K2.t5993 from rfl, totK_node, tot5992, tot5993]
  decide +kernel

theorem arows5986 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5986 = true := by
  rw [show D2M8K2.u5986 = KTree.node D2M8K2.t5994 (nat_lit 12773264) (nat_lit 2418875457) (nat_lit 0) D2M8K2.t5995 from rfl, allE_node, rows5994, irow5986, rows5995]
  all_goals rfl

theorem atot5986 : totK PD2M8K2 D2M8K2.u5986 = [0, 175368045151, 413823448195, 369668989918, 571113624094, 214846132150, 9139067247, 0] := by
  rw [show D2M8K2.u5986 = KTree.node D2M8K2.t5994 (nat_lit 12773264) (nat_lit 2418875457) (nat_lit 0) D2M8K2.t5995 from rfl, totK_node, tot5994, tot5995]
  decide +kernel

theorem arows5988 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5988 = true := by
  rw [show D2M8K2.u5988 = KTree.node D2M8K2.t5996 (nat_lit 12775111) (nat_lit 2297694481) (nat_lit 0) D2M8K2.t5997 from rfl, allE_node, rows5996, irow5988, rows5997]
  all_goals rfl

theorem atot5988 : totK PD2M8K2 D2M8K2.u5988 = [0, 166181834610, 747855749367, 756838180284, 108986158412, 1275377855, 0, 0] := by
  rw [show D2M8K2.u5988 = KTree.node D2M8K2.t5996 (nat_lit 12775111) (nat_lit 2297694481) (nat_lit 0) D2M8K2.t5997 from rfl, totK_node, tot5996, tot5997]
  decide +kernel

theorem arows5989 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.u5989 = true := by
  rw [show D2M8K2.u5989 = KTree.node D2M8K2.t5998 (nat_lit 12777564) (nat_lit 2808163541) (nat_lit 0) D2M8K2.t5999 from rfl, allE_node, rows5998, irow5989, rows5999]
  all_goals rfl

theorem atot5989 : totK PD2M8K2 D2M8K2.u5989 = [0, 342323677183, 907999157355, 532305916697, 50545256189, 0, 0, 0] := by
  rw [show D2M8K2.u5989 = KTree.node D2M8K2.t5998 (nat_lit 12777564) (nat_lit 2808163541) (nat_lit 0) D2M8K2.t5999 from rfl, totK_node, tot5998, tot5999]
  decide +kernel

end QECKChecks.D2M8K2
