import QEC.Count.ChunksK3
import QEC.KChecks.A10K2.A3

namespace QECKChecks.A10K2

open QEC QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem arows4796 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4796 = true := by
  rw [show A10K2.u4796 = KTree.node A10K2.t4800 (nat_lit 75081914) (nat_lit 14957480092) (nat_lit 0) A10K2.t4801 from rfl, allE_node, rows4800, irow4796, rows4801]
  all_goals rfl

theorem atot4796 : totK PA10K2 A10K2.u4796 = [0, 0, 842611296620, 3349042561378, 4031211670406, 1436073775762, 115996238129, 0, 0, 0] := by
  rw [show A10K2.u4796 = KTree.node A10K2.t4800 (nat_lit 75081914) (nat_lit 14957480092) (nat_lit 0) A10K2.t4801 from rfl, totK_node, tot4800, tot4801]
  decide +kernel

theorem arows4797 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4797 = true := by
  rw [show A10K2.u4797 = KTree.node A10K2.t4802 (nat_lit 75086636) (nat_lit 13039352284) (nat_lit 0) A10K2.t4803 from rfl, allE_node, rows4802, irow4797, rows4803]
  all_goals rfl

theorem atot4797 : totK PA10K2 A10K2.u4797 = [0, 0, 401404787705, 2080720106610, 3787840432715, 2599222054220, 561306100060, 31082886609, 0, 0] := by
  rw [show A10K2.u4797 = KTree.node A10K2.t4802 (nat_lit 75086636) (nat_lit 13039352284) (nat_lit 0) A10K2.t4803 from rfl, totK_node, tot4802, tot4803]
  decide +kernel

theorem arows4799 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4799 = true := by
  rw [show A10K2.u4799 = KTree.node A10K2.t4804 (nat_lit 75094380) (nat_lit 12782193965) (nat_lit 0) A10K2.t4805 from rfl, allE_node, rows4804, irow4799, rows4805]
  all_goals rfl

theorem atot4799 : totK PA10K2 A10K2.u4799 = [0, 0, 630424199649, 2926046008907, 4095008048704, 1793091753242, 221986429791, 5885702948, 0, 0] := by
  rw [show A10K2.u4799 = KTree.node A10K2.t4804 (nat_lit 75094380) (nat_lit 12782193965) (nat_lit 0) A10K2.t4805 from rfl, totK_node, tot4804, tot4805]
  decide +kernel

theorem arows4800 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4800 = true := by
  rw [show A10K2.u4800 = KTree.node A10K2.t4806 (nat_lit 75170145) (nat_lit 9072528644) (nat_lit 0) A10K2.t4807 from rfl, allE_node, rows4806, irow4800, rows4807]
  all_goals rfl

theorem atot4800 : totK PA10K2 A10K2.u4800 = [0, 592431485893, 2492307573866, 3749593138452, 2516273709994, 734272809507, 55982429459, 0, 0, 0] := by
  rw [show A10K2.u4800 = KTree.node A10K2.t4806 (nat_lit 75170145) (nat_lit 9072528644) (nat_lit 0) A10K2.t4807 from rfl, totK_node, tot4806, tot4807]
  decide +kernel

theorem arows4803 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4803 = true := by
  rw [show A10K2.u4803 = KTree.node A10K2.t4808 (nat_lit 75179233) (nat_lit 3041727668) (nat_lit 0) A10K2.t4809 from rfl, allE_node, rows4808, irow4803, rows4809]
  all_goals rfl

theorem atot4803 : totK PA10K2 A10K2.u4803 = [0, 663379152110, 2729970104929, 3916116599515, 2171508683275, 402906015781, 12473006693, 0, 0, 0] := by
  rw [show A10K2.u4803 = KTree.node A10K2.t4808 (nat_lit 75179233) (nat_lit 3041727668) (nat_lit 0) A10K2.t4809 from rfl, totK_node, tot4808, tot4809]
  decide +kernel

theorem arows4804 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4804 = true := by
  rw [show A10K2.u4804 = KTree.node A10K2.t4810 (nat_lit 75183899) (nat_lit 9974826297) (nat_lit 0) A10K2.t4811 from rfl, allE_node, rows4810, irow4804, rows4811]
  all_goals rfl

theorem atot4804 : totK PA10K2 A10K2.u4804 = [0, 374309255074, 2054961791460, 3975457578374, 2853382951813, 595866896736, 31452269383, 0, 0, 0] := by
  rw [show A10K2.u4804 = KTree.node A10K2.t4810 (nat_lit 75183899) (nat_lit 9974826297) (nat_lit 0) A10K2.t4811 from rfl, totK_node, tot4810, tot4811]
  decide +kernel

theorem arows4806 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4806 = true := by
  rw [show A10K2.u4806 = KTree.node A10K2.t4812 (nat_lit 75197610) (nat_lit 12206374583) (nat_lit 0) A10K2.t4813 from rfl, allE_node, rows4812, irow4806, rows4813]
  all_goals rfl

theorem atot4806 : totK PA10K2 A10K2.u4806 = [0, 613618390301, 2877369994162, 4210476123838, 1987689830647, 271819530629, 6853348008, 0, 0, 0] := by
  rw [show A10K2.u4806 = KTree.node A10K2.t4812 (nat_lit 75197610) (nat_lit 12206374583) (nat_lit 0) A10K2.t4813 from rfl, totK_node, tot4812, tot4813]
  decide +kernel

theorem arows4807 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4807 = true := by
  rw [show A10K2.u4807 = KTree.node A10K2.t4814 (nat_lit 75202124) (nat_lit 4908538337) (nat_lit 0) A10K2.t4815 from rfl, allE_node, rows4814, irow4807, rows4815]
  all_goals rfl

theorem atot4807 : totK PA10K2 A10K2.u4807 = [0, 0, 1083554177049, 3821450054367, 3953249661101, 1160113563710, 68628332737, 0, 0, 0] := by
  rw [show A10K2.u4807 = KTree.node A10K2.t4814 (nat_lit 75202124) (nat_lit 4908538337) (nat_lit 0) A10K2.t4815 from rfl, totK_node, tot4814, tot4815]
  decide +kernel

theorem arows4811 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4811 = true := by
  rw [show A10K2.u4811 = KTree.node A10K2.t4816 (nat_lit 75209777) (nat_lit 9841484075) (nat_lit 0) A10K2.t4817 from rfl, allE_node, rows4816, irow4811, rows4817]
  all_goals rfl

theorem atot4811 : totK PA10K2 A10K2.u4811 = [0, 0, 523331329943, 2571542552188, 4219287264614, 2324745733125, 302082524244, 6632180018, 0, 0] := by
  rw [show A10K2.u4811 = KTree.node A10K2.t4816 (nat_lit 75209777) (nat_lit 9841484075) (nat_lit 0) A10K2.t4817 from rfl, totK_node, tot4816, tot4817]
  decide +kernel

theorem arows4812 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4812 = true := by
  rw [show A10K2.u4812 = KTree.node A10K2.t4818 (nat_lit 75216100) (nat_lit 11342025568) (nat_lit 0) A10K2.t4819 from rfl, allE_node, rows4818, irow4812, rows4819]
  all_goals rfl

theorem atot4812 : totK PA10K2 A10K2.u4812 = [0, 0, 483047408349, 2520035237053, 4180794004086, 2377812475959, 339563427077, 7047025452, 0, 0] := by
  rw [show A10K2.u4812 = KTree.node A10K2.t4818 (nat_lit 75216100) (nat_lit 11342025568) (nat_lit 0) A10K2.t4819 from rfl, totK_node, tot4818, tot4819]
  decide +kernel

theorem arows4814 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4814 = true := by
  rw [show A10K2.u4814 = KTree.node A10K2.t4820 (nat_lit 75230248) (nat_lit 11990687201) (nat_lit 0) A10K2.t4821 from rfl, allE_node, rows4820, irow4814, rows4821]
  all_goals rfl

theorem atot4814 : totK PA10K2 A10K2.u4814 = [0, 0, 761677496734, 3220759991638, 4154277828059, 1647149542285, 136180009978, 0, 0, 0] := by
  rw [show A10K2.u4814 = KTree.node A10K2.t4820 (nat_lit 75230248) (nat_lit 11990687201) (nat_lit 0) A10K2.t4821 from rfl, totK_node, tot4820, tot4821]
  decide +kernel

theorem arows4815 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4815 = true := by
  rw [show A10K2.u4815 = KTree.node A10K2.t4822 (nat_lit 75234816) (nat_lit 15119108432) (nat_lit 0) A10K2.t4823 from rfl, allE_node, rows4822, irow4815, rows4823]
  all_goals rfl

theorem atot4815 : totK PA10K2 A10K2.u4815 = [374610277362, 1242783310141, 1271872596821, 972816471539, 2373033443632, 2721887583726, 854869586529, 61110126106, 0, 0] := by
  rw [show A10K2.u4815 = KTree.node A10K2.t4822 (nat_lit 75234816) (nat_lit 15119108432) (nat_lit 0) A10K2.t4823 from rfl, totK_node, tot4822, tot4823]
  decide +kernel

theorem arows4818 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4818 = true := by
  rw [show A10K2.u4818 = KTree.node A10K2.t4824 (nat_lit 75501495) (nat_lit 15155692245) (nat_lit 0) A10K2.t4825 from rfl, allE_node, rows4824, irow4818, rows4825]
  all_goals rfl

theorem atot4818 : totK PA10K2 A10K2.u4818 = [462785603557, 2425287941274, 3940357236779, 2220661879425, 413774448885, 25371180993, 0, 0, 0, 0] := by
  rw [show A10K2.u4818 = KTree.node A10K2.t4824 (nat_lit 75501495) (nat_lit 15155692245) (nat_lit 0) A10K2.t4825 from rfl, totK_node, tot4824, tot4825]
  decide +kernel

theorem arows4819 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4819 = true := by
  rw [show A10K2.u4819 = KTree.node A10K2.t4826 (nat_lit 75514694) (nat_lit 10317107059) (nat_lit 0) A10K2.t4827 from rfl, allE_node, rows4826, irow4819, rows4827]
  all_goals rfl

theorem atot4819 : totK PA10K2 A10K2.u4819 = [747310367277, 2974344482138, 3796668221086, 1703804701479, 230836402911, 5460492893, 0, 0, 0, 0] := by
  rw [show A10K2.u4819 = KTree.node A10K2.t4826 (nat_lit 75514694) (nat_lit 10317107059) (nat_lit 0) A10K2.t4827 from rfl, totK_node, tot4826, tot4827]
  decide +kernel

theorem arows4821 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4821 = true := by
  rw [show A10K2.u4821 = KTree.node A10K2.t4828 (nat_lit 75520804) (nat_lit 14092073173) (nat_lit 0) A10K2.t4829 from rfl, allE_node, rows4828, irow4821, rows4829]
  all_goals rfl

theorem atot4821 : totK PA10K2 A10K2.u4821 = [625789152892, 2711711900473, 3965335978686, 2081020437353, 300948640468, 6354482628, 0, 0, 0, 0] := by
  rw [show A10K2.u4821 = KTree.node A10K2.t4828 (nat_lit 75520804) (nat_lit 14092073173) (nat_lit 0) A10K2.t4829 from rfl, totK_node, tot4828, tot4829]
  decide +kernel

theorem arows4822 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4822 = true := by
  rw [show A10K2.u4822 = KTree.node A10K2.t4830 (nat_lit 75528127) (nat_lit 14162250694) (nat_lit 0) A10K2.t4831 from rfl, allE_node, rows4830, irow4822, rows4831]
  all_goals rfl

theorem atot4822 : totK PA10K2 A10K2.u4822 = [0, 1271959814870, 4076118560268, 3670237639584, 912109953256, 49555253812, 0, 0, 0, 0] := by
  rw [show A10K2.u4822 = KTree.node A10K2.t4830 (nat_lit 75528127) (nat_lit 14162250694) (nat_lit 0) A10K2.t4831 from rfl, totK_node, tot4830, tot4831]
  decide +kernel

theorem arows4827 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4827 = true := by
  rw [show A10K2.u4827 = KTree.node A10K2.t4832 (nat_lit 75533825) (nat_lit 10449602172) (nat_lit 0) A10K2.t4833 from rfl, allE_node, rows4832, irow4827, rows4833]
  all_goals rfl

theorem atot4827 : totK PA10K2 A10K2.u4827 = [0, 524717092464, 2557869631526, 3890462993417, 2042841941922, 411082756590, 25239774317, 0, 0, 0] := by
  rw [show A10K2.u4827 = KTree.node A10K2.t4832 (nat_lit 75533825) (nat_lit 10449602172) (nat_lit 0) A10K2.t4833 from rfl, totK_node, tot4832, tot4833]
  decide +kernel

theorem arows4828 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4828 = true := by
  rw [show A10K2.u4828 = KTree.node A10K2.t4834 (nat_lit 75547199) (nat_lit 9723813420) (nat_lit 0) A10K2.t4835 from rfl, allE_node, rows4834, irow4828, rows4835]
  all_goals rfl

theorem atot4828 : totK PA10K2 A10K2.u4828 = [0, 745113170429, 3027165060235, 3796738061650, 1570994130505, 201551373091, 5410721913, 0, 0, 0] := by
  rw [show A10K2.u4828 = KTree.node A10K2.t4834 (nat_lit 75547199) (nat_lit 9723813420) (nat_lit 0) A10K2.t4835 from rfl, totK_node, tot4834, tot4835]
  decide +kernel

theorem arows4830 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4830 = true := by
  rw [show A10K2.u4830 = KTree.node A10K2.t4836 (nat_lit 75553581) (nat_lit 6600309105) (nat_lit 0) A10K2.t4837 from rfl, allE_node, rows4836, irow4830, rows4837]
  all_goals rfl

theorem atot4830 : totK PA10K2 A10K2.u4830 = [0, 623341764251, 2821007664912, 4101444746940, 1824327648671, 219178372242, 5546304973, 0, 0, 0] := by
  rw [show A10K2.u4830 = KTree.node A10K2.t4836 (nat_lit 75553581) (nat_lit 6600309105) (nat_lit 0) A10K2.t4837 from rfl, totK_node, tot4836, tot4837]
  decide +kernel

theorem arows4831 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4831 = true := by
  rw [show A10K2.u4831 = KTree.node A10K2.t4838 (nat_lit 75630700) (nat_lit 11667306728) (nat_lit 0) A10K2.t4839 from rfl, allE_node, rows4838, irow4831, rows4839]
  all_goals rfl

theorem atot4831 : totK PA10K2 A10K2.u4831 = [778776062315, 2993307346246, 3639900102036, 1825719180365, 516148691465, 43925757666, 0, 0, 0, 0] := by
  rw [show A10K2.u4831 = KTree.node A10K2.t4838 (nat_lit 75630700) (nat_lit 11667306728) (nat_lit 0) A10K2.t4839 from rfl, totK_node, tot4838, tot4839]
  decide +kernel

theorem arows4834 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4834 = true := by
  rw [show A10K2.u4834 = KTree.node A10K2.t4840 (nat_lit 75635752) (nat_lit 12665709491) (nat_lit 0) A10K2.t4841 from rfl, allE_node, rows4840, irow4834, rows4841]
  all_goals rfl

theorem atot4834 : totK PA10K2 A10K2.u4834 = [519258088118, 2183506294521, 3726814370078, 2561446753310, 546695252997, 30831673886, 0, 0, 0, 0] := by
  rw [show A10K2.u4834 = KTree.node A10K2.t4840 (nat_lit 75635752) (nat_lit 12665709491) (nat_lit 0) A10K2.t4841 from rfl, totK_node, tot4840, tot4841]
  decide +kernel

theorem arows4835 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4835 = true := by
  rw [show A10K2.u4835 = KTree.node A10K2.t4842 (nat_lit 75643094) (nat_lit 12338645780) (nat_lit 0) A10K2.t4843 from rfl, allE_node, rows4842, irow4835, rows4843]
  all_goals rfl

theorem atot4835 : totK PA10K2 A10K2.u4835 = [418098136616, 2186665006337, 3818640427982, 2528244991100, 551104862808, 31768748853, 0, 0, 0, 0] := by
  rw [show A10K2.u4835 = KTree.node A10K2.t4842 (nat_lit 75643094) (nat_lit 12338645780) (nat_lit 0) A10K2.t4843 from rfl, totK_node, tot4842, tot4843]
  decide +kernel

theorem arows4837 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4837 = true := by
  rw [show A10K2.u4837 = KTree.node A10K2.t4844 (nat_lit 75647828) (nat_lit 12912737647) (nat_lit 0) A10K2.t4845 from rfl, allE_node, rows4844, irow4837, rows4845]
  all_goals rfl

theorem atot4837 : totK PA10K2 A10K2.u4837 = [441334865603, 2617864748656, 4258718123977, 1921686611045, 167633749522, 0, 0, 0, 0, 0] := by
  rw [show A10K2.u4837 = KTree.node A10K2.t4844 (nat_lit 75647828) (nat_lit 12912737647) (nat_lit 0) A10K2.t4845 from rfl, totK_node, tot4844, tot4845]
  decide +kernel

theorem arows4838 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4838 = true := by
  rw [show A10K2.u4838 = KTree.node A10K2.t4846 (nat_lit 75663637) (nat_lit 7022094326) (nat_lit 0) A10K2.t4847 from rfl, allE_node, rows4846, irow4838, rows4847]
  all_goals rfl

theorem atot4838 : totK PA10K2 A10K2.u4838 = [0, 1053606793119, 3773871374672, 3843114125943, 976772711029, 45137667897, 0, 0, 0, 0] := by
  rw [show A10K2.u4838 = KTree.node A10K2.t4846 (nat_lit 75663637) (nat_lit 7022094326) (nat_lit 0) A10K2.t4847 from rfl, totK_node, tot4846, tot4847]
  decide +kernel

theorem arows4842 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4842 = true := by
  rw [show A10K2.u4842 = KTree.node A10K2.t4848 (nat_lit 75678060) (nat_lit 12699658009) (nat_lit 0) A10K2.t4849 from rfl, allE_node, rows4848, irow4842, rows4849]
  all_goals rfl

theorem atot4842 : totK PA10K2 A10K2.u4842 = [0, 967556099971, 3482348078015, 3777128174009, 1109592189361, 82738314188, 0, 0, 0, 0] := by
  rw [show A10K2.u4842 = KTree.node A10K2.t4848 (nat_lit 75678060) (nat_lit 12699658009) (nat_lit 0) A10K2.t4849 from rfl, totK_node, tot4848, tot4849]
  decide +kernel

theorem arows4843 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4843 = true := by
  rw [show A10K2.u4843 = KTree.node A10K2.t4850 (nat_lit 75683913) (nat_lit 8287161922) (nat_lit 0) A10K2.t4851 from rfl, allE_node, rows4850, irow4843, rows4851]
  all_goals rfl

theorem atot4843 : totK PA10K2 A10K2.u4843 = [306130628101, 1141094245006, 2509816700001, 3418289249387, 1695398030042, 265773289542, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u4843 = KTree.node A10K2.t4850 (nat_lit 75683913) (nat_lit 8287161922) (nat_lit 0) A10K2.t4851 from rfl, totK_node, tot4850, tot4851]
  decide +kernel

theorem arows4845 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4845 = true := by
  rw [show A10K2.u4845 = KTree.node A10K2.t4852 (nat_lit 75698135) (nat_lit 14217301965) (nat_lit 0) A10K2.t4853 from rfl, allE_node, rows4852, irow4845, rows4853]
  all_goals rfl

theorem atot4845 : totK PA10K2 A10K2.u4845 = [464557879428, 2313018212834, 3930076965683, 2549722965540, 521377065189, 25351274858, 0, 0, 0, 0] := by
  rw [show A10K2.u4845 = KTree.node A10K2.t4852 (nat_lit 75698135) (nat_lit 14217301965) (nat_lit 0) A10K2.t4853 from rfl, totK_node, tot4852, tot4853]
  decide +kernel

theorem arows4846 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4846 = true := by
  rw [show A10K2.u4846 = KTree.node A10K2.t4854 (nat_lit 75721907) (nat_lit 10068087110) (nat_lit 0) A10K2.t4855 from rfl, allE_node, rows4854, irow4846, rows4855]
  all_goals rfl

theorem atot4846 : totK PA10K2 A10K2.u4846 = [593693355846, 2727562595818, 4169615971126, 2269150999780, 351979265556, 12312941161, 0, 0, 0, 0] := by
  rw [show A10K2.u4846 = KTree.node A10K2.t4854 (nat_lit 75721907) (nat_lit 10068087110) (nat_lit 0) A10K2.t4855 from rfl, totK_node, tot4854, tot4855]
  decide +kernel

theorem arows4849 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4849 = true := by
  rw [show A10K2.u4849 = KTree.node A10K2.t4856 (nat_lit 75727314) (nat_lit 6531007106) (nat_lit 0) A10K2.t4857 from rfl, allE_node, rows4856, irow4849, rows4857]
  all_goals rfl

theorem atot4849 : totK PA10K2 A10K2.u4849 = [0, 1077122521670, 3786233144498, 3886403432878, 1147605794908, 80261166969, 0, 0, 0, 0] := by
  rw [show A10K2.u4849 = KTree.node A10K2.t4856 (nat_lit 75727314) (nat_lit 6531007106) (nat_lit 0) A10K2.t4857 from rfl, totK_node, tot4856, tot4857]
  decide +kernel

theorem arows4850 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4850 = true := by
  rw [show A10K2.u4850 = KTree.node A10K2.t4858 (nat_lit 75733352) (nat_lit 9476821359) (nat_lit 0) A10K2.t4859 from rfl, allE_node, rows4858, irow4850, rows4859]
  all_goals rfl

theorem atot4850 : totK PA10K2 A10K2.u4850 = [0, 472777056719, 2432037554525, 4208544694833, 2393889490272, 334918204999, 6904928264, 0, 0, 0] := by
  rw [show A10K2.u4850 = KTree.node A10K2.t4858 (nat_lit 75733352) (nat_lit 9476821359) (nat_lit 0) A10K2.t4859 from rfl, totK_node, tot4858, tot4859]
  decide +kernel

theorem arows4852 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4852 = true := by
  rw [show A10K2.u4852 = KTree.node A10K2.t4860 (nat_lit 75756478) (nat_lit 16128367311) (nat_lit 0) A10K2.t4861 from rfl, allE_node, rows4860, irow4852, rows4861]
  all_goals rfl

theorem atot4852 : totK PA10K2 A10K2.u4852 = [0, 438759164984, 2158213198008, 3749681336093, 2856480086243, 764933149668, 54952977549, 0, 0, 0] := by
  rw [show A10K2.u4852 = KTree.node A10K2.t4860 (nat_lit 75756478) (nat_lit 16128367311) (nat_lit 0) A10K2.t4861 from rfl, totK_node, tot4860, tot4861]
  decide +kernel

theorem arows4853 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4853 = true := by
  rw [show A10K2.u4853 = KTree.node A10K2.t4862 (nat_lit 75763098) (nat_lit 6136818601) (nat_lit 0) A10K2.t4863 from rfl, allE_node, rows4862, irow4853, rows4863]
  all_goals rfl

theorem atot4853 : totK PA10K2 A10K2.u4853 = [0, 524578926850, 2544355814713, 3937033845586, 2072252899985, 388881324205, 25371180993, 0, 0, 0] := by
  rw [show A10K2.u4853 = KTree.node A10K2.t4862 (nat_lit 75763098) (nat_lit 6136818601) (nat_lit 0) A10K2.t4863 from rfl, totK_node, tot4862, tot4863]
  decide +kernel

theorem arows4861 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4861 = true := by
  rw [show A10K2.u4861 = KTree.node A10K2.t4864 (nat_lit 75776340) (nat_lit 12780705436) (nat_lit 0) A10K2.t4865 from rfl, allE_node, rows4864, irow4861, rows4865]
  all_goals rfl

theorem atot4861 : totK PA10K2 A10K2.u4861 = [0, 746637748062, 2852795304431, 3721976182010, 1825842816458, 257153785360, 5460492893, 0, 0, 0] := by
  rw [show A10K2.u4861 = KTree.node A10K2.t4864 (nat_lit 75776340) (nat_lit 12780705436) (nat_lit 0) A10K2.t4865 from rfl, totK_node, tot4864, tot4865]
  decide +kernel

theorem arows4862 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4862 = true := by
  rw [show A10K2.u4862 = KTree.node A10K2.t4866 (nat_lit 75782428) (nat_lit 12202579886) (nat_lit 0) A10K2.t4867 from rfl, allE_node, rows4866, irow4862, rows4867]
  all_goals rfl

theorem atot4862 : totK PA10K2 A10K2.u4862 = [0, 405869091711, 2496761848210, 4306718524476, 2061610791285, 231729266272, 5705019915, 0, 0, 0] := by
  rw [show A10K2.u4862 = KTree.node A10K2.t4866 (nat_lit 75782428) (nat_lit 12202579886) (nat_lit 0) A10K2.t4867 from rfl, totK_node, tot4866, tot4867]
  decide +kernel

theorem arows4864 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4864 = true := by
  rw [show A10K2.u4864 = KTree.node A10K2.t4868 (nat_lit 75789061) (nat_lit 6340564974) (nat_lit 0) A10K2.t4869 from rfl, allE_node, rows4868, irow4864, rows4869]
  all_goals rfl

theorem atot4864 : totK PA10K2 A10K2.u4864 = [0, 218975725320, 1837980641773, 4044573232353, 3098082760129, 706204977590, 35031173917, 0, 0, 0] := by
  rw [show A10K2.u4864 = KTree.node A10K2.t4868 (nat_lit 75789061) (nat_lit 6340564974) (nat_lit 0) A10K2.t4869 from rfl, totK_node, tot4868, tot4869]
  decide +kernel

theorem arows4865 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4865 = true := by
  rw [show A10K2.u4865 = KTree.node A10K2.t4870 (nat_lit 75795844) (nat_lit 8054580468) (nat_lit 0) A10K2.t4871 from rfl, allE_node, rows4870, irow4865, rows4871]
  all_goals rfl

theorem atot4865 : totK PA10K2 A10K2.u4865 = [0, 0, 522241106775, 2623348412404, 3893962746746, 1929148011128, 389574588130, 25239774317, 0, 0] := by
  rw [show A10K2.u4865 = KTree.node A10K2.t4870 (nat_lit 75795844) (nat_lit 8054580468) (nat_lit 0) A10K2.t4871 from rfl, totK_node, tot4870, tot4871]
  decide +kernel

theorem arows4868 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4868 = true := by
  rw [show A10K2.u4868 = KTree.node A10K2.t4872 (nat_lit 75809214) (nat_lit 14267822336) (nat_lit 0) A10K2.t4873 from rfl, allE_node, rows4872, irow4868, rows4873]
  all_goals rfl

theorem atot4868 : totK PA10K2 A10K2.u4868 = [0, 0, 740570195616, 2963378894523, 3687099320546, 1588032045387, 217039146458, 5365973533, 0, 0] := by
  rw [show A10K2.u4868 = KTree.node A10K2.t4872 (nat_lit 75809214) (nat_lit 14267822336) (nat_lit 0) A10K2.t4873 from rfl, totK_node, tot4872, tot4873]
  decide +kernel

theorem arows4869 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4869 = true := by
  rw [show A10K2.u4869 = KTree.node A10K2.t4874 (nat_lit 75815592) (nat_lit 8254785999) (nat_lit 0) A10K2.t4875 from rfl, allE_node, rows4874, irow4869, rows4875]
  all_goals rfl

theorem atot4869 : totK PA10K2 A10K2.u4869 = [0, 0, 622765862201, 2811172517936, 4038136489235, 1687351538909, 211677635039, 5528811039, 0, 0] := by
  rw [show A10K2.u4869 = KTree.node A10K2.t4874 (nat_lit 75815592) (nat_lit 8254785999) (nat_lit 0) A10K2.t4875 from rfl, totK_node, tot4874, tot4875]
  decide +kernel

theorem arows4871 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4871 = true := by
  rw [show A10K2.u4871 = KTree.node A10K2.t4876 (nat_lit 75892884) (nat_lit 12788947827) (nat_lit 0) A10K2.t4877 from rfl, allE_node, rows4876, irow4871, rows4877]
  all_goals rfl

theorem atot4871 : totK PA10K2 A10K2.u4871 = [0, 778599946908, 3010544784038, 3738993908006, 1826869599104, 414724567863, 29010686974, 0, 0, 0] := by
  rw [show A10K2.u4871 = KTree.node A10K2.t4876 (nat_lit 75892884) (nat_lit 12788947827) (nat_lit 0) A10K2.t4877 from rfl, totK_node, tot4876, tot4877]
  decide +kernel

theorem arows4872 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4872 = true := by
  rw [show A10K2.u4872 = KTree.node A10K2.t4878 (nat_lit 75897915) (nat_lit 3510908873) (nat_lit 0) A10K2.t4879 from rfl, allE_node, rows4878, irow4872, rows4879]
  all_goals rfl

theorem atot4872 : totK PA10K2 A10K2.u4872 = [0, 558195267532, 2259330721095, 3656308823484, 2504744300285, 540791484588, 30831673886, 0, 0, 0] := by
  rw [show A10K2.u4872 = KTree.node A10K2.t4878 (nat_lit 75897915) (nat_lit 3510908873) (nat_lit 0) A10K2.t4879 from rfl, totK_node, tot4878, tot4879]
  decide +kernel

theorem arows4876 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4876 = true := by
  rw [show A10K2.u4876 = KTree.node A10K2.t4880 (nat_lit 75905824) (nat_lit 11562272761) (nat_lit 0) A10K2.t4881 from rfl, allE_node, rows4880, irow4876, rows4881]
  all_goals rfl

theorem atot4876 : totK PA10K2 A10K2.u4876 = [0, 515753070049, 2666189112141, 4058879551943, 1922105758163, 248312905013, 6034215561, 0, 0, 0] := by
  rw [show A10K2.u4876 = KTree.node A10K2.t4880 (nat_lit 75905824) (nat_lit 11562272761) (nat_lit 0) A10K2.t4881 from rfl, totK_node, tot4880, tot4881]
  decide +kernel

theorem arows4877 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4877 = true := by
  rw [show A10K2.u4877 = KTree.node A10K2.t4882 (nat_lit 75911622) (nat_lit 13338532578) (nat_lit 0) A10K2.t4883 from rfl, allE_node, rows4882, irow4877, rows4883]
  all_goals rfl

theorem atot4877 : totK PA10K2 A10K2.u4877 = [0, 303792748393, 2227104968452, 4236773650677, 2278414280029, 306570332572, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u4877 = KTree.node A10K2.t4882 (nat_lit 75911622) (nat_lit 13338532578) (nat_lit 0) A10K2.t4883 from rfl, totK_node, tot4882, tot4883]
  decide +kernel

theorem arows4879 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4879 = true := by
  rw [show A10K2.u4879 = KTree.node A10K2.t4884 (nat_lit 75926564) (nat_lit 12353951995) (nat_lit 0) A10K2.t4885 from rfl, allE_node, rows4884, irow4879, rows4885]
  all_goals rfl

theorem atot4879 : totK PA10K2 A10K2.u4879 = [0, 0, 1151790355827, 3947279560847, 3618211710520, 795749533828, 38551375656, 0, 0, 0] := by
  rw [show A10K2.u4879 = KTree.node A10K2.t4884 (nat_lit 75926564) (nat_lit 12353951995) (nat_lit 0) A10K2.t4885 from rfl, totK_node, tot4884, tot4885]
  decide +kernel

theorem arows4880 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4880 = true := by
  rw [show A10K2.u4880 = KTree.node A10K2.t4886 (nat_lit 75941541) (nat_lit 7026826106) (nat_lit 0) A10K2.t4887 from rfl, allE_node, rows4886, irow4880, rows4887]
  all_goals rfl

theorem atot4880 : totK PA10K2 A10K2.u4880 = [0, 0, 811672183507, 3430770985307, 3897224922188, 1093881926696, 69005204554, 0, 0, 0] := by
  rw [show A10K2.u4880 = KTree.node A10K2.t4886 (nat_lit 75941541) (nat_lit 7026826106) (nat_lit 0) A10K2.t4887 from rfl, totK_node, tot4886, tot4887]
  decide +kernel

theorem arows4883 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4883 = true := by
  rw [show A10K2.u4883 = KTree.node A10K2.t4888 (nat_lit 75956748) (nat_lit 10947536199) (nat_lit 0) A10K2.t4889 from rfl, allE_node, rows4888, irow4883, rows4889]
  all_goals rfl

theorem atot4883 : totK PA10K2 A10K2.u4883 = [0, 767515445342, 2647803949968, 3029348635560, 1982554575291, 943999745845, 160162151064, 5676195732, 0, 0] := by
  rw [show A10K2.u4883 = KTree.node A10K2.t4888 (nat_lit 75956748) (nat_lit 10947536199) (nat_lit 0) A10K2.t4889 from rfl, totK_node, tot4888, tot4889]
  decide +kernel

theorem arows4884 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4884 = true := by
  rw [show A10K2.u4884 = KTree.node A10K2.t4890 (nat_lit 75962725) (nat_lit 7229140086) (nat_lit 0) A10K2.t4891 from rfl, allE_node, rows4890, irow4884, rows4891]
  all_goals rfl

theorem atot4884 : totK PA10K2 A10K2.u4884 = [0, 455581209591, 2326242068831, 4101722139439, 2466558131094, 462918782417, 25313348169, 0, 0, 0] := by
  rw [show A10K2.u4884 = KTree.node A10K2.t4890 (nat_lit 75962725) (nat_lit 7229140086) (nat_lit 0) A10K2.t4891 from rfl, totK_node, tot4890, tot4891]
  decide +kernel

theorem arows4886 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4886 = true := by
  rw [show A10K2.u4886 = KTree.node A10K2.t4892 (nat_lit 75985814) (nat_lit 15693259330) (nat_lit 0) A10K2.t4893 from rfl, allE_node, rows4892, irow4886, rows4893]
  all_goals rfl

theorem atot4886 : totK PA10K2 A10K2.u4886 = [320561472736, 909459650683, 1764776171085, 3368384508137, 2910392515719, 817268972640, 55990884373, 0, 0, 0] := by
  rw [show A10K2.u4886 = KTree.node A10K2.t4892 (nat_lit 75985814) (nat_lit 15693259330) (nat_lit 0) A10K2.t4893 from rfl, totK_node, tot4892, tot4893]
  decide +kernel

theorem arows4887 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4887 = true := by
  rw [show A10K2.u4887 = KTree.node A10K2.t4894 (nat_lit 76098802) (nat_lit 14990917596) (nat_lit 0) A10K2.t4895 from rfl, allE_node, rows4894, irow4887, rows4895]
  all_goals rfl

theorem atot4887 : totK PA10K2 A10K2.u4887 = [527762187806, 2637921524175, 4015950151989, 2068660037942, 362783778840, 20340910120, 0, 0, 0, 0] := by
  rw [show A10K2.u4887 = KTree.node A10K2.t4894 (nat_lit 76098802) (nat_lit 14990917596) (nat_lit 0) A10K2.t4895 from rfl, totK_node, tot4894, tot4895]
  decide +kernel

theorem arows4892 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4892 = true := by
  rw [show A10K2.u4892 = KTree.node A10K2.t4896 (nat_lit 76103971) (nat_lit 9298980690) (nat_lit 0) A10K2.t4897 from rfl, allE_node, rows4896, irow4892, rows4897]
  all_goals rfl

theorem atot4892 : totK PA10K2 A10K2.u4892 = [640026692955, 2568001321781, 3783927872911, 2167638465236, 342818444895, 11427838733, 0, 0, 0, 0] := by
  rw [show A10K2.u4892 = KTree.node A10K2.t4896 (nat_lit 76103971) (nat_lit 9298980690) (nat_lit 0) A10K2.t4897 from rfl, totK_node, tot4896, tot4897]
  decide +kernel

theorem arows4893 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4893 = true := by
  rw [show A10K2.u4893 = KTree.node A10K2.t4898 (nat_lit 76109970) (nat_lit 15203200646) (nat_lit 0) A10K2.t4899 from rfl, allE_node, rows4898, irow4893, rows4899]
  all_goals rfl

theorem atot4893 : totK PA10K2 A10K2.u4893 = [476125298792, 2598503447487, 4144884963029, 2105660369022, 290495991534, 6354482628, 0, 0, 0, 0] := by
  rw [show A10K2.u4893 = KTree.node A10K2.t4898 (nat_lit 76109970) (nat_lit 15203200646) (nat_lit 0) A10K2.t4899 from rfl, totK_node, tot4898, tot4899]
  decide +kernel

theorem arows4895 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4895 = true := by
  rw [show A10K2.u4895 = KTree.node A10K2.t4900 (nat_lit 76117282) (nat_lit 13664070545) (nat_lit 0) A10K2.t4901 from rfl, allE_node, rows4900, irow4895, rows4901]
  all_goals rfl

theorem atot4895 : totK PA10K2 A10K2.u4895 = [260403760671, 1884535607788, 4020474897471, 3096339945876, 793677711069, 49660736315, 0, 0, 0, 0] := by
  rw [show A10K2.u4895 = KTree.node A10K2.t4900 (nat_lit 76117282) (nat_lit 13664070545) (nat_lit 0) A10K2.t4901 from rfl, totK_node, tot4900, tot4901]
  decide +kernel

theorem arows4896 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4896 = true := by
  rw [show A10K2.u4896 = KTree.node A10K2.t4902 (nat_lit 76131092) (nat_lit 13227563897) (nat_lit 0) A10K2.t4903 from rfl, allE_node, rows4902, irow4896, rows4903]
  all_goals rfl

theorem atot4896 : totK PA10K2 A10K2.u4896 = [0, 727137270146, 3235534875367, 4104557868409, 1441879943330, 101146013670, 0, 0, 0, 0] := by
  rw [show A10K2.u4896 = KTree.node A10K2.t4902 (nat_lit 76131092) (nat_lit 13227563897) (nat_lit 0) A10K2.t4903 from rfl, totK_node, tot4902, tot4903]
  decide +kernel

theorem arows4899 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4899 = true := by
  rw [show A10K2.u4899 = KTree.node A10K2.t4904 (nat_lit 76135898) (nat_lit 14396099117) (nat_lit 0) A10K2.t4905 from rfl, allE_node, rows4904, irow4899, rows4905]
  all_goals rfl

theorem atot4899 : totK PA10K2 A10K2.u4899 = [0, 528786827964, 2273337745771, 3667781611270, 2374860441862, 535182075992, 31082886609, 0, 0, 0] := by
  rw [show A10K2.u4899 = KTree.node A10K2.t4904 (nat_lit 76135898) (nat_lit 14396099117) (nat_lit 0) A10K2.t4905 from rfl, totK_node, tot4904, tot4905]
  decide +kernel

theorem arows4900 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4900 = true := by
  rw [show A10K2.u4900 = KTree.node A10K2.t4906 (nat_lit 76142070) (nat_lit 15564566643) (nat_lit 0) A10K2.t4907 from rfl, allE_node, rows4906, irow4900, rows4907]
  all_goals rfl

theorem atot4900 : totK PA10K2 A10K2.u4900 = [0, 584821006333, 2785813013490, 4034177705482, 1830513722576, 219342352943, 6121173289, 0, 0, 0] := by
  rw [show A10K2.u4900 = KTree.node A10K2.t4906 (nat_lit 76142070) (nat_lit 15564566643) (nat_lit 0) A10K2.t4907 from rfl, totK_node, tot4906, tot4907]
  decide +kernel

theorem arows4902 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4902 = true := by
  rw [show A10K2.u4902 = KTree.node A10K2.t4908 (nat_lit 76153132) (nat_lit 13183119572) (nat_lit 0) A10K2.t4909 from rfl, allE_node, rows4908, irow4902, rows4909]
  all_goals rfl

theorem atot4902 : totK PA10K2 A10K2.u4902 = [556587369176, 2391201288880, 3522903140561, 2394663986394, 802973991974, 69778634372, 0, 0, 0, 0] := by
  rw [show A10K2.u4902 = KTree.node A10K2.t4908 (nat_lit 76153132) (nat_lit 13183119572) (nat_lit 0) A10K2.t4909 from rfl, totK_node, tot4908, tot4909]
  decide +kernel

theorem arows4903 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4903 = true := by
  rw [show A10K2.u4903 = KTree.node A10K2.t4910 (nat_lit 76162204) (nat_lit 11653260701) (nat_lit 0) A10K2.t4911 from rfl, allE_node, rows4910, irow4903, rows4911]
  all_goals rfl

theorem atot4903 : totK PA10K2 A10K2.u4903 = [584594178835, 2445934978352, 3648087030631, 2299809482284, 511049618881, 30831673886, 0, 0, 0, 0] := by
  rw [show A10K2.u4903 = KTree.node A10K2.t4910 (nat_lit 76162204) (nat_lit 11653260701) (nat_lit 0) A10K2.t4911 from rfl, totK_node, tot4910, tot4911]
  decide +kernel

theorem arows4907 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4907 = true := by
  rw [show A10K2.u4907 = KTree.node A10K2.t4912 (nat_lit 76166885) (nat_lit 6559079392) (nat_lit 0) A10K2.t4913 from rfl, allE_node, rows4912, irow4907, rows4913]
  all_goals rfl

theorem atot4907 : totK PA10K2 A10K2.u4907 = [297686525469, 1858109860341, 3948443803617, 2970431499461, 616265480328, 31768748853, 0, 0, 0, 0] := by
  rw [show A10K2.u4907 = KTree.node A10K2.t4912 (nat_lit 76166885) (nat_lit 6559079392) (nat_lit 0) A10K2.t4913 from rfl, totK_node, tot4912, tot4913]
  decide +kernel

theorem arows4908 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4908 = true := by
  rw [show A10K2.u4908 = KTree.node A10K2.t4914 (nat_lit 76171268) (nat_lit 12748852462) (nat_lit 0) A10K2.t4915 from rfl, allE_node, rows4914, irow4908, rows4915]
  all_goals rfl

theorem atot4908 : totK PA10K2 A10K2.u4908 = [719867136813, 3171723045928, 4019015917766, 1463502290935, 113187570241, 0, 0, 0, 0, 0] := by
  rw [show A10K2.u4908 = KTree.node A10K2.t4914 (nat_lit 76171268) (nat_lit 12748852462) (nat_lit 0) A10K2.t4915 from rfl, totK_node, tot4914, tot4915]
  decide +kernel

theorem arows4910 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4910 = true := by
  rw [show A10K2.u4910 = KTree.node A10K2.t4916 (nat_lit 76186110) (nat_lit 11437505448) (nat_lit 0) A10K2.t4917 from rfl, allE_node, rows4916, irow4910, rows4917]
  all_goals rfl

theorem atot4910 : totK PA10K2 A10K2.u4910 = [0, 1175296401480, 3977262405898, 3502433473022, 802987266459, 38342359577, 0, 0, 0, 0] := by
  rw [show A10K2.u4910 = KTree.node A10K2.t4916 (nat_lit 76186110) (nat_lit 11437505448) (nat_lit 0) A10K2.t4917 from rfl, totK_node, tot4916, tot4917]
  decide +kernel

theorem arows4911 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4911 = true := by
  rw [show A10K2.u4911 = KTree.node A10K2.t4918 (nat_lit 76197055) (nat_lit 14008065033) (nat_lit 0) A10K2.t4919 from rfl, allE_node, rows4918, irow4911, rows4919]
  all_goals rfl

theorem atot4911 : totK PA10K2 A10K2.u4911 = [0, 987920184362, 3582586349485, 3877409700564, 1073548775542, 64078106957, 0, 0, 0, 0] := by
  rw [show A10K2.u4911 = KTree.node A10K2.t4918 (nat_lit 76197055) (nat_lit 14008065033) (nat_lit 0) A10K2.t4919 from rfl, totK_node, tot4918, tot4919]
  decide +kernel

theorem arows4914 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4914 = true := by
  rw [show A10K2.u4914 = KTree.node A10K2.t4920 (nat_lit 76206125) (nat_lit 6466289309) (nat_lit 0) A10K2.t4921 from rfl, allE_node, rows4920, irow4914, rows4921]
  all_goals rfl

theorem atot4914 : totK PA10K2 A10K2.u4914 = [0, 382674072533, 2507408196576, 4193890848926, 1978127575130, 253660988062, 0, 0, 0, 0] := by
  rw [show A10K2.u4914 = KTree.node A10K2.t4920 (nat_lit 76206125) (nat_lit 6466289309) (nat_lit 0) A10K2.t4921 from rfl, totK_node, tot4920, tot4921]
  decide +kernel

theorem arows4915 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4915 = true := by
  rw [show A10K2.u4915 = KTree.node A10K2.t4922 (nat_lit 76229480) (nat_lit 8517328027) (nat_lit 0) A10K2.t4923 from rfl, allE_node, rows4922, irow4915, rows4923]
  all_goals rfl

theorem atot4915 : totK PA10K2 A10K2.u4915 = [773889436601, 3145571801016, 4054106643574, 1760459694061, 197493044292, 30401557407, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u4915 = KTree.node A10K2.t4922 (nat_lit 76229480) (nat_lit 8517328027) (nat_lit 0) A10K2.t4923 from rfl, totK_node, tot4922, tot4923]
  decide +kernel

theorem arows4917 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4917 = true := by
  rw [show A10K2.u4917 = KTree.node A10K2.t4924 (nat_lit 76244258) (nat_lit 13630913656) (nat_lit 0) A10K2.t4925 from rfl, allE_node, rows4924, irow4917, rows4925]
  all_goals rfl

theorem atot4917 : totK PA10K2 A10K2.u4917 = [595724520244, 2658298961024, 3972572183858, 2335184403696, 469584842145, 31747192500, 0, 0, 0, 0] := by
  rw [show A10K2.u4917 = KTree.node A10K2.t4924 (nat_lit 76244258) (nat_lit 13630913656) (nat_lit 0) A10K2.t4925 from rfl, totK_node, tot4924, tot4925]
  decide +kernel

theorem arows4918 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4918 = true := by
  rw [show A10K2.u4918 = KTree.node A10K2.t4926 (nat_lit 76250702) (nat_lit 10774798059) (nat_lit 0) A10K2.t4927 from rfl, allE_node, rows4926, irow4918, rows4927]
  all_goals rfl

theorem atot4918 : totK PA10K2 A10K2.u4918 = [0, 1030532739453, 3782474414412, 3972785833581, 1210805913639, 82048797876, 0, 0, 0, 0] := by
  rw [show A10K2.u4918 = KTree.node A10K2.t4926 (nat_lit 76250702) (nat_lit 10774798059) (nat_lit 0) A10K2.t4927 from rfl, totK_node, tot4926, tot4927]
  decide +kernel

theorem arows4924 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4924 = true := by
  rw [show A10K2.u4924 = KTree.node A10K2.t4928 (nat_lit 76264787) (nat_lit 10539063937) (nat_lit 0) A10K2.t4929 from rfl, allE_node, rows4928, irow4924, rows4929]
  all_goals rfl

theorem atot4924 : totK PA10K2 A10K2.u4924 = [0, 524876967399, 2619289628852, 4139579880243, 2279180276483, 327024886482, 7047025452, 0, 0, 0] := by
  rw [show A10K2.u4924 = KTree.node A10K2.t4928 (nat_lit 76264787) (nat_lit 10539063937) (nat_lit 0) A10K2.t4929 from rfl, totK_node, tot4928, tot4929]
  decide +kernel

theorem arows4925 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4925 = true := by
  rw [show A10K2.u4925 = KTree.node A10K2.t4930 (nat_lit 76279772) (nat_lit 2317170715) (nat_lit 0) A10K2.t4931 from rfl, allE_node, rows4930, irow4925, rows4931]
  all_goals rfl

theorem atot4925 : totK PA10K2 A10K2.u4925 = [0, 407759875301, 2301402885869, 4216242762237, 2719125755352, 486733604014, 11910457242, 0, 0, 0] := by
  rw [show A10K2.u4925 = KTree.node A10K2.t4930 (nat_lit 76279772) (nat_lit 2317170715) (nat_lit 0) A10K2.t4931 from rfl, totK_node, tot4930, tot4931]
  decide +kernel

theorem arows4927 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4927 = true := by
  rw [show A10K2.u4927 = KTree.node A10K2.t4932 (nat_lit 76359937) (nat_lit 8172691691) (nat_lit 0) A10K2.t4933 from rfl, allE_node, rows4932, irow4927, rows4933]
  all_goals rfl

theorem atot4927 : totK PA10K2 A10K2.u4927 = [0, 845829470152, 3212184500919, 3708749440785, 1500819693712, 376437078336, 43132710386, 0, 0, 0] := by
  rw [show A10K2.u4927 = KTree.node A10K2.t4932 (nat_lit 76359937) (nat_lit 8172691691) (nat_lit 0) A10K2.t4933 from rfl, totK_node, tot4932, tot4933]
  decide +kernel

theorem arows4928 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4928 = true := by
  rw [show A10K2.u4928 = KTree.node A10K2.t4934 (nat_lit 76364626) (nat_lit 13710285956) (nat_lit 0) A10K2.t4935 from rfl, allE_node, rows4934, irow4928, rows4935]
  all_goals rfl

theorem atot4928 : totK PA10K2 A10K2.u4928 = [0, 461866678616, 2152591302791, 3666866427889, 2599707643183, 573744887892, 31768748853, 0, 0, 0] := by
  rw [show A10K2.u4928 = KTree.node A10K2.t4934 (nat_lit 76364626) (nat_lit 13710285956) (nat_lit 0) A10K2.t4935 from rfl, totK_node, tot4934, tot4935]
  decide +kernel

theorem arows4931 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4931 = true := by
  rw [show A10K2.u4931 = KTree.node A10K2.t4936 (nat_lit 76371098) (nat_lit 15154852766) (nat_lit 0) A10K2.t4937 from rfl, allE_node, rows4936, irow4931, rows4937]
  all_goals rfl

theorem atot4931 : totK PA10K2 A10K2.u4931 = [0, 472686988510, 2433392041765, 4156288228415, 2110509281457, 247202306788, 6239673734, 0, 0, 0] := by
  rw [show A10K2.u4931 = KTree.node A10K2.t4936 (nat_lit 76371098) (nat_lit 15154852766) (nat_lit 0) A10K2.t4937 from rfl, totK_node, tot4936, tot4937]
  decide +kernel

theorem arows4932 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4932 = true := by
  rw [show A10K2.u4932 = KTree.node A10K2.t4938 (nat_lit 76378004) (nat_lit 7633801621) (nat_lit 0) A10K2.t4939 from rfl, allE_node, rows4938, irow4932, rows4939]
  all_goals rfl

theorem atot4932 : totK PA10K2 A10K2.u4932 = [0, 440236534549, 2514573679558, 4260095678068, 2455587973434, 384142588473, 6962742351, 0, 0, 0] := by
  rw [show A10K2.u4932 = KTree.node A10K2.t4938 (nat_lit 76378004) (nat_lit 7633801621) (nat_lit 0) A10K2.t4939 from rfl, totK_node, tot4938, tot4939]
  decide +kernel

theorem arows4934 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4934 = true := by
  rw [show A10K2.u4934 = KTree.node A10K2.t4940 (nat_lit 76392492) (nat_lit 12681689623) (nat_lit 0) A10K2.t4941 from rfl, allE_node, rows4940, irow4934, rows4941]
  all_goals rfl

theorem atot4934 : totK PA10K2 A10K2.u4934 = [0, 0, 839608009595, 3382068708956, 3989844576314, 1294657513317, 79406773478, 0, 0, 0] := by
  rw [show A10K2.u4934 = KTree.node A10K2.t4940 (nat_lit 76392492) (nat_lit 12681689623) (nat_lit 0) A10K2.t4941 from rfl, totK_node, tot4940, tot4941]
  decide +kernel

theorem arows4935 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4935 = true := by
  rw [show A10K2.u4935 = KTree.node A10K2.t4942 (nat_lit 76397312) (nat_lit 8675140210) (nat_lit 0) A10K2.t4943 from rfl, allE_node, rows4942, irow4935, rows4943]
  all_goals rfl

theorem atot4935 : totK PA10K2 A10K2.u4935 = [0, 0, 457723444173, 2206677733759, 3675066015578, 2400781643180, 547707472651, 31018567651, 0, 0] := by
  rw [show A10K2.u4935 = KTree.node A10K2.t4942 (nat_lit 76397312) (nat_lit 8675140210) (nat_lit 0) A10K2.t4943 from rfl, totK_node, tot4942, tot4943]
  decide +kernel

theorem arows4939 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4939 = true := by
  rw [show A10K2.u4939 = KTree.node A10K2.t4944 (nat_lit 76403885) (nat_lit 6276761685) (nat_lit 0) A10K2.t4945 from rfl, allE_node, rows4944, irow4939, rows4945]
  all_goals rfl

theorem atot4939 : totK PA10K2 A10K2.u4939 = [0, 0, 516871774822, 2585645024999, 4079329993282, 1867941893578, 226343046628, 5685526223, 0, 0] := by
  rw [show A10K2.u4939 = KTree.node A10K2.t4944 (nat_lit 76403885) (nat_lit 6276761685) (nat_lit 0) A10K2.t4945 from rfl, totK_node, tot4944, tot4945]
  decide +kernel

theorem arows4940 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4940 = true := by
  rw [show A10K2.u4940 = KTree.node A10K2.t4946 (nat_lit 76415031) (nat_lit 12648865630) (nat_lit 0) A10K2.t4947 from rfl, allE_node, rows4946, irow4940, rows4947]
  all_goals rfl

theorem atot4940 : totK PA10K2 A10K2.u4940 = [0, 556222090703, 2413680805493, 3632758828556, 2458286512442, 685653962214, 51666332465, 0, 0, 0] := by
  rw [show A10K2.u4940 = KTree.node A10K2.t4946 (nat_lit 76415031) (nat_lit 12648865630) (nat_lit 0) A10K2.t4947 from rfl, totK_node, tot4946, tot4947]
  decide +kernel

theorem arows4942 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4942 = true := by
  rw [show A10K2.u4942 = KTree.node A10K2.t4948 (nat_lit 76424477) (nat_lit 6342138324) (nat_lit 0) A10K2.t4949 from rfl, allE_node, rows4948, irow4942, rows4949]
  all_goals rfl

theorem atot4942 : totK PA10K2 A10K2.u4942 = [0, 626278403089, 2730772265210, 4012807914067, 1909374101360, 225792720626, 5460492893, 0, 0, 0] := by
  rw [show A10K2.u4942 = KTree.node A10K2.t4948 (nat_lit 76424477) (nat_lit 6342138324) (nat_lit 0) A10K2.t4949 from rfl, totK_node, tot4948, tot4949]
  decide +kernel

theorem arows4943 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4943 = true := by
  rw [show A10K2.u4943 = KTree.node A10K2.t4950 (nat_lit 76429233) (nat_lit 2946750537) (nat_lit 0) A10K2.t4951 from rfl, allE_node, rows4950, irow4943, rows4951]
  all_goals rfl

theorem atot4943 : totK PA10K2 A10K2.u4943 = [0, 392294856917, 2015334300714, 3805339843367, 2817593681182, 602619601620, 31768748853, 0, 0, 0] := by
  rw [show A10K2.u4943 = KTree.node A10K2.t4950 (nat_lit 76429233) (nat_lit 2946750537) (nat_lit 0) A10K2.t4951 from rfl, totK_node, tot4950, tot4951]
  decide +kernel

theorem arows4946 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4946 = true := by
  rw [show A10K2.u4946 = KTree.node A10K2.t4952 (nat_lit 76433581) (nat_lit 6561767260) (nat_lit 0) A10K2.t4953 from rfl, allE_node, rows4952, irow4946, rows4953]
  all_goals rfl

theorem atot4946 : totK PA10K2 A10K2.u4946 = [0, 583209941258, 2959307613062, 4229014612857, 1608952186583, 118051014925, 0, 0, 0, 0] := by
  rw [show A10K2.u4946 = KTree.node A10K2.t4952 (nat_lit 76433581) (nat_lit 6561767260) (nat_lit 0) A10K2.t4953 from rfl, totK_node, tot4952, tot4953]
  decide +kernel

theorem arows4947 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4947 = true := by
  rw [show A10K2.u4947 = KTree.node A10K2.t4954 (nat_lit 76448621) (nat_lit 5385992497) (nat_lit 0) A10K2.t4955 from rfl, allE_node, rows4954, irow4947, rows4955]
  all_goals rfl

theorem atot4947 : totK PA10K2 A10K2.u4947 = [0, 0, 1121748308607, 3933359155132, 3550517019422, 745063051585, 33066034854, 0, 0, 0] := by
  rw [show A10K2.u4947 = KTree.node A10K2.t4954 (nat_lit 76448621) (nat_lit 5385992497) (nat_lit 0) A10K2.t4955 from rfl, totK_node, tot4954, tot4955]
  decide +kernel

theorem arows4949 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4949 = true := by
  rw [show A10K2.u4949 = KTree.node A10K2.t4956 (nat_lit 76459760) (nat_lit 5620545382) (nat_lit 0) A10K2.t4957 from rfl, allE_node, rows4956, irow4949, rows4957]
  all_goals rfl

theorem atot4949 : totK PA10K2 A10K2.u4949 = [0, 0, 987374192960, 3697805399205, 3871473905488, 901697780424, 49076455522, 0, 0, 0] := by
  rw [show A10K2.u4949 = KTree.node A10K2.t4956 (nat_lit 76459760) (nat_lit 5620545382) (nat_lit 0) A10K2.t4957 from rfl, totK_node, tot4956, tot4957]
  decide +kernel

theorem arows4950 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4950 = true := by
  rw [show A10K2.u4950 = KTree.node A10K2.t4958 (nat_lit 76469522) (nat_lit 14993366649) (nat_lit 0) A10K2.t4959 from rfl, allE_node, rows4958, irow4950, rows4959]
  all_goals rfl

theorem atot4950 : totK PA10K2 A10K2.u4950 = [0, 305746175225, 1143871318645, 2486975779165, 3475601051342, 1616839809892, 220553073859, 6239673734, 0, 0] := by
  rw [show A10K2.u4950 = KTree.node A10K2.t4958 (nat_lit 76469522) (nat_lit 14993366649) (nat_lit 0) A10K2.t4959 from rfl, totK_node, tot4958, tot4959]
  decide +kernel

theorem arows4955 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4955 = true := by
  rw [show A10K2.u4955 = KTree.node A10K2.t4960 (nat_lit 76492453) (nat_lit 6102999130) (nat_lit 0) A10K2.t4961 from rfl, allE_node, rows4960, irow4955, rows4961]
  all_goals rfl

theorem atot4955 : totK PA10K2 A10K2.u4955 = [0, 465040202289, 2471996360933, 4137660609665, 2310697141514, 442591816263, 25660650750, 0, 0, 0] := by
  rw [show A10K2.u4955 = KTree.node A10K2.t4960 (nat_lit 76492453) (nat_lit 6102999130) (nat_lit 0) A10K2.t4961 from rfl, totK_node, tot4960, tot4961]
  decide +kernel

theorem arows4956 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4956 = true := by
  rw [show A10K2.u4956 = KTree.node A10K2.t4962 (nat_lit 76507026) (nat_lit 15452378084) (nat_lit 0) A10K2.t4963 from rfl, allE_node, rows4962, irow4956, rows4963]
  all_goals rfl

theorem atot4956 : totK PA10K2 A10K2.u4956 = [0, 594801703647, 2738066129186, 4196387664163, 2269030890694, 303017381075, 5624717336, 0, 0, 0] := by
  rw [show A10K2.u4956 = KTree.node A10K2.t4962 (nat_lit 76507026) (nat_lit 15452378084) (nat_lit 0) A10K2.t4963 from rfl, totK_node, tot4962, tot4963]
  decide +kernel

theorem arows4958 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4958 = true := by
  rw [show A10K2.u4958 = KTree.node A10K2.t4964 (nat_lit 76546163) (nat_lit 4016531734) (nat_lit 0) A10K2.t4965 from rfl, allE_node, rows4964, irow4958, rows4965]
  all_goals rfl

theorem atot4958 : totK PA10K2 A10K2.u4958 = [581007796273, 2113097130879, 2439341503468, 1967409621659, 1958668323875, 732288083005, 56100664475, 0, 0, 0] := by
  rw [show A10K2.u4958 = KTree.node A10K2.t4964 (nat_lit 76546163) (nat_lit 4016531734) (nat_lit 0) A10K2.t4965 from rfl, totK_node, tot4964, tot4965]
  decide +kernel

theorem arows4959 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4959 = true := by
  rw [show A10K2.u4959 = KTree.node A10K2.t4966 (nat_lit 76550769) (nat_lit 7422301059) (nat_lit 0) A10K2.t4967 from rfl, allE_node, rows4966, irow4959, rows4967]
  all_goals rfl

theorem atot4959 : totK PA10K2 A10K2.u4959 = [331557213969, 1842959872572, 3786473558026, 2828504421129, 581511716866, 30831673886, 0, 0, 0, 0] := by
  rw [show A10K2.u4959 = KTree.node A10K2.t4966 (nat_lit 76550769) (nat_lit 7422301059) (nat_lit 0) A10K2.t4967 from rfl, totK_node, tot4966, tot4967]
  decide +kernel

theorem arows4962 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4962 = true := by
  rw [show A10K2.u4962 = KTree.node A10K2.t4968 (nat_lit 76564551) (nat_lit 9901433796) (nat_lit 0) A10K2.t4969 from rfl, allE_node, rows4968, irow4962, rows4969]
  all_goals rfl

theorem atot4962 : totK PA10K2 A10K2.u4962 = [674340088327, 3094825406897, 4177162181156, 1565764573213, 113202773402, 0, 0, 0, 0, 0] := by
  rw [show A10K2.u4962 = KTree.node A10K2.t4968 (nat_lit 76564551) (nat_lit 9901433796) (nat_lit 0) A10K2.t4969 from rfl, totK_node, tot4968, tot4969]
  decide +kernel

theorem arows4963 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4963 = true := by
  rw [show A10K2.u4963 = KTree.node A10K2.t4970 (nat_lit 76571404) (nat_lit 11637713880) (nat_lit 0) A10K2.t4971 from rfl, allE_node, rows4970, irow4963, rows4971]
  all_goals rfl

theorem atot4963 : totK PA10K2 A10K2.u4963 = [458520426296, 2249550091267, 3927501606498, 2532294389537, 473085362185, 13207830636, 0, 0, 0, 0] := by
  rw [show A10K2.u4963 = KTree.node A10K2.t4970 (nat_lit 76571404) (nat_lit 11637713880) (nat_lit 0) A10K2.t4971 from rfl, totK_node, tot4970, tot4971]
  decide +kernel

theorem arows4965 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4965 = true := by
  rw [show A10K2.u4965 = KTree.node A10K2.t4972 (nat_lit 76579683) (nat_lit 4446478681) (nat_lit 0) A10K2.t4973 from rfl, allE_node, rows4972, irow4965, rows4973]
  all_goals rfl

theorem atot4965 : totK PA10K2 A10K2.u4965 = [0, 979585301790, 3611323214387, 3816882834416, 1095593960289, 75282308959, 0, 0, 0, 0] := by
  rw [show A10K2.u4965 = KTree.node A10K2.t4972 (nat_lit 76579683) (nat_lit 4446478681) (nat_lit 0) A10K2.t4973 from rfl, totK_node, tot4972, tot4973]
  decide +kernel

theorem arows4966 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4966 = true := by
  rw [show A10K2.u4966 = KTree.node A10K2.t4974 (nat_lit 76585509) (nat_lit 7034150879) (nat_lit 0) A10K2.t4975 from rfl, allE_node, rows4974, irow4966, rows4975]
  all_goals rfl

theorem atot4966 : totK PA10K2 A10K2.u4966 = [0, 325086607341, 1865157547879, 3841816678266, 2694909314357, 568718202469, 30650496230, 0, 0, 0] := by
  rw [show A10K2.u4966 = KTree.node A10K2.t4974 (nat_lit 76585509) (nat_lit 7034150879) (nat_lit 0) A10K2.t4975 from rfl, totK_node, tot4974, tot4975]
  decide +kernel

theorem arows4970 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4970 = true := by
  rw [show A10K2.u4970 = KTree.node A10K2.t4976 (nat_lit 76599392) (nat_lit 13816408441) (nat_lit 0) A10K2.t4977 from rfl, allE_node, rows4976, irow4970, rows4977]
  all_goals rfl

theorem atot4970 : totK PA10K2 A10K2.u4970 = [0, 570897550607, 2801691183276, 4091194552343, 1757509242852, 204981600246, 5546304973, 0, 0, 0] := by
  rw [show A10K2.u4970 = KTree.node A10K2.t4976 (nat_lit 76599392) (nat_lit 13816408441) (nat_lit 0) A10K2.t4977 from rfl, totK_node, tot4976, tot4977]
  decide +kernel

theorem arows4971 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4971 = true := by
  rw [show A10K2.u4971 = KTree.node A10K2.t4978 (nat_lit 76621100) (nat_lit 13191186536) (nat_lit 0) A10K2.t4979 from rfl, allE_node, rows4978, irow4971, rows4979]
  all_goals rfl

theorem atot4971 : totK PA10K2 A10K2.u4971 = [622048478734, 2546748883694, 3630985795688, 2268401409841, 623774384322, 58509527586, 0, 0, 0, 0] := by
  rw [show A10K2.u4971 = KTree.node A10K2.t4978 (nat_lit 76621100) (nat_lit 13191186536) (nat_lit 0) A10K2.t4979 from rfl, totK_node, tot4978, tot4979]
  decide +kernel

theorem arows4973 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4973 = true := by
  rw [show A10K2.u4973 = KTree.node A10K2.t4980 (nat_lit 76625699) (nat_lit 10266066168) (nat_lit 0) A10K2.t4981 from rfl, allE_node, rows4980, irow4973, rows4981]
  all_goals rfl

theorem atot4973 : totK PA10K2 A10K2.u4973 = [308324070986, 1857311398423, 3819824118878, 2891737440585, 609266696130, 31768748853, 0, 0, 0, 0] := by
  rw [show A10K2.u4973 = KTree.node A10K2.t4980 (nat_lit 76625699) (nat_lit 10266066168) (nat_lit 0) A10K2.t4981 from rfl, totK_node, tot4980, tot4981]
  decide +kernel

theorem arows4974 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4974 = true := by
  rw [show A10K2.u4974 = KTree.node A10K2.t4982 (nat_lit 76630164) (nat_lit 12820410605) (nat_lit 0) A10K2.t4983 from rfl, allE_node, rows4982, irow4974, rows4983]
  all_goals rfl

theorem atot4974 : totK PA10K2 A10K2.u4974 = [649712545477, 3073275800612, 4182355400120, 1618825730672, 119570809196, 0, 0, 0, 0, 0] := by
  rw [show A10K2.u4974 = KTree.node A10K2.t4982 (nat_lit 76630164) (nat_lit 12820410605) (nat_lit 0) A10K2.t4983 from rfl, totK_node, tot4982, tot4983]
  decide +kernel

theorem arows4977 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4977 = true := by
  rw [show A10K2.u4977 = KTree.node A10K2.t4984 (nat_lit 76638036) (nat_lit 12148320722) (nat_lit 0) A10K2.t4985 from rfl, allE_node, rows4984, irow4977, rows4985]
  all_goals rfl

theorem atot4977 : totK PA10K2 A10K2.u4977 = [461607179050, 2220955582857, 3949800486758, 2612654991689, 487973597312, 13317224979, 0, 0, 0, 0] := by
  rw [show A10K2.u4977 = KTree.node A10K2.t4984 (nat_lit 76638036) (nat_lit 12148320722) (nat_lit 0) A10K2.t4985 from rfl, totK_node, tot4984, tot4985]
  decide +kernel

theorem arows4978 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4978 = true := by
  rw [show A10K2.u4978 = KTree.node A10K2.t4986 (nat_lit 76654485) (nat_lit 5171259390) (nat_lit 0) A10K2.t4987 from rfl, allE_node, rows4986, irow4978, rows4987]
  all_goals rfl

theorem atot4978 : totK PA10K2 A10K2.u4978 = [0, 984250608778, 3594559031693, 3844329975759, 1144008874441, 76604352247, 0, 0, 0, 0] := by
  rw [show A10K2.u4978 = KTree.node A10K2.t4986 (nat_lit 76654485) (nat_lit 5171259390) (nat_lit 0) A10K2.t4987 from rfl, totK_node, tot4986, tot4987]
  decide +kernel

theorem arows4980 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4980 = true := by
  rw [show A10K2.u4980 = KTree.node A10K2.t4988 (nat_lit 76659356) (nat_lit 11611774975) (nat_lit 0) A10K2.t4989 from rfl, allE_node, rows4988, irow4980, rows4989]
  all_goals rfl

theorem atot4980 : totK PA10K2 A10K2.u4980 = [0, 455239522804, 2103320832206, 3723713644680, 2586640347660, 569366200075, 31082886609, 0, 0, 0] := by
  rw [show A10K2.u4980 = KTree.node A10K2.t4988 (nat_lit 76659356) (nat_lit 11611774975) (nat_lit 0) A10K2.t4989 from rfl, totK_node, tot4988, tot4989]
  decide +kernel

theorem arows4981 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4981 = true := by
  rw [show A10K2.u4981 = KTree.node A10K2.t4990 (nat_lit 76664941) (nat_lit 5376512212) (nat_lit 0) A10K2.t4991 from rfl, allE_node, rows4990, irow4981, rows4991]
  all_goals rfl

theorem atot4981 : totK PA10K2 A10K2.u4981 = [0, 427150340102, 2443983746589, 4190635007193, 2061176911948, 245885793701, 6121173289, 0, 0, 0] := by
  rw [show A10K2.u4981 = KTree.node A10K2.t4990 (nat_lit 76664941) (nat_lit 5376512212) (nat_lit 0) A10K2.t4991 from rfl, totK_node, tot4990, tot4991]
  decide +kernel

theorem arows4988 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4988 = true := by
  rw [show A10K2.u4988 = KTree.node A10K2.t4992 (nat_lit 76677190) (nat_lit 14505970622) (nat_lit 0) A10K2.t4993 from rfl, allE_node, rows4992, irow4988, rows4993]
  all_goals rfl

theorem atot4988 : totK PA10K2 A10K2.u4988 = [578044150334, 2410152667972, 3556834246609, 2387374731696, 730540753575, 64208876967, 0, 0, 0, 0] := by
  rw [show A10K2.u4988 = KTree.node A10K2.t4992 (nat_lit 76677190) (nat_lit 14505970622) (nat_lit 0) A10K2.t4993 from rfl, totK_node, tot4992, tot4993]
  decide +kernel

theorem arows4989 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4989 = true := by
  rw [show A10K2.u4989 = KTree.node A10K2.t4994 (nat_lit 76682118) (nat_lit 14482522193) (nat_lit 0) A10K2.t4995 from rfl, allE_node, rows4994, irow4989, rows4995]
  all_goals rfl

theorem atot4989 : totK PA10K2 A10K2.u4989 = [459186044289, 2028004800313, 3737674217279, 2677402648575, 569730236052, 30831673886, 0, 0, 0, 0] := by
  rw [show A10K2.u4989 = KTree.node A10K2.t4994 (nat_lit 76682118) (nat_lit 14482522193) (nat_lit 0) A10K2.t4995 from rfl, totK_node, tot4994, tot4995]
  decide +kernel

theorem arows4991 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4991 = true := by
  rw [show A10K2.u4991 = KTree.node A10K2.t4996 (nat_lit 76688790) (nat_lit 13946581908) (nat_lit 0) A10K2.t4997 from rfl, allE_node, rows4996, irow4991, rows4997]
  all_goals rfl

theorem atot4991 : totK PA10K2 A10K2.u4991 = [451522813587, 2523257852177, 4047119443008, 2139019673632, 414469028046, 25734533292, 0, 0, 0, 0] := by
  rw [show A10K2.u4991 = KTree.node A10K2.t4996 (nat_lit 76688790) (nat_lit 13946581908) (nat_lit 0) A10K2.t4997 from rfl, totK_node, tot4996, tot4997]
  decide +kernel

theorem arows4992 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4992 = true := by
  rw [show A10K2.u4992 = KTree.node A10K2.t4998 (nat_lit 76694277) (nat_lit 6920038188) (nat_lit 0) A10K2.t4999 from rfl, allE_node, rows4998, irow4992, rows4999]
  all_goals rfl

theorem atot4992 : totK PA10K2 A10K2.u4992 = [855079708561, 2964073156615, 3623259234987, 1850190834768, 266892881627, 6034215561, 0, 0, 0, 0] := by
  rw [show A10K2.u4992 = KTree.node A10K2.t4998 (nat_lit 76694277) (nat_lit 6920038188) (nat_lit 0) A10K2.t4999 from rfl, totK_node, tot4998, tot4999]
  decide +kernel

theorem arows4995 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4995 = true := by
  rw [show A10K2.u4995 = KTree.node A10K2.t5000 (nat_lit 76699802) (nat_lit 14655832545) (nat_lit 0) A10K2.t5001 from rfl, allE_node, rows5000, irow4995, rows5001]
  all_goals rfl

theorem atot4995 : totK PA10K2 A10K2.u4995 = [0, 1547953158068, 4272530959069, 2999706854259, 601169861383, 31987755669, 0, 0, 0, 0] := by
  rw [show A10K2.u4995 = KTree.node A10K2.t5000 (nat_lit 76699802) (nat_lit 14655832545) (nat_lit 0) A10K2.t5001 from rfl, totK_node, tot5000, tot5001]
  decide +kernel

theorem arows4996 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4996 = true := by
  rw [show A10K2.u4996 = KTree.node A10K2.t5002 (nat_lit 76719331) (nat_lit 10483448895) (nat_lit 0) A10K2.t5003 from rfl, allE_node, rows5002, irow4996, rows5003]
  all_goals rfl

theorem atot4996 : totK PA10K2 A10K2.u4996 = [0, 1025412600873, 3769361954710, 3826582255652, 930654151287, 39266247089, 0, 0, 0, 0] := by
  rw [show A10K2.u4996 = KTree.node A10K2.t5002 (nat_lit 76719331) (nat_lit 10483448895) (nat_lit 0) A10K2.t5003 from rfl, totK_node, tot5002, tot5003]
  decide +kernel

theorem arows4998 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4998 = true := by
  rw [show A10K2.u4998 = KTree.node A10K2.t5004 (nat_lit 76727483) (nat_lit 7069627424) (nat_lit 0) A10K2.t5005 from rfl, allE_node, rows5004, irow4998, rows5005]
  all_goals rfl

theorem atot4998 : totK PA10K2 A10K2.u4998 = [0, 1014948975921, 3648231645233, 3774887261190, 1015503800822, 63495312472, 0, 0, 0, 0] := by
  rw [show A10K2.u4998 = KTree.node A10K2.t5004 (nat_lit 76727483) (nat_lit 7069627424) (nat_lit 0) A10K2.t5005 from rfl, totK_node, tot5004, tot5005]
  decide +kernel

theorem arows4999 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4999 = true := by
  rw [show A10K2.u4999 = KTree.node A10K2.t5006 (nat_lit 76733090) (nat_lit 13130920533) (nat_lit 0) A10K2.t5007 from rfl, allE_node, rows5006, irow4999, rows5007]
  all_goals rfl

theorem atot4999 : totK PA10K2 A10K2.u4999 = [0, 541973644762, 2537511207892, 4043220067318, 1974056611100, 291459347602, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u4999 = KTree.node A10K2.t5006 (nat_lit 76733090) (nat_lit 13130920533) (nat_lit 0) A10K2.t5007 from rfl, totK_node, tot5006, tot5007]
  decide +kernel

theorem arows5003 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5003 = true := by
  rw [show A10K2.u5003 = KTree.node A10K2.t5008 (nat_lit 76812629) (nat_lit 6468576712) (nat_lit 0) A10K2.t5009 from rfl, allE_node, rows5008, irow5003, rows5009]
  all_goals rfl

theorem atot5003 : totK PA10K2 A10K2.u5003 = [0, 257947951571, 1925547234405, 3945731296940, 2679225298708, 549499131491, 30818366867, 0, 0, 0] := by
  rw [show A10K2.u5003 = KTree.node A10K2.t5008 (nat_lit 76812629) (nat_lit 6468576712) (nat_lit 0) A10K2.t5009 from rfl, totK_node, tot5008, tot5009]
  decide +kernel

theorem arows5004 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5004 = true := by
  rw [show A10K2.u5004 = KTree.node A10K2.t5010 (nat_lit 76826284) (nat_lit 11831981296) (nat_lit 0) A10K2.t5011 from rfl, allE_node, rows5010, irow5004, rows5011]
  all_goals rfl

theorem atot5004 : totK PA10K2 A10K2.u5004 = [0, 784354618750, 3238261784944, 3971886491586, 1409303347722, 108437783054, 0, 0, 0, 0] := by
  rw [show A10K2.u5004 = KTree.node A10K2.t5010 (nat_lit 76826284) (nat_lit 11831981296) (nat_lit 0) A10K2.t5011 from rfl, totK_node, tot5010, tot5011]
  decide +kernel

theorem arows5006 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5006 = true := by
  rw [show A10K2.u5006 = KTree.node A10K2.t5012 (nat_lit 76833153) (nat_lit 10320576489) (nat_lit 0) A10K2.t5013 from rfl, allE_node, rows5012, irow5006, rows5013]
  all_goals rfl

theorem atot5006 : totK PA10K2 A10K2.u5006 = [0, 458520426296, 2407962218387, 4114968638577, 2266382829407, 331047127058, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u5006 = KTree.node A10K2.t5012 (nat_lit 76833153) (nat_lit 10320576489) (nat_lit 0) A10K2.t5013 from rfl, totK_node, tot5012, tot5013]
  decide +kernel

theorem arows5007 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5007 = true := by
  rw [show A10K2.u5007 = KTree.node A10K2.t5014 (nat_lit 76883747) (nat_lit 10308727980) (nat_lit 0) A10K2.t5015 from rfl, allE_node, rows5014, irow5007, rows5015]
  all_goals rfl

theorem atot5007 : totK PA10K2 A10K2.u5007 = [0, 803239508316, 3070973566430, 3789274569106, 1765306791930, 270999294701, 6853348008, 0, 0, 0] := by
  rw [show A10K2.u5007 = KTree.node A10K2.t5014 (nat_lit 76883747) (nat_lit 10308727980) (nat_lit 0) A10K2.t5015 from rfl, totK_node, tot5014, tot5015]
  decide +kernel

theorem arows5010 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5010 = true := by
  rw [show A10K2.u5010 = KTree.node A10K2.t5016 (nat_lit 76888356) (nat_lit 14146312874) (nat_lit 0) A10K2.t5017 from rfl, allE_node, rows5016, irow5010, rows5017]
  all_goals rfl

theorem atot5010 : totK PA10K2 A10K2.u5010 = [0, 314342126396, 1770993638644, 3795868711205, 2891796838183, 607296232050, 31452573850, 0, 0, 0] := by
  rw [show A10K2.u5010 = KTree.node A10K2.t5016 (nat_lit 76888356) (nat_lit 14146312874) (nat_lit 0) A10K2.t5017 from rfl, totK_node, tot5016, tot5017]
  decide +kernel

theorem arows5011 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5011 = true := by
  rw [show A10K2.u5011 = KTree.node A10K2.t5018 (nat_lit 76892941) (nat_lit 5825883562) (nat_lit 0) A10K2.t5019 from rfl, allE_node, rows5018, irow5011, rows5019]
  all_goals rfl

theorem atot5011 : totK PA10K2 A10K2.u5011 = [0, 470624164805, 2745916596221, 4318737108970, 1854001042472, 159950145403, 0, 0, 0, 0] := by
  rw [show A10K2.u5011 = KTree.node A10K2.t5018 (nat_lit 76892941) (nat_lit 5825883562) (nat_lit 0) A10K2.t5019 from rfl, totK_node, tot5018, tot5019]
  decide +kernel

theorem arows5013 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5013 = true := by
  rw [show A10K2.u5013 = KTree.node A10K2.t5020 (nat_lit 76902079) (nat_lit 14115639999) (nat_lit 0) A10K2.t5021 from rfl, allE_node, rows5020, irow5013, rows5021]
  all_goals rfl

theorem atot5013 : totK PA10K2 A10K2.u5013 = [0, 636121943500, 2527764321504, 3810028118494, 2394064173716, 463918772567, 13317224979, 0, 0, 0] := by
  rw [show A10K2.u5013 = KTree.node A10K2.t5020 (nat_lit 76902079) (nat_lit 14115639999) (nat_lit 0) A10K2.t5021 from rfl, totK_node, tot5020, tot5021]
  decide +kernel

theorem arows5014 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5014 = true := by
  rw [show A10K2.u5014 = KTree.node A10K2.t5022 (nat_lit 76942345) (nat_lit 9732766126) (nat_lit 0) A10K2.t5023 from rfl, allE_node, rows5022, irow5014, rows5023]
  all_goals rfl

theorem atot5014 : totK PA10K2 A10K2.u5014 = [0, 567168627722, 2710564219812, 3903082418403, 1872834302696, 330766427866, 24614390653, 0, 0, 0] := by
  rw [show A10K2.u5014 = KTree.node A10K2.t5022 (nat_lit 76942345) (nat_lit 9732766126) (nat_lit 0) A10K2.t5023 from rfl, totK_node, tot5022, tot5023]
  decide +kernel

theorem arows5019 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5019 = true := by
  rw [show A10K2.u5019 = KTree.node A10K2.t5024 (nat_lit 76949183) (nat_lit 11208942370) (nat_lit 0) A10K2.t5025 from rfl, allE_node, rows5024, irow5019, rows5025]
  all_goals rfl

theorem atot5019 : totK PA10K2 A10K2.u5019 = [0, 745073480358, 2998454811898, 3891179511362, 1692005267918, 195082135425, 5460492893, 0, 0, 0] := by
  rw [show A10K2.u5019 = KTree.node A10K2.t5024 (nat_lit 76949183) (nat_lit 11208942370) (nat_lit 0) A10K2.t5025 from rfl, totK_node, tot5024, tot5025]
  decide +kernel

theorem arows5020 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5020 = true := by
  rw [show A10K2.u5020 = KTree.node A10K2.t5026 (nat_lit 76954145) (nat_lit 9354464869) (nat_lit 0) A10K2.t5027 from rfl, allE_node, rows5026, irow5020, rows5027]
  all_goals rfl

theorem atot5020 : totK PA10K2 A10K2.u5020 = [0, 377644818022, 1961021442586, 3830676301210, 2642596353520, 513559548322, 31003444686, 0, 0, 0] := by
  rw [show A10K2.u5020 = KTree.node A10K2.t5026 (nat_lit 76954145) (nat_lit 9354464869) (nat_lit 0) A10K2.t5027 from rfl, totK_node, tot5026, tot5027]
  decide +kernel

theorem arows5022 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5022 = true := by
  rw [show A10K2.u5022 = KTree.node A10K2.t5028 (nat_lit 76958490) (nat_lit 12655625857) (nat_lit 0) A10K2.t5029 from rfl, allE_node, rows5028, irow5022, rows5029]
  all_goals rfl

theorem atot5022 : totK PA10K2 A10K2.u5022 = [0, 474214578890, 2763213655559, 4322187825185, 1728861320546, 138456623420, 0, 0, 0, 0] := by
  rw [show A10K2.u5022 = KTree.node A10K2.t5028 (nat_lit 76958490) (nat_lit 12655625857) (nat_lit 0) A10K2.t5029 from rfl, totK_node, tot5028, tot5029]
  decide +kernel

theorem arows5023 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5023 = true := by
  rw [show A10K2.u5023 = KTree.node A10K2.t5030 (nat_lit 76974304) (nat_lit 8896386222) (nat_lit 0) A10K2.t5031 from rfl, allE_node, rows5030, irow5023, rows5031]
  all_goals rfl

theorem atot5023 : totK PA10K2 A10K2.u5023 = [0, 0, 1030164315514, 3733130944576, 3623370599102, 877741658130, 57372072225, 0, 0, 0] := by
  rw [show A10K2.u5023 = KTree.node A10K2.t5030 (nat_lit 76974304) (nat_lit 8896386222) (nat_lit 0) A10K2.t5031 from rfl, totK_node, tot5030, tot5031]
  decide +kernel

theorem arows5026 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5026 = true := by
  rw [show A10K2.u5026 = KTree.node A10K2.t5032 (nat_lit 76988706) (nat_lit 11053555411) (nat_lit 0) A10K2.t5033 from rfl, allE_node, rows5032, irow5026, rows5033]
  all_goals rfl

theorem atot5026 : totK PA10K2 A10K2.u5026 = [0, 0, 1075676366847, 3679247323510, 3524594584638, 919395254407, 61975941459, 0, 0, 0] := by
  rw [show A10K2.u5026 = KTree.node A10K2.t5032 (nat_lit 76988706) (nat_lit 11053555411) (nat_lit 0) A10K2.t5033 from rfl, totK_node, tot5032, tot5033]
  decide +kernel

theorem arows5027 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5027 = true := by
  rw [show A10K2.u5027 = KTree.node A10K2.t5034 (nat_lit 76994574) (nat_lit 8506885534) (nat_lit 0) A10K2.t5035 from rfl, allE_node, rows5034, irow5027, rows5035]
  all_goals rfl

theorem atot5027 : totK PA10K2 A10K2.u5027 = [0, 319364639558, 1187218927669, 2522528114467, 3344165971702, 1658335102020, 265614550179, 6354482628, 0, 0] := by
  rw [show A10K2.u5027 = KTree.node A10K2.t5034 (nat_lit 76994574) (nat_lit 8506885534) (nat_lit 0) A10K2.t5035 from rfl, totK_node, tot5034, tot5035]
  decide +kernel

theorem arows5029 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5029 = true := by
  rw [show A10K2.u5029 = KTree.node A10K2.t5036 (nat_lit 77598245) (nat_lit 6710424982) (nat_lit 0) A10K2.t5037 from rfl, allE_node, rows5036, irow5029, rows5037]
  all_goals rfl

theorem atot5029 : totK PA10K2 A10K2.u5029 = [0, 526179114281, 2528526893172, 3940150016680, 2136827027983, 406344512596, 25371180993, 0, 0, 0] := by
  rw [show A10K2.u5029 = KTree.node A10K2.t5036 (nat_lit 77598245) (nat_lit 6710424982) (nat_lit 0) A10K2.t5037 from rfl, totK_node, tot5036, tot5037]
  decide +kernel

theorem arows5030 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5030 = true := by
  rw [show A10K2.u5030 = KTree.node A10K2.t5038 (nat_lit 77611525) (nat_lit 6386651307) (nat_lit 0) A10K2.t5039 from rfl, allE_node, rows5038, irow5030, rows5039]
  all_goals rfl

theorem atot5030 : totK PA10K2 A10K2.u5030 = [0, 745959159527, 2872263612091, 3722335148215, 1805081097006, 242119815985, 5460492893, 0, 0, 0] := by
  rw [show A10K2.u5030 = KTree.node A10K2.t5038 (nat_lit 77611525) (nat_lit 6386651307) (nat_lit 0) A10K2.t5039 from rfl, totK_node, tot5038, tot5039]
  decide +kernel

theorem arows5034 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5034 = true := by
  rw [show A10K2.u5034 = KTree.node A10K2.t5040 (nat_lit 77617493) (nat_lit 6970753704) (nat_lit 0) A10K2.t5041 from rfl, allE_node, rows5040, irow5034, rows5041]
  all_goals rfl

theorem atot5034 : totK PA10K2 A10K2.u5034 = [0, 472601942740, 2442990747928, 4177570120090, 2187541760145, 300511238796, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u5034 = KTree.node A10K2.t5040 (nat_lit 77617493) (nat_lit 6970753704) (nat_lit 0) A10K2.t5041 from rfl, totK_node, tot5040, tot5041]
  decide +kernel

theorem arows5035 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5035 = true := by
  rw [show A10K2.u5035 = KTree.node A10K2.t5042 (nat_lit 77624108) (nat_lit 11809024653) (nat_lit 0) A10K2.t5043 from rfl, allE_node, rows5042, irow5035, rows5043]
  all_goals rfl

theorem atot5035 : totK PA10K2 A10K2.u5035 = [0, 153187210152, 1678809045211, 4024656005709, 3256994143743, 805397592322, 40858060673, 0, 0, 0] := by
  rw [show A10K2.u5035 = KTree.node A10K2.t5042 (nat_lit 77624108) (nat_lit 11809024653) (nat_lit 0) A10K2.t5043 from rfl, totK_node, tot5042, tot5043]
  decide +kernel

theorem arows5037 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5037 = true := by
  rw [show A10K2.u5037 = KTree.node A10K2.t5044 (nat_lit 77630642) (nat_lit 6736996142) (nat_lit 0) A10K2.t5045 from rfl, allE_node, rows5044, irow5037, rows5045]
  all_goals rfl

theorem atot5037 : totK PA10K2 A10K2.u5037 = [0, 0, 582440298174, 2750603756312, 3926096615149, 1838171960597, 367009774902, 25239774317, 0, 0] := by
  rw [show A10K2.u5037 = KTree.node A10K2.t5044 (nat_lit 77630642) (nat_lit 6736996142) (nat_lit 0) A10K2.t5045 from rfl, totK_node, tot5044, tot5045]
  decide +kernel

theorem arows5038 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5038 = true := by
  rw [show A10K2.u5038 = KTree.node A10K2.t5046 (nat_lit 77644132) (nat_lit 13775768551) (nat_lit 0) A10K2.t5047 from rfl, allE_node, rows5046, irow5038, rows5047]
  all_goals rfl

theorem atot5038 : totK PA10K2 A10K2.u5038 = [0, 0, 743124031774, 2856932075462, 3742701550898, 1763963168351, 245128305183, 5410721913, 0, 0] := by
  rw [show A10K2.u5038 = KTree.node A10K2.t5046 (nat_lit 77644132) (nat_lit 13775768551) (nat_lit 0) A10K2.t5047 from rfl, totK_node, tot5046, tot5047]
  decide +kernel

theorem arows5041 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5041 = true := by
  rw [show A10K2.u5041 = KTree.node A10K2.t5048 (nat_lit 77650274) (nat_lit 11887954746) (nat_lit 0) A10K2.t5049 from rfl, allE_node, rows5048, irow5041, rows5049]
  all_goals rfl

theorem atot5041 : totK PA10K2 A10K2.u5041 = [0, 0, 494232055333, 2692975752613, 4250048850706, 1868285606654, 219085974858, 5546304973, 0, 0] := by
  rw [show A10K2.u5041 = KTree.node A10K2.t5048 (nat_lit 77650274) (nat_lit 11887954746) (nat_lit 0) A10K2.t5049 from rfl, totK_node, tot5048, tot5049]
  decide +kernel

theorem arows5042 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5042 = true := by
  rw [show A10K2.u5042 = KTree.node A10K2.t5050 (nat_lit 77726604) (nat_lit 8615425820) (nat_lit 0) A10K2.t5051 from rfl, allE_node, rows5050, irow5042, rows5051]
  all_goals rfl

theorem atot5042 : totK PA10K2 A10K2.u5042 = [0, 778776062315, 2968909395673, 3720506682844, 1875951669076, 451578162791, 29791859037, 0, 0, 0] := by
  rw [show A10K2.u5042 = KTree.node A10K2.t5050 (nat_lit 77726604) (nat_lit 8615425820) (nat_lit 0) A10K2.t5051 from rfl, totK_node, tot5050, tot5051]
  decide +kernel

theorem arows5044 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5044 = true := by
  rw [show A10K2.u5044 = KTree.node A10K2.t5052 (nat_lit 77732608) (nat_lit 14179613491) (nat_lit 0) A10K2.t5053 from rfl, allE_node, rows5052, irow5044, rows5053]
  all_goals rfl

theorem atot5044 : totK PA10K2 A10K2.u5044 = [0, 410905957332, 2040382013842, 3845228501338, 2659952941660, 566252869619, 30831673886, 0, 0, 0] := by
  rw [show A10K2.u5044 = KTree.node A10K2.t5052 (nat_lit 77732608) (nat_lit 14179613491) (nat_lit 0) A10K2.t5053 from rfl, totK_node, tot5052, tot5053]
  decide +kernel

theorem arows5045 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5045 = true := by
  rw [show A10K2.u5045 = KTree.node A10K2.t5054 (nat_lit 77740077) (nat_lit 6547425208) (nat_lit 0) A10K2.t5055 from rfl, allE_node, rows5054, irow5045, rows5055]
  all_goals rfl

theorem atot5045 : totK PA10K2 A10K2.u5045 = [0, 408844855940, 2238727802263, 3831920069665, 2457193124595, 489555158112, 31333686660, 0, 0, 0] := by
  rw [show A10K2.u5045 = KTree.node A10K2.t5054 (nat_lit 77740077) (nat_lit 6547425208) (nat_lit 0) A10K2.t5055 from rfl, totK_node, tot5054, tot5055]
  decide +kernel

theorem arows5051 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5051 = true := by
  rw [show A10K2.u5051 = KTree.node A10K2.t5056 (nat_lit 77744808) (nat_lit 8619919229) (nat_lit 0) A10K2.t5057 from rfl, allE_node, rows5056, irow5051, rows5057]
  all_goals rfl

theorem atot5051 : totK PA10K2 A10K2.u5051 = [0, 539891055239, 2838311677564, 4150927106897, 1686898322764, 139987411557, 0, 0, 0, 0] := by
  rw [show A10K2.u5051 = KTree.node A10K2.t5056 (nat_lit 77744808) (nat_lit 8619919229) (nat_lit 0) A10K2.t5057 from rfl, totK_node, tot5056, tot5057]
  decide +kernel

theorem arows5052 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5052 = true := by
  rw [show A10K2.u5052 = KTree.node A10K2.t5058 (nat_lit 77760666) (nat_lit 12576118988) (nat_lit 0) A10K2.t5059 from rfl, allE_node, rows5058, irow5052, rows5059]
  all_goals rfl

theorem atot5052 : totK PA10K2 A10K2.u5052 = [0, 0, 986391887808, 3783254867872, 3859249420734, 956748761219, 45137667897, 0, 0, 0] := by
  rw [show A10K2.u5052 = KTree.node A10K2.t5058 (nat_lit 77760666) (nat_lit 12576118988) (nat_lit 0) A10K2.t5059 from rfl, totK_node, tot5058, tot5059]
  decide +kernel

theorem arows5054 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5054 = true := by
  rw [show A10K2.u5054 = KTree.node A10K2.t5060 (nat_lit 77775111) (nat_lit 9190149628) (nat_lit 0) A10K2.t5061 from rfl, allE_node, rows5060, irow5054, rows5061]
  all_goals rfl

theorem atot5054 : totK PA10K2 A10K2.u5054 = [0, 0, 954504362172, 3490946272496, 3798265032806, 1073016243364, 82303251995, 0, 0, 0] := by
  rw [show A10K2.u5054 = KTree.node A10K2.t5060 (nat_lit 77775111) (nat_lit 9190149628) (nat_lit 0) A10K2.t5061 from rfl, totK_node, tot5060, tot5061]
  decide +kernel

theorem arows5055 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5055 = true := by
  rw [show A10K2.u5055 = KTree.node A10K2.t5062 (nat_lit 77780375) (nat_lit 7980175745) (nat_lit 0) A10K2.t5063 from rfl, allE_node, rows5062, irow5055, rows5063]
  all_goals rfl

theorem atot5055 : totK PA10K2 A10K2.u5055 = [0, 306130628101, 1131825906576, 2474643951604, 3449688779143, 1697071192722, 265773289542, 6354482628, 0, 0] := by
  rw [show A10K2.u5055 = KTree.node A10K2.t5062 (nat_lit 77780375) (nat_lit 7980175745) (nat_lit 0) A10K2.t5063 from rfl, totK_node, tot5062, tot5063]
  decide +kernel

theorem arows5058 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5058 = true := by
  rw [show A10K2.u5058 = KTree.node A10K2.t5064 (nat_lit 77795219) (nat_lit 7351021301) (nat_lit 0) A10K2.t5065 from rfl, allE_node, rows5064, irow5058, rows5065]
  all_goals rfl

theorem atot5058 : totK PA10K2 A10K2.u5058 = [0, 464557879428, 2393999677450, 4078250151989, 2379641732525, 447418140346, 25351274858, 0, 0, 0] := by
  rw [show A10K2.u5058 = KTree.node A10K2.t5064 (nat_lit 77795219) (nat_lit 7351021301) (nat_lit 0) A10K2.t5065 from rfl, totK_node, tot5064, tot5065]
  decide +kernel

theorem arows5059 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5059 = true := by
  rw [show A10K2.u5059 = KTree.node A10K2.t5066 (nat_lit 77818948) (nat_lit 9180676555) (nat_lit 0) A10K2.t5067 from rfl, allE_node, rows5066, irow5059, rows5067]
  all_goals rfl

theorem atot5059 : totK PA10K2 A10K2.u5059 = [0, 593191967102, 2724823560130, 4120256498202, 2263008251082, 365600285975, 12312941161, 0, 0, 0] := by
  rw [show A10K2.u5059 = KTree.node A10K2.t5066 (nat_lit 77818948) (nat_lit 9180676555) (nat_lit 0) A10K2.t5067 from rfl, totK_node, tot5066, tot5067]
  decide +kernel

theorem arows5061 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5061 = true := by
  rw [show A10K2.u5061 = KTree.node A10K2.t5068 (nat_lit 77824390) (nat_lit 15557612177) (nat_lit 0) A10K2.t5069 from rfl, allE_node, rows5068, irow5061, rows5069]
  all_goals rfl

theorem atot5061 : totK PA10K2 A10K2.u5061 = [0, 0, 1074223171701, 3760383836168, 3870945161322, 1146532136656, 80261166969, 0, 0, 0] := by
  rw [show A10K2.u5061 = KTree.node A10K2.t5068 (nat_lit 77824390) (nat_lit 15557612177) (nat_lit 0) A10K2.t5069 from rfl, totK_node, tot5068, tot5069]
  decide +kernel

theorem arows5062 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5062 = true := by
  rw [show A10K2.u5062 = KTree.node A10K2.t5070 (nat_lit 77830445) (nat_lit 6629444949) (nat_lit 0) A10K2.t5071 from rfl, allE_node, rows5070, irow5062, rows5071]
  all_goals rfl

theorem atot5062 : totK PA10K2 A10K2.u5062 = [0, 0, 471468432376, 2593524975060, 4297345447305, 2217106355409, 302822342103, 6904928264, 0, 0] := by
  rw [show A10K2.u5062 = KTree.node A10K2.t5070 (nat_lit 77830445) (nat_lit 6629444949) (nat_lit 0) A10K2.t5071 from rfl, totK_node, tot5070, tot5071]
  decide +kernel

theorem arows5066 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5066 = true := by
  rw [show A10K2.u5066 = KTree.node A10K2.t5072 (nat_lit 78194461) (nat_lit 6295643072) (nat_lit 0) A10K2.t5073 from rfl, allE_node, rows5072, irow5066, rows5073]
  all_goals rfl

theorem atot5066 : totK PA10K2 A10K2.u5066 = [0, 848323660542, 3026208454579, 3488985090801, 1823210700529, 572848821379, 50888518472, 0, 0, 0] := by
  rw [show A10K2.u5066 = KTree.node A10K2.t5072 (nat_lit 78194461) (nat_lit 6295643072) (nat_lit 0) A10K2.t5073 from rfl, totK_node, tot5072, tot5073]
  decide +kernel

theorem arows5067 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5067 = true := by
  rw [show A10K2.u5067 = KTree.node A10K2.t5074 (nat_lit 78198999) (nat_lit 10764006638) (nat_lit 0) A10K2.t5075 from rfl, allE_node, rows5074, irow5067, rows5075]
  all_goals rfl

theorem atot5067 : totK PA10K2 A10K2.u5067 = [0, 167599367873, 1638579330660, 3962217631687, 3065444412239, 639276298334, 31768748853, 0, 0, 0] := by
  rw [show A10K2.u5067 = KTree.node A10K2.t5074 (nat_lit 78198999) (nat_lit 10764006638) (nat_lit 0) A10K2.t5075 from rfl, totK_node, tot5074, tot5075]
  decide +kernel

theorem arows5069 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5069 = true := by
  rw [show A10K2.u5069 = KTree.node A10K2.t5076 (nat_lit 78203427) (nat_lit 8217222220) (nat_lit 0) A10K2.t5077 from rfl, allE_node, rows5076, irow5069, rows5077]
  all_goals rfl

theorem atot5069 : totK PA10K2 A10K2.u5069 = [0, 579135734717, 2855082032535, 4195590080189, 1736938215423, 138626157634, 0, 0, 0, 0] := by
  rw [show A10K2.u5069 = KTree.node A10K2.t5076 (nat_lit 78203427) (nat_lit 8217222220) (nat_lit 0) A10K2.t5077 from rfl, totK_node, tot5076, tot5077]
  decide +kernel

theorem arows5070 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5070 = true := by
  rw [show A10K2.u5070 = KTree.node A10K2.t5078 (nat_lit 78212247) (nat_lit 14086296234) (nat_lit 0) A10K2.t5079 from rfl, allE_node, rows5078, irow5070, rows5079]
  all_goals rfl

theorem atot5070 : totK PA10K2 A10K2.u5070 = [0, 628467226016, 2681705502240, 4040338074599, 2318407499675, 378447415238, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u5070 = KTree.node A10K2.t5078 (nat_lit 78212247) (nat_lit 14086296234) (nat_lit 0) A10K2.t5079 from rfl, totK_node, tot5078, tot5079]
  decide +kernel

theorem arows5073 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5073 = true := by
  rw [show A10K2.u5073 = KTree.node A10K2.t5080 (nat_lit 78226844) (nat_lit 9162386381) (nat_lit 0) A10K2.t5081 from rfl, allE_node, rows5080, irow5073, rows5081]
  all_goals rfl

theorem atot5073 : totK PA10K2 A10K2.u5073 = [0, 0, 996800390863, 3636116670130, 3868892164590, 1162044345610, 74603424519, 0, 0, 0] := by
  rw [show A10K2.u5073 = KTree.node A10K2.t5080 (nat_lit 78226844) (nat_lit 9162386381) (nat_lit 0) A10K2.t5081 from rfl, totK_node, tot5080, tot5081]
  decide +kernel

theorem arows5074 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5074 = true := by
  rw [show A10K2.u5074 = KTree.node A10K2.t5082 (nat_lit 78231395) (nat_lit 9296564231) (nat_lit 0) A10K2.t5083 from rfl, allE_node, rows5082, irow5074, rows5083]
  all_goals rfl

theorem atot5074 : totK PA10K2 A10K2.u5074 = [0, 0, 275279134076, 1886499099440, 3954928351769, 2694077650724, 566391600505, 31082886609, 0, 0] := by
  rw [show A10K2.u5074 = KTree.node A10K2.t5082 (nat_lit 78231395) (nat_lit 9296564231) (nat_lit 0) A10K2.t5083 from rfl, totK_node, tot5082, tot5083]
  decide +kernel

theorem arows5076 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5076 = true := by
  rw [show A10K2.u5076 = KTree.node A10K2.t5084 (nat_lit 78235934) (nat_lit 9207398433) (nat_lit 0) A10K2.t5085 from rfl, allE_node, rows5084, irow5076, rows5085]
  all_goals rfl

theorem atot5076 : totK PA10K2 A10K2.u5076 = [0, 0, 578600964295, 2996149517465, 4225176744415, 1518208079070, 103914786332, 0, 0, 0] := by
  rw [show A10K2.u5076 = KTree.node A10K2.t5084 (nat_lit 78235934) (nat_lit 9207398433) (nat_lit 0) A10K2.t5085 from rfl, totK_node, tot5084, tot5085]
  decide +kernel

theorem arows5077 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5077 = true := by
  rw [show A10K2.u5077 = KTree.node A10K2.t5086 (nat_lit 78244983) (nat_lit 14652227679) (nat_lit 0) A10K2.t5087 from rfl, allE_node, rows5086, irow5077, rows5087]
  all_goals rfl

theorem atot5077 : totK PA10K2 A10K2.u5077 = [0, 272465788330, 1537930120659, 3124684312021, 3192266604018, 1454081417976, 190828678798, 6121173289, 0, 0] := by
  rw [show A10K2.u5077 = KTree.node A10K2.t5086 (nat_lit 78244983) (nat_lit 14652227679) (nat_lit 0) A10K2.t5087 from rfl, totK_node, tot5086, tot5087]
  decide +kernel

theorem arows5082 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5082 = true := by
  rw [show A10K2.u5082 = KTree.node A10K2.t5088 (nat_lit 78254670) (nat_lit 6516377241) (nat_lit 0) A10K2.t5089 from rfl, allE_node, rows5088, irow5082, rows5089]
  all_goals rfl

theorem atot5082 : totK PA10K2 A10K2.u5082 = [0, 587455450678, 2452622231982, 3717164308786, 2192253246761, 446742611023, 30402056026, 0, 0, 0] := by
  rw [show A10K2.u5082 = KTree.node A10K2.t5088 (nat_lit 78254670) (nat_lit 6516377241) (nat_lit 0) A10K2.t5089 from rfl, totK_node, tot5088, tot5089]
  decide +kernel

theorem arows5083 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5083 = true := by
  rw [show A10K2.u5083 = KTree.node A10K2.t5090 (nat_lit 78261722) (nat_lit 14491231619) (nat_lit 0) A10K2.t5091 from rfl, allE_node, rows5090, irow5083, rows5091]
  all_goals rfl

theorem atot5083 : totK PA10K2 A10K2.u5083 = [0, 475708131122, 2518036353885, 4085127625399, 2217132550311, 419950299588, 25734533292, 0, 0, 0] := by
  rw [show A10K2.u5083 = KTree.node A10K2.t5090 (nat_lit 78261722) (nat_lit 14491231619) (nat_lit 0) A10K2.t5091 from rfl, totK_node, tot5090, tot5091]
  decide +kernel

theorem arows5085 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5085 = true := by
  rw [show A10K2.u5085 = KTree.node A10K2.t5092 (nat_lit 78267148) (nat_lit 11917901536) (nat_lit 0) A10K2.t5093 from rfl, allE_node, rows5092, irow5085, rows5093]
  all_goals rfl

theorem atot5085 : totK PA10K2 A10K2.u5085 = [0, 817664287946, 2945463166491, 3603107198983, 1849224657611, 272121617700, 6034215561, 0, 0, 0] := by
  rw [show A10K2.u5085 = KTree.node A10K2.t5092 (nat_lit 78267148) (nat_lit 11917901536) (nat_lit 0) A10K2.t5093 from rfl, totK_node, tot5092, tot5093]
  decide +kernel

theorem arows5086 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5086 = true := by
  rw [show A10K2.u5086 = KTree.node A10K2.t5094 (nat_lit 78272724) (nat_lit 11800462688) (nat_lit 0) A10K2.t5095 from rfl, allE_node, rows5094, irow5086, rows5095]
  all_goals rfl

theorem atot5086 : totK PA10K2 A10K2.u5086 = [0, 0, 1513524102148, 4248687007989, 3024469712054, 573742306983, 31558137809, 0, 0, 0] := by
  rw [show A10K2.u5086 = KTree.node A10K2.t5094 (nat_lit 78272724) (nat_lit 11800462688) (nat_lit 0) A10K2.t5095 from rfl, totK_node, tot5094, tot5095]
  decide +kernel

theorem arows5089 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5089 = true := by
  rw [show A10K2.u5089 = KTree.node A10K2.t5096 (nat_lit 78292822) (nat_lit 11023673571) (nat_lit 0) A10K2.t5097 from rfl, allE_node, rows5096, irow5089, rows5097]
  all_goals rfl

theorem atot5089 : totK PA10K2 A10K2.u5089 = [0, 0, 1001496006593, 3698384696972, 3921920649019, 1010744753649, 45698881016, 0, 0, 0] := by
  rw [show A10K2.u5089 = KTree.node A10K2.t5096 (nat_lit 78292822) (nat_lit 11023673571) (nat_lit 0) A10K2.t5097 from rfl, totK_node, tot5096, tot5097]
  decide +kernel

theorem arows5090 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5090 = true := by
  rw [show A10K2.u5090 = KTree.node A10K2.t5098 (nat_lit 78301015) (nat_lit 4395773119) (nat_lit 0) A10K2.t5099 from rfl, allE_node, rows5098, irow5090, rows5099]
  all_goals rfl

theorem atot5090 : totK PA10K2 A10K2.u5090 = [0, 0, 773464716480, 3271585631905, 3897504812187, 1219974316532, 102397746322, 0, 0, 0] := by
  rw [show A10K2.u5090 = KTree.node A10K2.t5098 (nat_lit 78301015) (nat_lit 4395773119) (nat_lit 0) A10K2.t5099 from rfl, totK_node, tot5098, tot5099]
  decide +kernel

theorem arows5092 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5092 = true := by
  rw [show A10K2.u5092 = KTree.node A10K2.t5100 (nat_lit 78325238) (nat_lit 16429468305) (nat_lit 0) A10K2.t5101 from rfl, allE_node, rows5100, irow5092, rows5101]
  all_goals rfl

theorem atot5092 : totK PA10K2 A10K2.u5092 = [0, 773889436601, 2632804821270, 2970600822676, 2045649985642, 1069445138878, 213642913445, 6354482628, 0, 0] := by
  rw [show A10K2.u5092 = KTree.node A10K2.t5100 (nat_lit 78325238) (nat_lit 16429468305) (nat_lit 0) A10K2.t5101 from rfl, totK_node, tot5100, tot5101]
  decide +kernel

theorem arows5093 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5093 = true := by
  rw [show A10K2.u5093 = KTree.node A10K2.t5102 (nat_lit 78330146) (nat_lit 13255969661) (nat_lit 0) A10K2.t5103 from rfl, allE_node, rows5102, irow5093, rows5103]
  all_goals rfl

theorem atot5093 : totK PA10K2 A10K2.u5093 = [0, 287800699719, 1921034362271, 4068381382849, 2962714764403, 621200366949, 31522233512, 0, 0, 0] := by
  rw [show A10K2.u5093 = KTree.node A10K2.t5102 (nat_lit 78330146) (nat_lit 13255969661) (nat_lit 0) A10K2.t5103 from rfl, totK_node, tot5102, tot5103]
  decide +kernel

theorem arows5097 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5097 = true := by
  rw [show A10K2.u5097 = KTree.node A10K2.t5104 (nat_lit 78345671) (nat_lit 14357336368) (nat_lit 0) A10K2.t5105 from rfl, allE_node, rows5104, irow5097, rows5105]
  all_goals rfl

theorem atot5097 : totK PA10K2 A10K2.u5097 = [0, 307423764049, 1954039447881, 3975919429881, 3118911185632, 844335779254, 56143165367, 0, 0, 0] := by
  rw [show A10K2.u5097 = KTree.node A10K2.t5104 (nat_lit 78345671) (nat_lit 14357336368) (nat_lit 0) A10K2.t5105 from rfl, totK_node, tot5104, tot5105]
  decide +kernel

theorem arows5098 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5098 = true := by
  rw [show A10K2.u5098 = KTree.node A10K2.t5106 (nat_lit 78359762) (nat_lit 15577264525) (nat_lit 0) A10K2.t5107 from rfl, allE_node, rows5106, irow5098, rows5107]
  all_goals rfl

theorem atot5098 : totK PA10K2 A10K2.u5098 = [0, 0, 655326830950, 2897739357432, 4029970831352, 1974141812517, 282657703668, 7047025452, 0, 0] := by
  rw [show A10K2.u5098 = KTree.node A10K2.t5106 (nat_lit 78359762) (nat_lit 15577264525) (nat_lit 0) A10K2.t5107 from rfl, totK_node, tot5106, tot5107]
  decide +kernel

theorem arows5100 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5100 = true := by
  rw [show A10K2.u5100 = KTree.node A10K2.t5108 (nat_lit 78375987) (nat_lit 7031829568) (nat_lit 0) A10K2.t5109 from rfl, allE_node, rows5108, irow5100, rows5109]
  all_goals rfl

theorem atot5100 : totK PA10K2 A10K2.u5100 = [0, 309035082669, 1457689322216, 3171786579195, 3588784386122, 1386184988550, 105369386230, 0, 0, 0] := by
  rw [show A10K2.u5100 = KTree.node A10K2.t5108 (nat_lit 78375987) (nat_lit 7031829568) (nat_lit 0) A10K2.t5109 from rfl, totK_node, tot5108, tot5109]
  decide +kernel

theorem arows5101 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5101 = true := by
  rw [show A10K2.u5101 = KTree.node A10K2.t5110 (nat_lit 78646734) (nat_lit 14788148207) (nat_lit 0) A10K2.t5111 from rfl, allE_node, rows5110, irow5101, rows5111]
  all_goals rfl

theorem atot5101 : totK PA10K2 A10K2.u5101 = [0, 490159822480, 2463059887368, 3925344380349, 2144179168163, 415734661875, 25371180993, 0, 0, 0] := by
  rw [show A10K2.u5101 = KTree.node A10K2.t5110 (nat_lit 78646734) (nat_lit 14788148207) (nat_lit 0) A10K2.t5111 from rfl, totK_node, tot5110, tot5111]
  decide +kernel

theorem arows5104 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5104 = true := by
  rw [show A10K2.u5104 = KTree.node A10K2.t5112 (nat_lit 78660129) (nat_lit 10144271537) (nat_lit 0) A10K2.t5113 from rfl, allE_node, rows5112, irow5104, rows5113]
  all_goals rfl

theorem atot5104 : totK PA10K2 A10K2.u5104 = [0, 783657094257, 2933595770631, 3697837717730, 1801332115636, 242609116650, 5460492893, 0, 0, 0] := by
  rw [show A10K2.u5104 = KTree.node A10K2.t5112 (nat_lit 78660129) (nat_lit 10144271537) (nat_lit 0) A10K2.t5113 from rfl, totK_node, tot5112, tot5113]
  decide +kernel

theorem arows5105 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5105 = true := by
  rw [show A10K2.u5105 = KTree.node A10K2.t5114 (nat_lit 78666005) (nat_lit 7051909534) (nat_lit 0) A10K2.t5115 from rfl, allE_node, rows5114, irow5105, rows5115]
  all_goals rfl

theorem atot5105 : totK PA10K2 A10K2.u5105 = [0, 429138988169, 2424264618475, 4197375874866, 2198314118032, 301105607360, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u5105 = KTree.node A10K2.t5114 (nat_lit 78666005) (nat_lit 7051909534) (nat_lit 0) A10K2.t5115 from rfl, totK_node, tot5114, tot5115]
  decide +kernel

theorem arows5107 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5107 = true := by
  rw [show A10K2.u5107 = KTree.node A10K2.t5116 (nat_lit 78675526) (nat_lit 14280713247) (nat_lit 0) A10K2.t5117 from rfl, allE_node, rows5116, irow5107, rows5117]
  all_goals rfl

theorem atot5107 : totK PA10K2 A10K2.u5107 = [0, 17179869184, 1363143530316, 4048785397231, 3486787675295, 788811169189, 38413255743, 0, 0, 0] := by
  rw [show A10K2.u5107 = KTree.node A10K2.t5116 (nat_lit 78675526) (nat_lit 14280713247) (nat_lit 0) A10K2.t5117 from rfl, totK_node, tot5116, tot5117]
  decide +kernel

theorem arows5108 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5108 = true := by
  rw [show A10K2.u5108 = KTree.node A10K2.t5118 (nat_lit 78680625) (nat_lit 9945262219) (nat_lit 0) A10K2.t5119 from rfl, allE_node, rows5118, irow5108, rows5119]
  all_goals rfl

theorem atot5108 : totK PA10K2 A10K2.u5108 = [0, 0, 368244125724, 2184435617179, 3956262998754, 2267949143434, 447988493724, 30220878370, 0, 0] := by
  rw [show A10K2.u5108 = KTree.node A10K2.t5118 (nat_lit 78680625) (nat_lit 9945262219) (nat_lit 0) A10K2.t5119 from rfl, totK_node, tot5118, tot5119]
  decide +kernel

theorem arows5118 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5118 = true := by
  rw [show A10K2.u5118 = KTree.node A10K2.t5120 (nat_lit 78694627) (nat_lit 10076610976) (nat_lit 0) A10K2.t5121 from rfl, allE_node, rows5120, irow5118, rows5121]
  all_goals rfl

theorem atot5118 : totK PA10K2 A10K2.u5118 = [0, 0, 619655136887, 3130693306815, 4239014928722, 1374882736442, 96483997752, 0, 0, 0] := by
  rw [show A10K2.u5118 = KTree.node A10K2.t5120 (nat_lit 78694627) (nat_lit 10076610976) (nat_lit 0) A10K2.t5121 from rfl, totK_node, tot5120, tot5121]
  decide +kernel

theorem arows5119 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5119 = true := by
  rw [show A10K2.u5119 = KTree.node A10K2.t5122 (nat_lit 78704065) (nat_lit 9937805989) (nat_lit 0) A10K2.t5123 from rfl, allE_node, rows5122, irow5119, rows5123]
  all_goals rfl

theorem atot5119 : totK PA10K2 A10K2.u5119 = [0, 477404030452, 1994498942945, 3230270381952, 2722318925231, 1063637299581, 155462620214, 5546304973, 0, 0] := by
  rw [show A10K2.u5119 = KTree.node A10K2.t5122 (nat_lit 78704065) (nat_lit 9937805989) (nat_lit 0) A10K2.t5123 from rfl, totK_node, tot5122, tot5123]
  decide +kernel

theorem arows5121 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5121 = true := by
  rw [show A10K2.u5121 = KTree.node A10K2.t5124 (nat_lit 78722325) (nat_lit 6888461581) (nat_lit 0) A10K2.t5125 from rfl, allE_node, rows5124, irow5121, rows5125]
  all_goals rfl

theorem atot5121 : totK PA10K2 A10K2.u5121 = [0, 325104351284, 2017920162946, 3877666608143, 2670519348082, 563554176701, 31768748853, 0, 0, 0] := by
  rw [show A10K2.u5121 = KTree.node A10K2.t5124 (nat_lit 78722325) (nat_lit 6888461581) (nat_lit 0) A10K2.t5125 from rfl, totK_node, tot5124, tot5125]
  decide +kernel

theorem arows5122 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5122 = true := by
  rw [show A10K2.u5122 = KTree.node A10K2.t5126 (nat_lit 78726810) (nat_lit 15100829552) (nat_lit 0) A10K2.t5127 from rfl, allE_node, rows5126, irow5122, rows5127]
  all_goals rfl

theorem atot5122 : totK PA10K2 A10K2.u5122 = [0, 784265249764, 3221666581017, 3983378077965, 1467900909796, 128231518729, 0, 0, 0, 0] := by
  rw [show A10K2.u5122 = KTree.node A10K2.t5126 (nat_lit 78726810) (nat_lit 15100829552) (nat_lit 0) A10K2.t5127 from rfl, totK_node, tot5126, tot5127]
  decide +kernel

theorem arows5125 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5125 = true := by
  rw [show A10K2.u5125 = KTree.node A10K2.t5128 (nat_lit 78734578) (nat_lit 15042214456) (nat_lit 0) A10K2.t5129 from rfl, allE_node, rows5128, irow5125, rows5129]
  all_goals rfl

theorem atot5125 : totK PA10K2 A10K2.u5125 = [0, 461607179050, 2466656806011, 4218041095355, 2249293249216, 302318819792, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u5125 = KTree.node A10K2.t5128 (nat_lit 78734578) (nat_lit 15042214456) (nat_lit 0) A10K2.t5129 from rfl, totK_node, tot5128, tot5129]
  decide +kernel

theorem arows5126 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5126 = true := by
  rw [show A10K2.u5126 = KTree.node A10K2.t5130 (nat_lit 78751217) (nat_lit 3784772940) (nat_lit 0) A10K2.t5131 from rfl, allE_node, rows5130, irow5126, rows5131]
  all_goals rfl

theorem atot5126 : totK PA10K2 A10K2.u5126 = [0, 0, 1072196562388, 3794875606110, 3811948474657, 964507036717, 45449654167, 0, 0, 0] := by
  rw [show A10K2.u5126 = KTree.node A10K2.t5130 (nat_lit 78751217) (nat_lit 3784772940) (nat_lit 0) A10K2.t5131 from rfl, totK_node, tot5130, tot5131]
  decide +kernel

theorem arows5128 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5128 = true := by
  rw [show A10K2.u5128 = KTree.node A10K2.t5132 (nat_lit 78756100) (nat_lit 12950680606) (nat_lit 0) A10K2.t5133 from rfl, allE_node, rows5132, irow5128, rows5133]
  all_goals rfl

theorem atot5128 : totK PA10K2 A10K2.u5128 = [0, 0, 375139718867, 2217169258053, 3965633832883, 2328000453195, 457429618912, 30647824416, 0, 0] := by
  rw [show A10K2.u5128 = KTree.node A10K2.t5132 (nat_lit 78756100) (nat_lit 12950680606) (nat_lit 0) A10K2.t5133 from rfl, totK_node, tot5132, tot5133]
  decide +kernel

theorem arows5129 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5129 = true := by
  rw [show A10K2.u5129 = KTree.node A10K2.t5134 (nat_lit 78762019) (nat_lit 4761851963) (nat_lit 0) A10K2.t5135 from rfl, allE_node, rows5134, irow5129, rows5135]
  all_goals rfl

theorem atot5129 : totK PA10K2 A10K2.u5129 = [0, 0, 405699854225, 2482233618336, 4213579524438, 1977076203683, 245422692313, 0, 0, 0] := by
  rw [show A10K2.u5129 = KTree.node A10K2.t5134 (nat_lit 78762019) (nat_lit 4761851963) (nat_lit 0) A10K2.t5135 from rfl, totK_node, tot5134, tot5135]
  decide +kernel

theorem arows5133 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5133 = true := by
  rw [show A10K2.u5133 = KTree.node A10K2.t5136 (nat_lit 78774381) (nat_lit 5445491920) (nat_lit 0) A10K2.t5137 from rfl, allE_node, rows5136, irow5133, rows5137]
  all_goals rfl

theorem atot5133 : totK PA10K2 A10K2.u5133 = [0, 575328351731, 2550943962808, 3790617364405, 2271384197643, 509911183362, 27250992027, 0, 0, 0] := by
  rw [show A10K2.u5133 = KTree.node A10K2.t5136 (nat_lit 78774381) (nat_lit 5445491920) (nat_lit 0) A10K2.t5137 from rfl, totK_node, tot5136, tot5137]
  decide +kernel

theorem arows5134 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5134 = true := by
  rw [show A10K2.u5134 = KTree.node A10K2.t5138 (nat_lit 78780421) (nat_lit 6786139667) (nat_lit 0) A10K2.t5139 from rfl, allE_node, rows5138, irow5134, rows5139]
  all_goals rfl

theorem atot5134 : totK PA10K2 A10K2.u5134 = [0, 455111935113, 2098189300638, 3704003663964, 2597064085427, 519851032229, 30831673886, 0, 0, 0] := by
  rw [show A10K2.u5134 = KTree.node A10K2.t5138 (nat_lit 78780421) (nat_lit 6786139667) (nat_lit 0) A10K2.t5139 from rfl, totK_node, tot5138, tot5139]
  decide +kernel

theorem arows5136 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5136 = true := by
  rw [show A10K2.u5136 = KTree.node A10K2.t5140 (nat_lit 78786034) (nat_lit 14140600527) (nat_lit 0) A10K2.t5141 from rfl, allE_node, rows5140, irow5136, rows5141]
  all_goals rfl

theorem atot5136 : totK PA10K2 A10K2.u5136 = [0, 450165197568, 2431174976040, 4024656554209, 2229240977585, 392883240766, 25734533292, 0, 0, 0] := by
  rw [show A10K2.u5136 = KTree.node A10K2.t5140 (nat_lit 78786034) (nat_lit 14140600527) (nat_lit 0) A10K2.t5141 from rfl, totK_node, tot5140, tot5141]
  decide +kernel

theorem arows5137 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5137 = true := by
  rw [show A10K2.u5137 = KTree.node A10K2.t5142 (nat_lit 78791509) (nat_lit 6365417349) (nat_lit 0) A10K2.t5143 from rfl, allE_node, rows5142, irow5137, rows5143]
  all_goals rfl

theorem atot5137 : totK PA10K2 A10K2.u5137 = [0, 852343649289, 3071286417832, 3653427295598, 1711901637895, 234892762864, 6034215561, 0, 0, 0] := by
  rw [show A10K2.u5137 = KTree.node A10K2.t5142 (nat_lit 78791509) (nat_lit 6365417349) (nat_lit 0) A10K2.t5143 from rfl, totK_node, tot5142, tot5143]
  decide +kernel

theorem arows5140 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5140 = true := by
  rw [show A10K2.u5140 = KTree.node A10K2.t5144 (nat_lit 78797022) (nat_lit 5881700813) (nat_lit 0) A10K2.t5145 from rfl, allE_node, rows5144, irow5140, rows5145]
  all_goals rfl

theorem atot5140 : totK PA10K2 A10K2.u5140 = [0, 0, 1469229366035, 4222031602791, 3087807978628, 595171931421, 31987755669, 0, 0, 0] := by
  rw [show A10K2.u5140 = KTree.node A10K2.t5144 (nat_lit 78797022) (nat_lit 5881700813) (nat_lit 0) A10K2.t5145 from rfl, totK_node, tot5144, tot5145]
  decide +kernel

theorem arows5141 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5141 = true := by
  rw [show A10K2.u5141 = KTree.node A10K2.t5146 (nat_lit 78816557) (nat_lit 6572469376) (nat_lit 0) A10K2.t5147 from rfl, allE_node, rows5146, irow5141, rows5147]
  all_goals rfl

theorem atot5141 : totK PA10K2 A10K2.u5141 = [0, 0, 1031137485511, 3717700444305, 3794110855424, 915087584514, 45189801840, 0, 0, 0] := by
  rw [show A10K2.u5141 = KTree.node A10K2.t5146 (nat_lit 78816557) (nat_lit 6572469376) (nat_lit 0) A10K2.t5147 from rfl, totK_node, tot5146, tot5147]
  decide +kernel

theorem arows5143 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5143 = true := by
  rw [show A10K2.u5143 = KTree.node A10K2.t5148 (nat_lit 78824737) (nat_lit 8929195742) (nat_lit 0) A10K2.t5149 from rfl, allE_node, rows5148, irow5143, rows5149]
  all_goals rfl

theorem atot5143 : totK PA10K2 A10K2.u5143 = [0, 0, 924221318248, 3617322091964, 3886912660479, 972281874166, 63059542872, 0, 0, 0] := by
  rw [show A10K2.u5143 = KTree.node A10K2.t5148 (nat_lit 78824737) (nat_lit 8929195742) (nat_lit 0) A10K2.t5149 from rfl, totK_node, tot5148, tot5149]
  decide +kernel

theorem arows5144 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5144 = true := by
  rw [show A10K2.u5144 = KTree.node A10K2.t5150 (nat_lit 78830420) (nat_lit 12787305082) (nat_lit 0) A10K2.t5151 from rfl, allE_node, rows5150, irow5144, rows5151]
  all_goals rfl

theorem atot5144 : totK PA10K2 A10K2.u5144 = [0, 0, 578189715567, 2657080327452, 3926248706255, 1878923273183, 285103106428, 6354482628, 0, 0] := by
  rw [show A10K2.u5144 = KTree.node A10K2.t5150 (nat_lit 78830420) (nat_lit 12787305082) (nat_lit 0) A10K2.t5151 from rfl, totK_node, tot5150, tot5151]
  decide +kernel

theorem arows5149 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5149 = true := by
  rw [show A10K2.u5149 = KTree.node A10K2.t5152 (nat_lit 78909964) (nat_lit 10989989318) (nat_lit 0) A10K2.t5153 from rfl, allE_node, rows5152, irow5149, rows5153]
  all_goals rfl

theorem atot5149 : totK PA10K2 A10K2.u5149 = [0, 0, 331556073833, 2011544730977, 3994564355948, 2463409546445, 459912132344, 30388749007, 0, 0] := by
  rw [show A10K2.u5149 = KTree.node A10K2.t5152 (nat_lit 78909964) (nat_lit 10989989318) (nat_lit 0) A10K2.t5153 from rfl, totK_node, tot5152, tot5153]
  decide +kernel

theorem arows5150 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5150 = true := by
  rw [show A10K2.u5150 = KTree.node A10K2.t5154 (nat_lit 78923853) (nat_lit 5605626125) (nat_lit 0) A10K2.t5155 from rfl, allE_node, rows5154, irow5150, rows5155]
  all_goals rfl

theorem atot5150 : totK PA10K2 A10K2.u5150 = [0, 0, 666685636834, 3097293734312, 4100784453293, 1466560406130, 117542335794, 0, 0, 0] := by
  rw [show A10K2.u5150 = KTree.node A10K2.t5154 (nat_lit 78923853) (nat_lit 5605626125) (nat_lit 0) A10K2.t5155 from rfl, totK_node, tot5154, tot5155]
  decide +kernel

theorem arows5152 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5152 = true := by
  rw [show A10K2.u5152 = KTree.node A10K2.t5156 (nat_lit 78930728) (nat_lit 12251685841) (nat_lit 0) A10K2.t5157 from rfl, allE_node, rows5156, irow5152, rows5157]
  all_goals rfl

theorem atot5152 : totK PA10K2 A10K2.u5152 = [0, 0, 768953172235, 2969863530898, 3863466157171, 1743675237298, 260949997396, 6354482628, 0, 0] := by
  rw [show A10K2.u5152 = KTree.node A10K2.t5156 (nat_lit 78930728) (nat_lit 12251685841) (nat_lit 0) A10K2.t5157 from rfl, totK_node, tot5156, tot5157]
  decide +kernel

theorem arows5153 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5153 = true := by
  rw [show A10K2.u5153 = KTree.node A10K2.t5158 (nat_lit 78983058) (nat_lit 15204535253) (nat_lit 0) A10K2.t5159 from rfl, allE_node, rows5158, irow5153, rows5159]
  all_goals rfl

theorem atot5153 : totK PA10K2 A10K2.u5153 = [0, 0, 490584767793, 2463681217150, 4013961656536, 2098722654143, 343547761997, 25299471099, 0, 0] := by
  rw [show A10K2.u5153 = KTree.node A10K2.t5158 (nat_lit 78983058) (nat_lit 15204535253) (nat_lit 0) A10K2.t5159 from rfl, totK_node, tot5158, tot5159]
  decide +kernel

theorem arows5156 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5156 = true := by
  rw [show A10K2.u5156 = KTree.node A10K2.t5160 (nat_lit 78988729) (nat_lit 842855486) (nat_lit 0) A10K2.t5161 from rfl, allE_node, rows5160, irow5156, rows5161]
  all_goals rfl

theorem atot5156 : totK PA10K2 A10K2.u5156 = [0, 0, 779325947262, 3174463982277, 3797372778872, 1511718592505, 200627497169, 5718040558, 0, 0] := by
  rw [show A10K2.u5156 = KTree.node A10K2.t5160 (nat_lit 78988729) (nat_lit 842855486) (nat_lit 0) A10K2.t5161 from rfl, totK_node, tot5160, tot5161]
  decide +kernel

theorem arows5157 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5157 = true := by
  rw [show A10K2.u5157 = KTree.node A10K2.t5162 (nat_lit 78996665) (nat_lit 3375994727) (nat_lit 0) A10K2.t5163 from rfl, allE_node, rows5162, irow5157, rows5163]
  all_goals rfl

theorem atot5157 : totK PA10K2 A10K2.u5157 = [0, 0, 602706464918, 2646667187967, 4065594266957, 2023111385734, 280899590190, 6354482628, 0, 0] := by
  rw [show A10K2.u5157 = KTree.node A10K2.t5162 (nat_lit 78996665) (nat_lit 3375994727) (nat_lit 0) A10K2.t5163 from rfl, totK_node, tot5162, tot5163]
  decide +kernel

theorem arows5159 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5159 = true := by
  rw [show A10K2.u5159 = KTree.node A10K2.t5164 (nat_lit 79039341) (nat_lit 6354603908) (nat_lit 0) A10K2.t5165 from rfl, allE_node, rows5164, irow5159, rows5165]
  all_goals rfl

theorem atot5159 : totK PA10K2 A10K2.u5159 = [0, 0, 595126317713, 2751984551842, 3818354853176, 1729208056789, 326858143568, 24614390653, 0, 0] := by
  rw [show A10K2.u5159 = KTree.node A10K2.t5164 (nat_lit 79039341) (nat_lit 6354603908) (nat_lit 0) A10K2.t5165 from rfl, totK_node, tot5164, tot5165]
  decide +kernel

theorem arows5160 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5160 = true := by
  rw [show A10K2.u5160 = KTree.node A10K2.t5166 (nat_lit 79046437) (nat_lit 7311967796) (nat_lit 0) A10K2.t5167 from rfl, allE_node, rows5166, irow5160, rows5167]
  all_goals rfl

theorem atot5160 : totK PA10K2 A10K2.u5160 = [0, 0, 739600505509, 3005503851668, 3906835140095, 1579006700517, 187156128227, 5460492893, 0, 0] := by
  rw [show A10K2.u5160 = KTree.node A10K2.t5166 (nat_lit 79046437) (nat_lit 7311967796) (nat_lit 0) A10K2.t5167 from rfl, totK_node, tot5166, tot5167]
  decide +kernel

theorem arows5164 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5164 = true := by
  rw [show A10K2.u5164 = KTree.node A10K2.t5168 (nat_lit 79051924) (nat_lit 10531802714) (nat_lit 0) A10K2.t5169 from rfl, allE_node, rows5168, irow5164, rows5169]
  all_goals rfl

theorem atot5164 : totK PA10K2 A10K2.u5164 = [0, 0, 536528886358, 2332274509680, 3632272055652, 2226859111444, 484841637103, 31003444686, 0, 0] := by
  rw [show A10K2.u5164 = KTree.node A10K2.t5168 (nat_lit 79051924) (nat_lit 10531802714) (nat_lit 0) A10K2.t5169 from rfl, totK_node, tot5168, tot5169]
  decide +kernel

theorem arows5165 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5165 = true := by
  rw [show A10K2.u5165 = KTree.node A10K2.t5170 (nat_lit 79057192) (nat_lit 12309375425) (nat_lit 0) A10K2.t5171 from rfl, allE_node, rows5170, irow5165, rows5171]
  all_goals rfl

theorem atot5165 : totK PA10K2 A10K2.u5165 = [0, 0, 308068588377, 2258323512319, 4249770828888, 2218494408679, 306858562625, 6354482628, 0, 0] := by
  rw [show A10K2.u5165 = KTree.node A10K2.t5170 (nat_lit 79057192) (nat_lit 12309375425) (nat_lit 0) A10K2.t5171 from rfl, totK_node, tot5170, tot5171]
  decide +kernel

theorem arows5167 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5167 = true := by
  rw [show A10K2.u5167 = KTree.node A10K2.t5172 (nat_lit 79072033) (nat_lit 9477304812) (nat_lit 0) A10K2.t5173 from rfl, allE_node, rows5172, irow5167, rows5173]
  all_goals rfl

theorem atot5167 : totK PA10K2 A10K2.u5167 = [0, 0, 0, 1175246476829, 3840823921265, 3257212466158, 824759276177, 56529525987, 0, 0] := by
  rw [show A10K2.u5167 = KTree.node A10K2.t5172 (nat_lit 79072033) (nat_lit 9477304812) (nat_lit 0) A10K2.t5173 from rfl, totK_node, tot5172, tot5173]
  decide +kernel

theorem arows5168 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5168 = true := by
  rw [show A10K2.u5168 = KTree.node A10K2.t5174 (nat_lit 79086756) (nat_lit 13352547187) (nat_lit 0) A10K2.t5175 from rfl, allE_node, rows5174, irow5168, rows5175]
  all_goals rfl

theorem atot5168 : totK PA10K2 A10K2.u5168 = [0, 0, 0, 1035809211367, 3741129854225, 3459785932631, 861494428245, 56464005069, 0, 0] := by
  rw [show A10K2.u5168 = KTree.node A10K2.t5174 (nat_lit 79086756) (nat_lit 13352547187) (nat_lit 0) A10K2.t5175 from rfl, totK_node, tot5174, tot5175]
  decide +kernel

theorem arows5171 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5171 = true := by
  rw [show A10K2.u5171 = KTree.node A10K2.t5176 (nat_lit 79092480) (nat_lit 13116639826) (nat_lit 0) A10K2.t5177 from rfl, allE_node, rows5176, irow5171, rows5177]
  all_goals rfl

theorem atot5171 : totK PA10K2 A10K2.u5171 = [0, 583306429412, 1750750291517, 1574898593243, 1264334005090, 2360481836011, 1524081958218, 265614550179, 6354482628, 0] := by
  rw [show A10K2.u5171 = KTree.node A10K2.t5176 (nat_lit 79092480) (nat_lit 13116639826) (nat_lit 0) A10K2.t5177 from rfl, totK_node, tot5176, tot5177]
  decide +kernel

theorem arows5172 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5172 = true := by
  rw [show A10K2.u5172 = KTree.node A10K2.t5178 (nat_lit 83890284) (nat_lit 11030260021) (nat_lit 0) A10K2.t5179 from rfl, allE_node, rows5178, irow5172, rows5179]
  all_goals rfl

theorem atot5172 : totK PA10K2 A10K2.u5172 = [0, 286677691149, 2010305526618, 3987089681257, 2692422460738, 548122711584, 30831673886, 0, 0, 0] := by
  rw [show A10K2.u5172 = KTree.node A10K2.t5178 (nat_lit 83890284) (nat_lit 11030260021) (nat_lit 0) A10K2.t5179 from rfl, totK_node, tot5178, tot5179]
  decide +kernel

theorem arows5174 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5174 = true := by
  rw [show A10K2.u5174 = KTree.node A10K2.t5180 (nat_lit 83903764) (nat_lit 13095622804) (nat_lit 0) A10K2.t5181 from rfl, allE_node, rows5180, irow5174, rows5181]
  all_goals rfl

theorem atot5174 : totK PA10K2 A10K2.u5174 = [0, 727164550710, 3112411409675, 4024128616811, 1518580318982, 133838236052, 0, 0, 0, 0] := by
  rw [show A10K2.u5174 = KTree.node A10K2.t5180 (nat_lit 83903764) (nat_lit 13095622804) (nat_lit 0) A10K2.t5181 from rfl, totK_node, tot5180, tot5181]
  decide +kernel

theorem arows5175 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5175 = true := by
  rw [show A10K2.u5175 = KTree.node A10K2.t5182 (nat_lit 83910948) (nat_lit 13395856509) (nat_lit 0) A10K2.t5183 from rfl, allE_node, rows5182, irow5175, rows5183]
  all_goals rfl

theorem atot5175 : totK PA10K2 A10K2.u5175 = [0, 741544312551, 2872067787905, 3831217546199, 1867845064030, 273565330715, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u5175 = KTree.node A10K2.t5182 (nat_lit 83910948) (nat_lit 13395856509) (nat_lit 0) A10K2.t5183 from rfl, totK_node, tot5182, tot5183]
  decide +kernel

theorem arows5181 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5181 = true := by
  rw [show A10K2.u5181 = KTree.node A10K2.t5184 (nat_lit 83916210) (nat_lit 14081164750) (nat_lit 0) A10K2.t5185 from rfl, allE_node, rows5184, irow5181, rows5185]
  all_goals rfl

theorem atot5181 : totK PA10K2 A10K2.u5181 = [0, 0, 1261519040055, 3983313698300, 3634285488614, 939435219366, 48236066361, 0, 0, 0] := by
  rw [show A10K2.u5181 = KTree.node A10K2.t5184 (nat_lit 83916210) (nat_lit 14081164750) (nat_lit 0) A10K2.t5185 from rfl, totK_node, tot5184, tot5185]
  decide +kernel

theorem arows5182 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5182 = true := by
  rw [show A10K2.u5182 = KTree.node A10K2.t5186 (nat_lit 83921932) (nat_lit 10473693815) (nat_lit 0) A10K2.t5187 from rfl, allE_node, rows5186, irow5182, rows5187]
  all_goals rfl

theorem atot5182 : totK PA10K2 A10K2.u5182 = [0, 0, 709527520834, 3106509292321, 4040321329740, 1586576044630, 196661141535, 14945844243, 0, 0] := by
  rw [show A10K2.u5182 = KTree.node A10K2.t5186 (nat_lit 83921932) (nat_lit 10473693815) (nat_lit 0) A10K2.t5187 from rfl, totK_node, tot5186, tot5187]
  decide +kernel

theorem arows5184 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5184 = true := by
  rw [show A10K2.u5184 = KTree.node A10K2.t5188 (nat_lit 83935295) (nat_lit 13112235503) (nat_lit 0) A10K2.t5189 from rfl, allE_node, rows5188, irow5184, rows5189]
  all_goals rfl

theorem atot5184 : totK PA10K2 A10K2.u5184 = [0, 0, 616989536258, 2540686803929, 3681434575858, 2076889680730, 406006603093, 15704651987, 0, 0] := by
  rw [show A10K2.u5184 = KTree.node A10K2.t5188 (nat_lit 83935295) (nat_lit 13112235503) (nat_lit 0) A10K2.t5189 from rfl, totK_node, tot5188, tot5189]
  decide +kernel

theorem arows5185 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5185 = true := by
  rw [show A10K2.u5185 = KTree.node A10K2.t5190 (nat_lit 83941589) (nat_lit 6331008856) (nat_lit 0) A10K2.t5191 from rfl, allE_node, rows5190, irow5185, rows5191]
  all_goals rfl

theorem atot5185 : totK PA10K2 A10K2.u5185 = [0, 0, 546215072131, 2739631261409, 4075963509273, 1821932481263, 219178372242, 5546304973, 0, 0] := by
  rw [show A10K2.u5185 = KTree.node A10K2.t5190 (nat_lit 83941589) (nat_lit 6331008856) (nat_lit 0) A10K2.t5191 from rfl, totK_node, tot5190, tot5191]
  decide +kernel

theorem arows5188 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5188 = true := by
  rw [show A10K2.u5188 = KTree.node A10K2.t5192 (nat_lit 84017441) (nat_lit 9918507036) (nat_lit 0) A10K2.t5193 from rfl, allE_node, rows5192, irow5188, rows5193]
  all_goals rfl

theorem atot5188 : totK PA10K2 A10K2.u5188 = [0, 638550609260, 2503365527957, 3527547146763, 2308802066470, 684211778490, 42599296307, 0, 0, 0] := by
  rw [show A10K2.u5188 = KTree.node A10K2.t5192 (nat_lit 84017441) (nat_lit 9918507036) (nat_lit 0) A10K2.t5193 from rfl, totK_node, tot5192, tot5193]
  decide +kernel

theorem arows5189 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5189 = true := by
  rw [show A10K2.u5189 = KTree.node A10K2.t5194 (nat_lit 84022149) (nat_lit 5047026404) (nat_lit 0) A10K2.t5195 from rfl, allE_node, rows5194, irow5189, rows5195]
  all_goals rfl

theorem atot5189 : totK PA10K2 A10K2.u5189 = [0, 347846025083, 2046446612402, 3905990355601, 2807349503826, 586218807590, 30831673886, 0, 0, 0] := by
  rw [show A10K2.u5189 = KTree.node A10K2.t5194 (nat_lit 84022149) (nat_lit 5047026404) (nat_lit 0) A10K2.t5195 from rfl, totK_node, tot5194, tot5195]
  decide +kernel

theorem arows5191 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5191 = true := by
  rw [show A10K2.u5191 = KTree.node A10K2.t5196 (nat_lit 84031189) (nat_lit 6132576974) (nat_lit 0) A10K2.t5197 from rfl, allE_node, rows5196, irow5191, rows5197]
  all_goals rfl

theorem atot5191 : totK PA10K2 A10K2.u5191 = [0, 547186950112, 2443636866940, 3730299584176, 2212800038843, 477582333995, 31768748853, 0, 0, 0] := by
  rw [show A10K2.u5191 = KTree.node A10K2.t5196 (nat_lit 84031189) (nat_lit 6132576974) (nat_lit 0) A10K2.t5197 from rfl, totK_node, tot5196, tot5197]
  decide +kernel

theorem arows5192 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5192 = true := by
  rw [show A10K2.u5192 = KTree.node A10K2.t5198 (nat_lit 84035925) (nat_lit 6980450443) (nat_lit 0) A10K2.t5199 from rfl, allE_node, rows5198, irow5192, rows5199]
  all_goals rfl

theorem atot5192 : totK PA10K2 A10K2.u5192 = [0, 510219037452, 2691157745092, 4150590879355, 1788802921146, 160085866091, 0, 0, 0, 0] := by
  rw [show A10K2.u5192 = KTree.node A10K2.t5198 (nat_lit 84035925) (nat_lit 6980450443) (nat_lit 0) A10K2.t5199 from rfl, totK_node, tot5198, tot5199]
  decide +kernel

theorem arows5196 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5196 = true := by
  rw [show A10K2.u5196 = KTree.node A10K2.t5200 (nat_lit 84052003) (nat_lit 7997727697) (nat_lit 0) A10K2.t5201 from rfl, allE_node, rows5200, irow5196, rows5201]
  all_goals rfl

theorem atot5196 : totK PA10K2 A10K2.u5196 = [0, 0, 1012406483624, 3772531417664, 3862471913029, 975510142301, 45137667897, 0, 0, 0] := by
  rw [show A10K2.u5196 = KTree.node A10K2.t5200 (nat_lit 84052003) (nat_lit 7997727697) (nat_lit 0) A10K2.t5201 from rfl, totK_node, tot5200, tot5201]
  decide +kernel

theorem arows5197 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5197 = true := by
  rw [show A10K2.u5197 = KTree.node A10K2.t5202 (nat_lit 84066587) (nat_lit 9284220558) (nat_lit 0) A10K2.t5203 from rfl, allE_node, rows5202, irow5197, rows5203]
  all_goals rfl

theorem atot5197 : totK PA10K2 A10K2.u5197 = [0, 0, 985714074866, 3510726328277, 3694134048392, 1082976948032, 82738314188, 0, 0, 0] := by
  rw [show A10K2.u5197 = KTree.node A10K2.t5202 (nat_lit 84066587) (nat_lit 9284220558) (nat_lit 0) A10K2.t5203 from rfl, totK_node, tot5202, tot5203]
  decide +kernel

theorem arows5199 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5199 = true := by
  rw [show A10K2.u5199 = KTree.node A10K2.t5204 (nat_lit 84072517) (nat_lit 6202701764) (nat_lit 0) A10K2.t5205 from rfl, allE_node, rows5204, irow5199, rows5205]
  all_goals rfl

theorem atot5199 : totK PA10K2 A10K2.u5199 = [0, 310758541238, 1187749771823, 2534964694574, 3326889799832, 1687141778448, 265773289542, 6354482628, 0, 0] := by
  rw [show A10K2.u5199 = KTree.node A10K2.t5204 (nat_lit 84072517) (nat_lit 6202701764) (nat_lit 0) A10K2.t5205 from rfl, totK_node, tot5204, tot5205]
  decide +kernel

theorem arows5200 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5200 = true := by
  rw [show A10K2.u5200 = KTree.node A10K2.t5206 (nat_lit 84086660) (nat_lit 7781747672) (nat_lit 0) A10K2.t5207 from rfl, allE_node, rows5206, irow5200, rows5207]
  all_goals rfl

theorem atot5200 : totK PA10K2 A10K2.u5200 = [0, 498831047768, 2448342721106, 4032134343546, 2352116064553, 443104310655, 25351274858, 0, 0, 0] := by
  rw [show A10K2.u5200 = KTree.node A10K2.t5206 (nat_lit 84086660) (nat_lit 7781747672) (nat_lit 0) A10K2.t5207 from rfl, totK_node, tot5206, tot5207]
  decide +kernel

theorem arows5203 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5203 = true := by
  rw [show A10K2.u5203 = KTree.node A10K2.t5208 (nat_lit 84094930) (nat_lit 14872883413) (nat_lit 0) A10K2.t5209 from rfl, allE_node, rows5208, irow5203, rows5209]
  all_goals rfl

theorem atot5203 : totK PA10K2 A10K2.u5203 = [0, 649757058177, 2885886871598, 4158210812903, 2145043799031, 295795914696, 5459593153, 0, 0, 0] := by
  rw [show A10K2.u5203 = KTree.node A10K2.t5208 (nat_lit 84094930) (nat_lit 14872883413) (nat_lit 0) A10K2.t5209 from rfl, totK_node, tot5208, tot5209]
  decide +kernel

theorem arows5204 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5204 = true := by
  rw [show A10K2.u5204 = KTree.node A10K2.t5210 (nat_lit 84111369) (nat_lit 9788426220) (nat_lit 0) A10K2.t5211 from rfl, allE_node, rows5210, irow5204, rows5211]
  all_goals rfl

theorem atot5204 : totK PA10K2 A10K2.u5204 = [0, 414718020177, 2291840602892, 4135064106908, 2758778374883, 522749740575, 13816090359, 0, 0, 0] := by
  rw [show A10K2.u5204 = KTree.node A10K2.t5210 (nat_lit 84111369) (nat_lit 9788426220) (nat_lit 0) A10K2.t5211 from rfl, totK_node, tot5210, tot5211]
  decide +kernel

theorem arows5206 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5206 = true := by
  rw [show A10K2.u5206 = KTree.node A10K2.t5212 (nat_lit 84116072) (nat_lit 12020478838) (nat_lit 0) A10K2.t5213 from rfl, allE_node, rows5212, irow5206, rows5213]
  all_goals rfl

theorem atot5206 : totK PA10K2 A10K2.u5206 = [0, 0, 974144729453, 3603085961780, 3931506526820, 1246228483233, 87056475289, 0, 0, 0] := by
  rw [show A10K2.u5206 = KTree.node A10K2.t5212 (nat_lit 84116072) (nat_lit 12020478838) (nat_lit 0) A10K2.t5213 from rfl, totK_node, tot5212, tot5213]
  decide +kernel

theorem arows5207 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5207 = true := by
  rw [show A10K2.u5207 = KTree.node A10K2.t5214 (nat_lit 84122678) (nat_lit 16407917004) (nat_lit 0) A10K2.t5215 from rfl, allE_node, rows5214, irow5207, rows5215]
  all_goals rfl

theorem atot5207 : totK PA10K2 A10K2.u5207 = [0, 0, 279805444759, 2125923232811, 4394288732147, 2719596280275, 370267401058, 6904928264, 0, 0] := by
  rw [show A10K2.u5207 = KTree.node A10K2.t5214 (nat_lit 84122678) (nat_lit 16407917004) (nat_lit 0) A10K2.t5215 from rfl, totK_node, tot5214, tot5215]
  decide +kernel

theorem arows5212 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5212 = true := by
  rw [show A10K2.u5212 = KTree.node A10K2.t5216 (nat_lit 84141759) (nat_lit 12309121275) (nat_lit 0) A10K2.t5217 from rfl, allE_node, rows5216, irow5212, rows5217]
  all_goals rfl

theorem atot5212 : totK PA10K2 A10K2.u5212 = [0, 0, 797445464131, 3269887160802, 4151628465739, 1650082522673, 128523468031, 0, 0, 0] := by
  rw [show A10K2.u5212 = KTree.node A10K2.t5216 (nat_lit 84141759) (nat_lit 12309121275) (nat_lit 0) A10K2.t5217 from rfl, totK_node, tot5216, tot5217]
  decide +kernel

theorem arows5213 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5213 = true := by
  rw [show A10K2.u5213 = KTree.node A10K2.t5218 (nat_lit 84147761) (nat_lit 9165662610) (nat_lit 0) A10K2.t5219 from rfl, allE_node, rows5218, irow5213, rows5219]
  all_goals rfl

theorem atot5213 : totK PA10K2 A10K2.u5213 = [0, 0, 427178422353, 1965905650169, 3751856527264, 3076567587315, 764750206813, 39854233058, 0, 0] := by
  rw [show A10K2.u5213 = KTree.node A10K2.t5218 (nat_lit 84147761) (nat_lit 9165662610) (nat_lit 0) A10K2.t5219 from rfl, totK_node, tot5218, tot5219]
  decide +kernel

theorem arows5215 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5215 = true := by
  rw [show A10K2.u5215 = KTree.node A10K2.t5220 (nat_lit 84152268) (nat_lit 4094155744) (nat_lit 0) A10K2.t5221 from rfl, allE_node, rows5220, irow5215, rows5221]
  all_goals rfl

theorem atot5215 : totK PA10K2 A10K2.u5215 = [0, 0, 440261672059, 2338567907954, 3961459711506, 2281584914031, 427899423154, 25371180993, 0, 0] := by
  rw [show A10K2.u5215 = KTree.node A10K2.t5220 (nat_lit 84152268) (nat_lit 4094155744) (nat_lit 0) A10K2.t5221 from rfl, totK_node, tot5220, tot5221]
  decide +kernel

theorem arows5216 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5216 = true := by
  rw [show A10K2.u5216 = KTree.node A10K2.t5222 (nat_lit 84165482) (nat_lit 5533576650) (nat_lit 0) A10K2.t5223 from rfl, allE_node, rows5222, irow5216, rows5223]
  all_goals rfl

theorem atot5216 : totK PA10K2 A10K2.u5216 = [0, 0, 726491931495, 3032834849545, 3861346959506, 1595964448946, 211606067750, 5460492893, 0, 0] := by
  rw [show A10K2.u5216 = KTree.node A10K2.t5222 (nat_lit 84165482) (nat_lit 5533576650) (nat_lit 0) A10K2.t5223 from rfl, totK_node, tot5222, tot5223]
  decide +kernel

theorem arows5219 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5219 = true := by
  rw [show A10K2.u5219 = KTree.node A10K2.t5224 (nat_lit 84172896) (nat_lit 13865624482) (nat_lit 0) A10K2.t5225 from rfl, allE_node, rows5224, irow5219, rows5225]
  all_goals rfl

theorem atot5219 : totK PA10K2 A10K2.u5219 = [0, 0, 694831718653, 2814493485594, 3926454079949, 1838082494795, 210299938772, 5705019915, 0, 0] := by
  rw [show A10K2.u5219 = KTree.node A10K2.t5224 (nat_lit 84172896) (nat_lit 13865624482) (nat_lit 0) A10K2.t5225 from rfl, totK_node, tot5224, tot5225]
  decide +kernel

theorem arows5220 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5220 = true := by
  rw [show A10K2.u5220 = KTree.node A10K2.t5226 (nat_lit 84178162) (nat_lit 12186885809) (nat_lit 0) A10K2.t5227 from rfl, allE_node, rows5226, irow5220, rows5227]
  all_goals rfl

theorem atot5220 : totK PA10K2 A10K2.u5220 = [0, 0, 45768258037, 1564462228595, 4292966774971, 3271009066715, 663465334456, 35031173917, 0, 0] := by
  rw [show A10K2.u5220 = KTree.node A10K2.t5226 (nat_lit 84178162) (nat_lit 12186885809) (nat_lit 0) A10K2.t5227 from rfl, totK_node, tot5226, tot5227]
  decide +kernel

theorem arows5222 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5222 = true := by
  rw [show A10K2.u5222 = KTree.node A10K2.t5228 (nat_lit 84184449) (nat_lit 10144077097) (nat_lit 0) A10K2.t5229 from rfl, allE_node, rows5228, irow5222, rows5229]
  all_goals rfl

theorem atot5222 : totK PA10K2 A10K2.u5222 = [0, 0, 0, 541477851680, 2661406925790, 3891352135794, 1928162622956, 389574588130, 25239774317, 0] := by
  rw [show A10K2.u5222 = KTree.node A10K2.t5228 (nat_lit 84184449) (nat_lit 10144077097) (nat_lit 0) A10K2.t5229 from rfl, totK_node, tot5228, tot5229]
  decide +kernel

theorem arows5223 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5223 = true := by
  rw [show A10K2.u5223 = KTree.node A10K2.t5230 (nat_lit 84197816) (nat_lit 14365455101) (nat_lit 0) A10K2.t5231 from rfl, allE_node, rows5230, irow5223, rows5231]
  all_goals rfl

theorem atot5223 : totK PA10K2 A10K2.u5223 = [0, 0, 0, 719111798190, 2934353047219, 3694840111494, 1594676443604, 217039146458, 5365973533, 0] := by
  rw [show A10K2.u5223 = KTree.node A10K2.t5230 (nat_lit 84197816) (nat_lit 14365455101) (nat_lit 0) A10K2.t5231 from rfl, totK_node, tot5230, tot5231]
  decide +kernel

theorem arows5227 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5227 = true := by
  rw [show A10K2.u5227 = KTree.node A10K2.t5232 (nat_lit 84204297) (nat_lit 8159784399) (nat_lit 0) A10K2.t5233 from rfl, allE_node, rows5232, irow5227, rows5233]
  all_goals rfl

theorem atot5227 : totK PA10K2 A10K2.u5227 = [0, 0, 0, 719901543799, 2899622410186, 3867000915640, 1636108069235, 211677635039, 5528811039, 0] := by
  rw [show A10K2.u5227 = KTree.node A10K2.t5232 (nat_lit 84204297) (nat_lit 8159784399) (nat_lit 0) A10K2.t5233 from rfl, totK_node, tot5232, tot5233]
  decide +kernel

theorem arows5228 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5228 = true := by
  rw [show A10K2.u5228 = KTree.node A10K2.t5234 (nat_lit 84281399) (nat_lit 12189652935) (nat_lit 0) A10K2.t5235 from rfl, allE_node, rows5234, irow5228, rows5235]
  all_goals rfl

theorem atot5228 : totK PA10K2 A10K2.u5228 = [0, 0, 797092040211, 3033829567451, 3763569955223, 1837793035306, 395163365355, 29010686974, 0, 0] := by
  rw [show A10K2.u5228 = KTree.node A10K2.t5234 (nat_lit 84281399) (nat_lit 12189652935) (nat_lit 0) A10K2.t5235 from rfl, totK_node, tot5234, tot5235]
  decide +kernel

theorem arows5230 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5230 = true := by
  rw [show A10K2.u5230 = KTree.node A10K2.t5236 (nat_lit 84286276) (nat_lit 12221605977) (nat_lit 0) A10K2.t5237 from rfl, allE_node, rows5236, irow5230, rows5237]
  all_goals rfl

theorem atot5230 : totK PA10K2 A10K2.u5230 = [0, 0, 469339957255, 2138415629547, 3682519903883, 2606078061832, 561326509195, 30831673886, 0, 0] := by
  rw [show A10K2.u5230 = KTree.node A10K2.t5236 (nat_lit 84286276) (nat_lit 12221605977) (nat_lit 0) A10K2.t5237 from rfl, totK_node, tot5236, tot5237]
  decide +kernel

theorem arows5231 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5231 = true := by
  rw [show A10K2.u5231 = KTree.node A10K2.t5238 (nat_lit 84295776) (nat_lit 13847045638) (nat_lit 0) A10K2.t5239 from rfl, allE_node, rows5238, irow5231, rows5239]
  all_goals rfl

theorem atot5231 : totK PA10K2 A10K2.u5231 = [0, 0, 580318148999, 2607799586645, 3961376633554, 1932144277570, 252760694279, 6034215561, 0, 0] := by
  rw [show A10K2.u5231 = KTree.node A10K2.t5238 (nat_lit 84295776) (nat_lit 13847045638) (nat_lit 0) A10K2.t5239 from rfl, totK_node, tot5238, tot5239]
  decide +kernel

theorem arows5234 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5234 = true := by
  rw [show A10K2.u5234 = KTree.node A10K2.t5240 (nat_lit 84301121) (nat_lit 9066129373) (nat_lit 0) A10K2.t5241 from rfl, allE_node, rows5240, irow5234, rows5241]
  all_goals rfl

theorem atot5234 : totK PA10K2 A10K2.u5234 = [0, 0, 208565205755, 2036770971442, 4249480105907, 2489466224117, 340255407168, 6354482628, 0, 0] := by
  rw [show A10K2.u5234 = KTree.node A10K2.t5240 (nat_lit 84301121) (nat_lit 9066129373) (nat_lit 0) A10K2.t5241 from rfl, totK_node, tot5240, tot5241]
  decide +kernel

theorem arows5235 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5235 = true := by
  rw [show A10K2.u5235 = KTree.node A10K2.t5242 (nat_lit 84315661) (nat_lit 5411169083) (nat_lit 0) A10K2.t5243 from rfl, allE_node, rows5242, irow5235, rows5243]
  all_goals rfl

theorem atot5235 : totK PA10K2 A10K2.u5235 = [0, 0, 0, 1095789296404, 3799670636146, 3605510104873, 887020792530, 44791175865, 0, 0] := by
  rw [show A10K2.u5235 = KTree.node A10K2.t5242 (nat_lit 84315661) (nat_lit 5411169083) (nat_lit 0) A10K2.t5243 from rfl, totK_node, tot5242, tot5243]
  decide +kernel

theorem arows5237 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5237 = true := by
  rw [show A10K2.u5237 = KTree.node A10K2.t5244 (nat_lit 84330728) (nat_lit 7385295154) (nat_lit 0) A10K2.t5245 from rfl, allE_node, rows5244, irow5237, rows5245]
  all_goals rfl

theorem atot5237 : totK PA10K2 A10K2.u5237 = [0, 0, 0, 623817838288, 3152818519201, 4036888657901, 1301297400984, 94283252747, 0, 0] := by
  rw [show A10K2.u5237 = KTree.node A10K2.t5244 (nat_lit 84330728) (nat_lit 7385295154) (nat_lit 0) A10K2.t5245 from rfl, totK_node, tot5244, tot5245]
  decide +kernel

theorem arows5238 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5238 = true := by
  rw [show A10K2.u5238 = KTree.node A10K2.t5246 (nat_lit 84346989) (nat_lit 5483478668) (nat_lit 0) A10K2.t5247 from rfl, allE_node, rows5246, irow5238, rows5247]
  all_goals rfl

theorem atot5238 : totK PA10K2 A10K2.u5238 = [0, 0, 806416526819, 3061201070336, 3480606572104, 1588341986720, 615363456027, 128644302662, 5676195732, 0] := by
  rw [show A10K2.u5238 = KTree.node A10K2.t5246 (nat_lit 84346989) (nat_lit 5483478668) (nat_lit 0) A10K2.t5247 from rfl, totK_node, tot5246, tot5247]
  decide +kernel

theorem arows5245 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5245 = true := by
  rw [show A10K2.u5245 = KTree.node A10K2.t5248 (nat_lit 84352455) (nat_lit 14467255561) (nat_lit 0) A10K2.t5249 from rfl, allE_node, rows5248, irow5245, rows5249]
  all_goals rfl

theorem atot5245 : totK PA10K2 A10K2.u5245 = [0, 0, 338743555992, 2081993497862, 4217399439605, 2813529829472, 508816572665, 25313348169, 0, 0] := by
  rw [show A10K2.u5245 = KTree.node A10K2.t5248 (nat_lit 84352455) (nat_lit 14467255561) (nat_lit 0) A10K2.t5249 from rfl, totK_node, tot5248, tot5249]
  decide +kernel

theorem arows5246 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5246 = true := by
  rw [show A10K2.u5246 = KTree.node A10K2.t5250 (nat_lit 84372628) (nat_lit 5664983912) (nat_lit 0) A10K2.t5251 from rfl, allE_node, rows5250, irow5246, rows5251]
  all_goals rfl

theorem atot5246 : totK PA10K2 A10K2.u5246 = [0, 0, 739000411306, 3135631564917, 4158198308726, 1799999921438, 240272929202, 6853348008, 0, 0] := by
  rw [show A10K2.u5246 = KTree.node A10K2.t5250 (nat_lit 84372628) (nat_lit 5664983912) (nat_lit 0) A10K2.t5251 from rfl, totK_node, tot5250, tot5251]
  decide +kernel

theorem arows5248 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5248 = true := by
  rw [show A10K2.u5248 = KTree.node A10K2.t5252 (nat_lit 84934714) (nat_lit 8598336631) (nat_lit 0) A10K2.t5253 from rfl, allE_node, rows5252, irow5248, rows5253]
  all_goals rfl

theorem atot5248 : totK PA10K2 A10K2.u5248 = [0, 583967476257, 2059331499421, 2502081207301, 2314831374943, 1915242353824, 505785816206, 29687484142, 0, 0] := by
  rw [show A10K2.u5248 = KTree.node A10K2.t5252 (nat_lit 84934714) (nat_lit 8598336631) (nat_lit 0) A10K2.t5253 from rfl, totK_node, tot5252, tot5253]
  decide +kernel

theorem arows5249 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5249 = true := by
  rw [show A10K2.u5249 = KTree.node A10K2.t5254 (nat_lit 84939262) (nat_lit 15046685384) (nat_lit 0) A10K2.t5255 from rfl, allE_node, rows5254, irow5249, rows5255]
  all_goals rfl

theorem atot5249 : totK PA10K2 A10K2.u5249 = [0, 249468953483, 1798038286482, 3987511655967, 2837794665535, 564331252196, 30831673886, 0, 0, 0] := by
  rw [show A10K2.u5249 = KTree.node A10K2.t5254 (nat_lit 84939262) (nat_lit 15046685384) (nat_lit 0) A10K2.t5255 from rfl, totK_node, tot5254, tot5255]
  decide +kernel

theorem arows5252 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5252 = true := by
  rw [show A10K2.u5252 = KTree.node A10K2.t5256 (nat_lit 84952872) (nat_lit 9838449782) (nat_lit 0) A10K2.t5257 from rfl, allE_node, rows5256, irow5252, rows5257]
  all_goals rfl

theorem atot5252 : totK PA10K2 A10K2.u5252 = [0, 770023963405, 3169497114221, 3987018396095, 1524519977934, 135485898880, 0, 0, 0, 0] := by
  rw [show A10K2.u5252 = KTree.node A10K2.t5256 (nat_lit 84952872) (nat_lit 9838449782) (nat_lit 0) A10K2.t5257 from rfl, totK_node, tot5256, tot5257]
  decide +kernel

theorem arows5253 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5253 = true := by
  rw [show A10K2.u5253 = KTree.node A10K2.t5258 (nat_lit 84959752) (nat_lit 14437532646) (nat_lit 0) A10K2.t5259 from rfl, allE_node, rows5258, irow5253, rows5259]
  all_goals rfl

theorem atot5253 : totK PA10K2 A10K2.u5253 = [0, 552312781151, 2605046733148, 4073185236191, 2147879983282, 302928572156, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u5253 = KTree.node A10K2.t5258 (nat_lit 84959752) (nat_lit 14437532646) (nat_lit 0) A10K2.t5259 from rfl, totK_node, tot5258, tot5259]
  decide +kernel

theorem arows5255 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5255 = true := by
  rw [show A10K2.u5255 = KTree.node A10K2.t5260 (nat_lit 84967493) (nat_lit 6104404467) (nat_lit 0) A10K2.t5261 from rfl, allE_node, rows5260, irow5255, rows5261]
  all_goals rfl

theorem atot5255 : totK PA10K2 A10K2.u5255 = [0, 0, 944004447338, 3642048103186, 3950052365537, 1107136520876, 68300575967, 0, 0, 0] := by
  rw [show A10K2.u5255 = KTree.node A10K2.t5260 (nat_lit 84967493) (nat_lit 6104404467) (nat_lit 0) A10K2.t5261 from rfl, totK_node, tot5260, tot5261]
  decide +kernel

theorem arows5256 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5256 = true := by
  rw [show A10K2.u5256 = KTree.node A10K2.t5262 (nat_lit 84972094) (nat_lit 13444513979) (nat_lit 0) A10K2.t5263 from rfl, allE_node, rows5262, irow5256, rows5263]
  all_goals rfl

theorem atot5256 : totK PA10K2 A10K2.u5256 = [0, 0, 346250128679, 1870920641893, 3878091690743, 2685105113858, 555358256481, 30650496230, 0, 0] := by
  rw [show A10K2.u5256 = KTree.node A10K2.t5262 (nat_lit 84972094) (nat_lit 13444513979) (nat_lit 0) A10K2.t5263 from rfl, totK_node, tot5262, tot5263]
  decide +kernel

theorem arows5260 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5260 = true := by
  rw [show A10K2.u5260 = KTree.node A10K2.t5264 (nat_lit 84985969) (nat_lit 8027272226) (nat_lit 0) A10K2.t5265 from rfl, allE_node, rows5264, irow5260, rows5265]
  all_goals rfl

theorem atot5260 : totK PA10K2 A10K2.u5260 = [0, 0, 671280046886, 3214855716064, 4178416466220, 1375219320744, 91432550180, 0, 0, 0] := by
  rw [show A10K2.u5260 = KTree.node A10K2.t5264 (nat_lit 84985969) (nat_lit 8027272226) (nat_lit 0) A10K2.t5265 from rfl, totK_node, tot5264, tot5265]
  decide +kernel

theorem arows5261 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5261 = true := by
  rw [show A10K2.u5261 = KTree.node A10K2.t5266 (nat_lit 84995120) (nat_lit 14797286462) (nat_lit 0) A10K2.t5267 from rfl, allE_node, rows5266, irow5261, rows5267]
  all_goals rfl

theorem atot5261 : totK PA10K2 A10K2.u5261 = [0, 303055287478, 1490583246461, 3018431230667, 3225781955868, 1451405288532, 196288192697, 5546304973, 0, 0] := by
  rw [show A10K2.u5261 = KTree.node A10K2.t5266 (nat_lit 84995120) (nat_lit 14797286462) (nat_lit 0) A10K2.t5267 from rfl, totK_node, tot5266, tot5267]
  decide +kernel

theorem arows5263 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5263 = true := by
  rw [show A10K2.u5263 = KTree.node A10K2.t5268 (nat_lit 85012411) (nat_lit 6755606656) (nat_lit 0) A10K2.t5269 from rfl, allE_node, rows5268, irow5263, rows5269]
  all_goals rfl

theorem atot5263 : totK PA10K2 A10K2.u5263 = [0, 459928825582, 2416863699566, 4110670484325, 2328809191967, 381577391181, 25734533292, 0, 0, 0] := by
  rw [show A10K2.u5263 = KTree.node A10K2.t5268 (nat_lit 85012411) (nat_lit 6755606656) (nat_lit 0) A10K2.t5269 from rfl, totK_node, tot5268, tot5269]
  decide +kernel

theorem arows5264 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5264 = true := by
  rw [show A10K2.u5264 = KTree.node A10K2.t5270 (nat_lit 85018066) (nat_lit 15419639998) (nat_lit 0) A10K2.t5271 from rfl, allE_node, rows5270, irow5264, rows5271]
  all_goals rfl

theorem atot5264 : totK PA10K2 A10K2.u5264 = [0, 779393338859, 3183509939707, 3928293155823, 1577983278813, 203728595326, 6034215561, 0, 0, 0] := by
  rw [show A10K2.u5264 = KTree.node A10K2.t5270 (nat_lit 85018066) (nat_lit 15419639998) (nat_lit 0) A10K2.t5271 from rfl, totK_node, tot5270, tot5271]
  decide +kernel

theorem arows5267 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5267 = true := by
  rw [show A10K2.u5267 = KTree.node A10K2.t5272 (nat_lit 85042397) (nat_lit 5690802550) (nat_lit 0) A10K2.t5273 from rfl, allE_node, rows5272, irow5267, rows5273]
  all_goals rfl

theorem atot5267 : totK PA10K2 A10K2.u5267 = [0, 0, 1181826616472, 4039448395617, 3510342506745, 746651430439, 32833578888, 0, 0, 0] := by
  rw [show A10K2.u5267 = KTree.node A10K2.t5272 (nat_lit 85042397) (nat_lit 5690802550) (nat_lit 0) A10K2.t5273 from rfl, totK_node, tot5272, tot5273]
  decide +kernel

theorem arows5268 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5268 = true := by
  rw [show A10K2.u5268 = KTree.node A10K2.t5274 (nat_lit 85047336) (nat_lit 10091082827) (nat_lit 0) A10K2.t5275 from rfl, allE_node, rows5274, irow5268, rows5275]
  all_goals rfl

theorem atot5268 : totK PA10K2 A10K2.u5268 = [0, 0, 435460319369, 2225795280418, 3980436038889, 2496480940192, 474748100007, 31082886609, 0, 0] := by
  rw [show A10K2.u5268 = KTree.node A10K2.t5274 (nat_lit 85047336) (nat_lit 10091082827) (nat_lit 0) A10K2.t5275 from rfl, totK_node, tot5274, tot5275]
  decide +kernel

theorem arows5270 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5270 = true := by
  rw [show A10K2.u5270 = KTree.node A10K2.t5276 (nat_lit 85052161) (nat_lit 9733914940) (nat_lit 0) A10K2.t5277 from rfl, allE_node, rows5276, irow5270, rows5277]
  all_goals rfl

theorem atot5270 : totK PA10K2 A10K2.u5270 = [0, 0, 532658819189, 2813711752762, 4253652205041, 1717027516022, 136441762503, 0, 0, 0] := by
  rw [show A10K2.u5270 = KTree.node A10K2.t5276 (nat_lit 85052161) (nat_lit 9733914940) (nat_lit 0) A10K2.t5277 from rfl, totK_node, tot5276, tot5277]
  decide +kernel

theorem arows5271 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5271 = true := by
  rw [show A10K2.u5271 = KTree.node A10K2.t5278 (nat_lit 85068066) (nat_lit 11977706767) (nat_lit 0) A10K2.t5279 from rfl, allE_node, rows5278, irow5271, rows5279]
  all_goals rfl

theorem atot5271 : totK PA10K2 A10K2.u5271 = [0, 762214156616, 3070515681374, 3750261902299, 1478182270056, 412038622477, 109444031198, 6121173289, 0, 0] := by
  rw [show A10K2.u5271 = KTree.node A10K2.t5278 (nat_lit 85068066) (nat_lit 11977706767) (nat_lit 0) A10K2.t5279 from rfl, totK_node, tot5278, tot5279]
  decide +kernel

theorem arows5276 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5276 = true := by
  rw [show A10K2.u5276 = KTree.node A10K2.t5280 (nat_lit 85075093) (nat_lit 6681160818) (nat_lit 0) A10K2.t5281 from rfl, allE_node, rows5280, irow5276, rows5281]
  all_goals rfl

theorem atot5276 : totK PA10K2 A10K2.u5276 = [0, 559530676988, 2421180108632, 3650964187358, 2335323045010, 534208274178, 30831673886, 0, 0, 0] := by
  rw [show A10K2.u5276 = KTree.node A10K2.t5280 (nat_lit 85075093) (nat_lit 6681160818) (nat_lit 0) A10K2.t5281 from rfl, totK_node, tot5280, tot5281]
  decide +kernel

theorem arows5277 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5277 = true := by
  rw [show A10K2.u5277 = KTree.node A10K2.t5282 (nat_lit 85080278) (nat_lit 12805364263) (nat_lit 0) A10K2.t5283 from rfl, allE_node, rows5282, irow5277, rows5283]
  all_goals rfl

theorem atot5277 : totK PA10K2 A10K2.u5277 = [0, 367746460093, 2014850614405, 3864463369314, 2703957586195, 559232175284, 31768748853, 0, 0, 0] := by
  rw [show A10K2.u5277 = KTree.node A10K2.t5282 (nat_lit 85080278) (nat_lit 12805364263) (nat_lit 0) A10K2.t5283 from rfl, totK_node, tot5282, tot5283]
  decide +kernel

theorem arows5279 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5279 = true := by
  rw [show A10K2.u5279 = KTree.node A10K2.t5284 (nat_lit 85084827) (nat_lit 9934556558) (nat_lit 0) A10K2.t5285 from rfl, allE_node, rows5284, irow5279, rows5285]
  all_goals rfl

theorem atot5279 : totK PA10K2 A10K2.u5279 = [0, 564595576905, 2882977490311, 4173112337525, 1712960035402, 140464755192, 0, 0, 0, 0] := by
  rw [show A10K2.u5279 = KTree.node A10K2.t5284 (nat_lit 85084827) (nat_lit 9934556558) (nat_lit 0) A10K2.t5285 from rfl, totK_node, tot5284, tot5285]
  decide +kernel

theorem arows5280 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5280 = true := by
  rw [show A10K2.u5280 = KTree.node A10K2.t5286 (nat_lit 85100644) (nat_lit 13462219180) (nat_lit 0) A10K2.t5287 from rfl, allE_node, rows5286, irow5280, rows5287]
  all_goals rfl

theorem atot5280 : totK PA10K2 A10K2.u5280 = [0, 0, 1010955968956, 3794151435384, 3783031521460, 963761871099, 45137667897, 0, 0, 0] := by
  rw [show A10K2.u5280 = KTree.node A10K2.t5286 (nat_lit 85100644) (nat_lit 13462219180) (nat_lit 0) A10K2.t5287 from rfl, totK_node, tot5286, tot5287]
  decide +kernel

theorem arows5283 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5283 = true := by
  rw [show A10K2.u5283 = KTree.node A10K2.t5288 (nat_lit 85110420) (nat_lit 10608721493) (nat_lit 0) A10K2.t5289 from rfl, allE_node, rows5288, irow5283, rows5289]
  all_goals rfl

theorem atot5283 : totK PA10K2 A10K2.u5283 = [0, 0, 968946541408, 3606298463841, 3854406786522, 1018191582618, 64078106957, 0, 0, 0] := by
  rw [show A10K2.u5283 = KTree.node A10K2.t5288 (nat_lit 85110420) (nat_lit 10608721493) (nat_lit 0) A10K2.t5289 from rfl, totK_node, tot5288, tot5289]
  decide +kernel

theorem arows5284 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5284 = true := by
  rw [show A10K2.u5284 = KTree.node A10K2.t5290 (nat_lit 85119408) (nat_lit 13791983513) (nat_lit 0) A10K2.t5291 from rfl, allE_node, rows5290, irow5284, rows5291]
  all_goals rfl

theorem atot5284 : totK PA10K2 A10K2.u5284 = [0, 0, 519839083284, 2545017628180, 4000668233086, 1948994729771, 291306829918, 6354482628, 0, 0] := by
  rw [show A10K2.u5284 = KTree.node A10K2.t5290 (nat_lit 85119408) (nat_lit 13791983513) (nat_lit 0) A10K2.t5291 from rfl, totK_node, tot5290, tot5291]
  decide +kernel

theorem arows5286 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5286 = true := by
  rw [show A10K2.u5286 = KTree.node A10K2.t5292 (nat_lit 85199921) (nat_lit 9866223381) (nat_lit 0) A10K2.t5293 from rfl, allE_node, rows5292, irow5286, rows5293]
  all_goals rfl

theorem atot5286 : totK PA10K2 A10K2.u5286 = [0, 0, 620064690152, 2869422894022, 4017650549702, 1760497362667, 272482825576, 20070762815, 0, 0] := by
  rw [show A10K2.u5286 = KTree.node A10K2.t5292 (nat_lit 85199921) (nat_lit 9866223381) (nat_lit 0) A10K2.t5293 from rfl, totK_node, tot5292, tot5293]
  decide +kernel

theorem arows5287 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5287 = true := by
  rw [show A10K2.u5287 = KTree.node A10K2.t5294 (nat_lit 85213262) (nat_lit 10745604468) (nat_lit 0) A10K2.t5295 from rfl, allE_node, rows5294, irow5287, rows5295]
  all_goals rfl

theorem atot5287 : totK PA10K2 A10K2.u5287 = [0, 0, 577927606974, 2472314842211, 3791316228142, 2238104207632, 374702400735, 10747604052, 0, 0] := by
  rw [show A10K2.u5287 = KTree.node A10K2.t5294 (nat_lit 85213262) (nat_lit 10745604468) (nat_lit 0) A10K2.t5295 from rfl, totK_node, tot5294, tot5295]
  decide +kernel

theorem arows5291 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5291 = true := by
  rw [show A10K2.u5291 = KTree.node A10K2.t5296 (nat_lit 85219360) (nat_lit 13682504314) (nat_lit 0) A10K2.t5297 from rfl, allE_node, rows5296, irow5291, rows5297]
  all_goals rfl

theorem atot5291 : totK PA10K2 A10K2.u5291 = [0, 0, 485445559963, 2553278429576, 4074119672914, 2066272843863, 294708344159, 6354482628, 0, 0] := by
  rw [show A10K2.u5291 = KTree.node A10K2.t5296 (nat_lit 85219360) (nat_lit 13682504314) (nat_lit 0) A10K2.t5297 from rfl, totK_node, tot5296, tot5297]
  decide +kernel

theorem arows5292 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5292 = true := by
  rw [show A10K2.u5292 = KTree.node A10K2.t5298 (nat_lit 85225984) (nat_lit 15625377506) (nat_lit 0) A10K2.t5299 from rfl, allE_node, rows5298, irow5292, rows5299]
  all_goals rfl

theorem atot5292 : totK PA10K2 A10K2.u5292 = [0, 0, 562018865097, 2624098682906, 4135871675756, 2227163981537, 312248458075, 6853348008, 0, 0] := by
  rw [show A10K2.u5292 = KTree.node A10K2.t5298 (nat_lit 85225984) (nat_lit 15625377506) (nat_lit 0) A10K2.t5299 from rfl, totK_node, tot5298, tot5299]
  decide +kernel

theorem arows5294 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5294 = true := by
  rw [show A10K2.u5294 = KTree.node A10K2.t5300 (nat_lit 85275803) (nat_lit 10068108498) (nat_lit 0) A10K2.t5301 from rfl, allE_node, rows5300, irow5294, rows5301]
  all_goals rfl

theorem atot5294 : totK PA10K2 A10K2.u5294 = [0, 0, 459322409883, 2336638942160, 4046303551328, 2399711647951, 395970714888, 25734533292, 0, 0] := by
  rw [show A10K2.u5294 = KTree.node A10K2.t5300 (nat_lit 85275803) (nat_lit 10068108498) (nat_lit 0) A10K2.t5301 from rfl, totK_node, tot5300, tot5301]
  decide +kernel

theorem arows5295 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5295 = true := by
  rw [show A10K2.u5295 = KTree.node A10K2.t5302 (nat_lit 85280419) (nat_lit 10563198731) (nat_lit 0) A10K2.t5303 from rfl, allE_node, rows5302, irow5295, rows5303]
  all_goals rfl

theorem atot5295 : totK PA10K2 A10K2.u5295 = [0, 0, 777370108884, 3205220455825, 3968377126723, 1497996616507, 174669888176, 5718040558, 0, 0] := by
  rw [show A10K2.u5295 = KTree.node A10K2.t5302 (nat_lit 85280419) (nat_lit 10563198731) (nat_lit 0) A10K2.t5303 from rfl, totK_node, tot5302, tot5303]
  decide +kernel

theorem arows5298 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5298 = true := by
  rw [show A10K2.u5298 = KTree.node A10K2.t5304 (nat_lit 85328149) (nat_lit 6796925496) (nat_lit 0) A10K2.t5305 from rfl, allE_node, rows5304, irow5298, rows5305]
  all_goals rfl

theorem atot5298 : totK PA10K2 A10K2.u5298 = [0, 0, 621170932120, 2722171280261, 3956012108100, 1902559465175, 280529584324, 6354482628, 0, 0] := by
  rw [show A10K2.u5298 = KTree.node A10K2.t5304 (nat_lit 85328149) (nat_lit 6796925496) (nat_lit 0) A10K2.t5305 from rfl, totK_node, tot5304, tot5305]
  decide +kernel

theorem arows5299 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5299 = true := by
  rw [show A10K2.u5299 = KTree.node A10K2.t5306 (nat_lit 85334079) (nat_lit 5975346219) (nat_lit 0) A10K2.t5307 from rfl, allE_node, rows5306, irow5299, rows5307]
  all_goals rfl

theorem atot5299 : totK PA10K2 A10K2.u5299 = [0, 0, 416751557437, 2217083918088, 3881278421213, 2432145148513, 460961805964, 30074883546, 0, 0] := by
  rw [show A10K2.u5299 = KTree.node A10K2.t5306 (nat_lit 85334079) (nat_lit 5975346219) (nat_lit 0) A10K2.t5307 from rfl, totK_node, tot5306, tot5307]
  decide +kernel

theorem arows5301 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5301 = true := by
  rw [show A10K2.u5301 = KTree.node A10K2.t5308 (nat_lit 85341395) (nat_lit 10878723544) (nat_lit 0) A10K2.t5309 from rfl, allE_node, rows5308, irow5301, rows5309]
  all_goals rfl

theorem atot5301 : totK PA10K2 A10K2.u5301 = [0, 0, 377659829977, 2128230546886, 3928296924531, 2472882717595, 493020258817, 31003444686, 0, 0] := by
  rw [show A10K2.u5301 = KTree.node A10K2.t5308 (nat_lit 85341395) (nat_lit 10878723544) (nat_lit 0) A10K2.t5309 from rfl, totK_node, tot5308, tot5309]
  decide +kernel

theorem arows5302 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5302 = true := by
  rw [show A10K2.u5302 = KTree.node A10K2.t5310 (nat_lit 85345979) (nat_lit 7019896344) (nat_lit 0) A10K2.t5311 from rfl, allE_node, rows5310, irow5302, rows5311]
  all_goals rfl

theorem atot5302 : totK PA10K2 A10K2.u5302 = [0, 0, 835897603759, 3318044816334, 3917424353371, 1288180359943, 94772109456, 0, 0, 0] := by
  rw [show A10K2.u5302 = KTree.node A10K2.t5310 (nat_lit 85345979) (nat_lit 7019896344) (nat_lit 0) A10K2.t5311 from rfl, totK_node, tot5310, tot5311]
  decide +kernel

theorem arows5308 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5308 = true := by
  rw [show A10K2.u5308 = KTree.node A10K2.t5312 (nat_lit 85360736) (nat_lit 13929524539) (nat_lit 0) A10K2.t5313 from rfl, allE_node, rows5312, irow5308, rows5313]
  all_goals rfl

theorem atot5308 : totK PA10K2 A10K2.u5308 = [0, 0, 0, 1174086963984, 3987919708999, 3399087792659, 685695711517, 31193230065, 0, 0] := by
  rw [show A10K2.u5308 = KTree.node A10K2.t5312 (nat_lit 85360736) (nat_lit 13929524539) (nat_lit 0) A10K2.t5313 from rfl, totK_node, tot5312, tot5313]
  decide +kernel

theorem arows5309 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5309 = true := by
  rw [show A10K2.u5309 = KTree.node A10K2.t5314 (nat_lit 85371158) (nat_lit 9854604557) (nat_lit 0) A10K2.t5315 from rfl, allE_node, rows5314, irow5309, rows5315]
  all_goals rfl

theorem atot5309 : totK PA10K2 A10K2.u5309 = [0, 0, 0, 1201060497164, 3847105002243, 3357821882161, 866292025059, 62700657452, 0, 0] := by
  rw [show A10K2.u5309 = KTree.node A10K2.t5314 (nat_lit 85371158) (nat_lit 9854604557) (nat_lit 0) A10K2.t5315 from rfl, totK_node, tot5314, tot5315]
  decide +kernel

theorem arows5311 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5311 = true := by
  rw [show A10K2.u5311 = KTree.node A10K2.t5316 (nat_lit 85379925) (nat_lit 6825870322) (nat_lit 0) A10K2.t5317 from rfl, allE_node, rows5316, irow5311, rows5317]
  all_goals rfl

theorem atot5311 : totK PA10K2 A10K2.u5311 = [0, 0, 0, 451885222873, 2602108801535, 4040534492861, 1779399688068, 199528122827, 0, 0] := by
  rw [show A10K2.u5311 = KTree.node A10K2.t5316 (nat_lit 85379925) (nat_lit 6825870322) (nat_lit 0) A10K2.t5317 from rfl, totK_node, tot5316, tot5317]
  decide +kernel

theorem arows5312 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5312 = true := by
  rw [show A10K2.u5312 = KTree.node A10K2.t5318 (nat_lit 85461539) (nat_lit 6982382048) (nat_lit 0) A10K2.t5319 from rfl, allE_node, rows5318, irow5312, rows5319]
  all_goals rfl

theorem atot5312 : totK PA10K2 A10K2.u5312 = [0, 842822735057, 3289402214160, 3880316632238, 1339891194089, 128924563034, 156188333899, 91540553519, 6354482628, 0] := by
  rw [show A10K2.u5312 = KTree.node A10K2.t5318 (nat_lit 85461539) (nat_lit 6982382048) (nat_lit 0) A10K2.t5319 from rfl, totK_node, tot5318, tot5319]
  decide +kernel

theorem arows5315 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5315 = true := by
  rw [show A10K2.u5315 = KTree.node A10K2.t5320 (nat_lit 85466296) (nat_lit 11465925770) (nat_lit 0) A10K2.t5321 from rfl, allE_node, rows5320, irow5315, rows5321]
  all_goals rfl

theorem atot5315 : totK PA10K2 A10K2.u5315 = [0, 520278790885, 2217458673002, 3704874595713, 2567229000161, 559845201131, 30831673886, 0, 0, 0] := by
  rw [show A10K2.u5315 = KTree.node A10K2.t5320 (nat_lit 85466296) (nat_lit 11465925770) (nat_lit 0) A10K2.t5321 from rfl, totK_node, tot5320, tot5321]
  decide +kernel

theorem arows5316 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5316 = true := by
  rw [show A10K2.u5316 = KTree.node A10K2.t5322 (nat_lit 85482260) (nat_lit 13252706185) (nat_lit 0) A10K2.t5323 from rfl, allE_node, rows5322, irow5316, rows5323]
  all_goals rfl

theorem atot5316 : totK PA10K2 A10K2.u5316 = [0, 525784600629, 2763839458918, 4219832023087, 1962399676543, 235516241090, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u5316 = KTree.node A10K2.t5322 (nat_lit 85482260) (nat_lit 13252706185) (nat_lit 0) A10K2.t5323 from rfl, totK_node, tot5322, tot5323]
  decide +kernel

theorem arows5318 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5318 = true := by
  rw [show A10K2.u5318 = KTree.node A10K2.t5324 (nat_lit 85488083) (nat_lit 8148536192) (nat_lit 0) A10K2.t5325 from rfl, allE_node, rows5324, irow5318, rows5325]
  all_goals rfl

theorem atot5318 : totK PA10K2 A10K2.u5318 = [0, 316555443509, 1996020058230, 4188275722781, 3125527673952, 578890244462, 13814455608, 0, 0, 0] := by
  rw [show A10K2.u5318 = KTree.node A10K2.t5324 (nat_lit 85488083) (nat_lit 8148536192) (nat_lit 0) A10K2.t5325 from rfl, totK_node, tot5324, tot5325]
  decide +kernel

theorem arows5319 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5319 = true := by
  rw [show A10K2.u5319 = KTree.node A10K2.t5326 (nat_lit 85493857) (nat_lit 9952831216) (nat_lit 0) A10K2.t5327 from rfl, allE_node, rows5326, irow5319, rows5327]
  all_goals rfl

theorem atot5319 : totK PA10K2 A10K2.u5319 = [0, 0, 842335651861, 3353599797086, 4032952393930, 1405976500573, 109381178748, 0, 0, 0] := by
  rw [show A10K2.u5319 = KTree.node A10K2.t5326 (nat_lit 85493857) (nat_lit 9952831216) (nat_lit 0) A10K2.t5327 from rfl, totK_node, tot5326, tot5327]
  decide +kernel

theorem arows5323 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5323 = true := by
  rw [show A10K2.u5323 = KTree.node A10K2.t5328 (nat_lit 85498709) (nat_lit 6064408592) (nat_lit 0) A10K2.t5329 from rfl, allE_node, rows5328, irow5323, rows5329]
  all_goals rfl

theorem atot5323 : totK PA10K2 A10K2.u5323 = [0, 0, 418471038443, 2103453423379, 3763550372163, 2531637782177, 546121303300, 30650496230, 0, 0] := by
  rw [show A10K2.u5323 = KTree.node A10K2.t5328 (nat_lit 85498709) (nat_lit 6064408592) (nat_lit 0) A10K2.t5329 from rfl, totK_node, tot5328, tot5329]
  decide +kernel

theorem arows5324 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5324 = true := by
  rw [show A10K2.u5324 = KTree.node A10K2.t5330 (nat_lit 85514786) (nat_lit 7131720848) (nat_lit 0) A10K2.t5331 from rfl, allE_node, rows5330, irow5324, rows5331]
  all_goals rfl

theorem atot5324 : totK PA10K2 A10K2.u5324 = [0, 0, 625087059197, 2895483064736, 4089084431419, 1761811428518, 219994301830, 5546304973, 0, 0] := by
  rw [show A10K2.u5324 = KTree.node A10K2.t5330 (nat_lit 85514786) (nat_lit 7131720848) (nat_lit 0) A10K2.t5331 from rfl, totK_node, tot5330, tot5331]
  decide +kernel

theorem arows5326 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5326 = true := by
  rw [show A10K2.u5326 = KTree.node A10K2.t5332 (nat_lit 85655963) (nat_lit 6341640561) (nat_lit 0) A10K2.t5333 from rfl, allE_node, rows5332, irow5326, rows5333]
  all_goals rfl

theorem atot5326 : totK PA10K2 A10K2.u5326 = [0, 780629253406, 2825715518936, 3534595873727, 2125147102925, 640780929021, 50548650670, 0, 0, 0] := by
  rw [show A10K2.u5326 = KTree.node A10K2.t5332 (nat_lit 85655963) (nat_lit 6341640561) (nat_lit 0) A10K2.t5333 from rfl, totK_node, tot5332, tot5333]
  decide +kernel

theorem arows5327 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5327 = true := by
  rw [show A10K2.u5327 = KTree.node A10K2.t5334 (nat_lit 85661745) (nat_lit 9895747630) (nat_lit 0) A10K2.t5335 from rfl, allE_node, rows5334, irow5327, rows5335]
  all_goals rfl

theorem atot5327 : totK PA10K2 A10K2.u5327 = [0, 287747644888, 2010611243888, 4134896895927, 2837476441703, 575492865006, 30749153377, 0, 0, 0] := by
  rw [show A10K2.u5327 = KTree.node A10K2.t5334 (nat_lit 85661745) (nat_lit 9895747630) (nat_lit 0) A10K2.t5335 from rfl, totK_node, tot5334, tot5335]
  decide +kernel

theorem arows5330 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5330 = true := by
  rw [show A10K2.u5330 = KTree.node A10K2.t5336 (nat_lit 85669206) (nat_lit 11733451979) (nat_lit 0) A10K2.t5337 from rfl, allE_node, rows5336, irow5330, rows5337]
  all_goals rfl

theorem atot5330 : totK PA10K2 A10K2.u5330 = [0, 589692706676, 2656264975200, 4085189154564, 2397388628069, 419494981466, 13572172291, 0, 0, 0] := by
  rw [show A10K2.u5330 = KTree.node A10K2.t5336 (nat_lit 85669206) (nat_lit 11733451979) (nat_lit 0) A10K2.t5337 from rfl, totK_node, tot5336, tot5337]
  decide +kernel

theorem arows5331 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5331 = true := by
  rw [show A10K2.u5331 = KTree.node A10K2.t5338 (nat_lit 85683447) (nat_lit 14712644156) (nat_lit 0) A10K2.t5339 from rfl, allE_node, rows5338, irow5331, rows5339]
  all_goals rfl

theorem atot5331 : totK PA10K2 A10K2.u5331 = [0, 585790443428, 2715557145959, 4161708491047, 2181065611029, 307244681790, 6853348008, 0, 0, 0] := by
  rw [show A10K2.u5331 = KTree.node A10K2.t5338 (nat_lit 85683447) (nat_lit 14712644156) (nat_lit 0) A10K2.t5339 from rfl, totK_node, tot5338, tot5339]
  decide +kernel

theorem arows5333 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5333 = true := by
  rw [show A10K2.u5333 = KTree.node A10K2.t5340 (nat_lit 85687999) (nat_lit 14105813498) (nat_lit 0) A10K2.t5341 from rfl, allE_node, rows5340, irow5333, rows5341]
  all_goals rfl

theorem atot5333 : totK PA10K2 A10K2.u5333 = [0, 0, 1057615284158, 3731287280755, 3844386374983, 1177434029186, 81606090030, 0, 0, 0] := by
  rw [show A10K2.u5333 = KTree.node A10K2.t5340 (nat_lit 85687999) (nat_lit 14105813498) (nat_lit 0) A10K2.t5341 from rfl, totK_node, tot5340, tot5341]
  decide +kernel

theorem arows5334 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5334 = true := by
  rw [show A10K2.u5334 = KTree.node A10K2.t5342 (nat_lit 85692780) (nat_lit 10934813971) (nat_lit 0) A10K2.t5343 from rfl, allE_node, rows5342, irow5334, rows5343]
  all_goals rfl

theorem atot5334 : totK PA10K2 A10K2.u5334 = [0, 0, 482424917178, 2437984573655, 4188711169991, 2393098280034, 341679780790, 6904928264, 0, 0] := by
  rw [show A10K2.u5334 = KTree.node A10K2.t5342 (nat_lit 85692780) (nat_lit 10934813971) (nat_lit 0) A10K2.t5343 from rfl, totK_node, tot5342, tot5343]
  decide +kernel

theorem arows5339 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5339 = true := by
  rw [show A10K2.u5339 = KTree.node A10K2.t5344 (nat_lit 85700552) (nat_lit 12243687177) (nat_lit 0) A10K2.t5345 from rfl, allE_node, rows5344, irow5339, rows5345]
  all_goals rfl

theorem atot5339 : totK PA10K2 A10K2.u5339 = [0, 0, 541236137279, 2665422168262, 4248876725930, 2344233045577, 299707325676, 7047025452, 0, 0] := by
  rw [show A10K2.u5339 = KTree.node A10K2.t5344 (nat_lit 85700552) (nat_lit 12243687177) (nat_lit 0) A10K2.t5345 from rfl, totK_node, tot5344, tot5345]
  decide +kernel

theorem arows5340 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5340 = true := by
  rw [show A10K2.u5340 = KTree.node A10K2.t5346 (nat_lit 85716038) (nat_lit 15221459860) (nat_lit 0) A10K2.t5347 from rfl, allE_node, rows5346, irow5340, rows5347]
  all_goals rfl

theorem atot5340 : totK PA10K2 A10K2.u5340 = [0, 0, 732795665976, 3159646220192, 4191049703489, 1734631639624, 137037874025, 0, 0, 0] := by
  rw [show A10K2.u5340 = KTree.node A10K2.t5346 (nat_lit 85716038) (nat_lit 15221459860) (nat_lit 0) A10K2.t5347 from rfl, totK_node, tot5346, tot5347]
  decide +kernel

theorem arows5342 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5342 = true := by
  rw [show A10K2.u5342 = KTree.node A10K2.t5348 (nat_lit 85720625) (nat_lit 9165662610) (nat_lit 0) A10K2.t5349 from rfl, allE_node, rows5348, irow5342, rows5349]
  all_goals rfl

theorem atot5342 : totK PA10K2 A10K2.u5342 = [0, 0, 421744910736, 1921936924735, 3528617012083, 3015180090516, 881432404386, 61110126106, 0, 0] := by
  rw [show A10K2.u5342 = KTree.node A10K2.t5348 (nat_lit 85720625) (nat_lit 9165662610) (nat_lit 0) A10K2.t5349 from rfl, totK_node, tot5348, tot5349]
  decide +kernel

theorem arows5343 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5343 = true := by
  rw [show A10K2.u5343 = KTree.node A10K2.t5350 (nat_lit 85725169) (nat_lit 8038460607) (nat_lit 0) A10K2.t5351 from rfl, allE_node, rows5350, irow5343, rows5351]
  all_goals rfl

theorem atot5343 : totK PA10K2 A10K2.u5343 = [0, 0, 421077824321, 2277003294649, 3959484031202, 2387212672080, 446233328360, 25333254304, 0, 0] := by
  rw [show A10K2.u5343 = KTree.node A10K2.t5350 (nat_lit 85725169) (nat_lit 8038460607) (nat_lit 0) A10K2.t5351 from rfl, totK_node, tot5350, tot5351]
  decide +kernel

theorem arows5346 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5346 = true := by
  rw [show A10K2.u5346 = KTree.node A10K2.t5352 (nat_lit 85739526) (nat_lit 12026390757) (nat_lit 0) A10K2.t5353 from rfl, allE_node, rows5352, irow5346, rows5353]
  all_goals rfl

theorem atot5346 : totK PA10K2 A10K2.u5346 = [0, 0, 559707398140, 2820776658201, 4157384773785, 1833106660638, 236182859232, 5447185874, 0, 0] := by
  rw [show A10K2.u5346 = KTree.node A10K2.t5352 (nat_lit 85739526) (nat_lit 12026390757) (nat_lit 0) A10K2.t5353 from rfl, totK_node, tot5352, tot5353]
  decide +kernel

theorem arows5347 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5347 = true := by
  rw [show A10K2.u5347 = KTree.node A10K2.t5354 (nat_lit 85747130) (nat_lit 14568508912) (nat_lit 0) A10K2.t5355 from rfl, allE_node, rows5354, irow5347, rows5355]
  all_goals rfl

theorem atot5347 : totK PA10K2 A10K2.u5347 = [0, 0, 802911436883, 3106532541146, 4021196669537, 1794523206066, 228247379814, 5705019915, 0, 0] := by
  rw [show A10K2.u5347 = KTree.node A10K2.t5354 (nat_lit 85747130) (nat_lit 14568508912) (nat_lit 0) A10K2.t5355 from rfl, totK_node, tot5354, tot5355]
  decide +kernel

theorem arows5349 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5349 = true := by
  rw [show A10K2.u5349 = KTree.node A10K2.t5356 (nat_lit 85753351) (nat_lit 14124766815) (nat_lit 0) A10K2.t5357 from rfl, allE_node, rows5356, irow5349, rows5357]
  all_goals rfl

theorem atot5349 : totK PA10K2 A10K2.u5349 = [0, 0, 0, 1113968145681, 3893967487492, 3910858598018, 1031998454854, 62115688426, 0, 0] := by
  rw [show A10K2.u5349 = KTree.node A10K2.t5356 (nat_lit 85753351) (nat_lit 14124766815) (nat_lit 0) A10K2.t5357 from rfl, totK_node, tot5356, tot5357]
  decide +kernel

theorem arows5350 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5350 = true := by
  rw [show A10K2.u5350 = KTree.node A10K2.t5358 (nat_lit 85758061) (nat_lit 5339389701) (nat_lit 0) A10K2.t5359 from rfl, allE_node, rows5358, irow5350, rows5359]
  all_goals rfl

theorem atot5350 : totK PA10K2 A10K2.u5350 = [0, 0, 0, 513089470429, 2608186936350, 4070273066164, 2062235013051, 301682493616, 7007974415, 0] := by
  rw [show A10K2.u5350 = KTree.node A10K2.t5358 (nat_lit 85758061) (nat_lit 5339389701) (nat_lit 0) A10K2.t5359 from rfl, totK_node, tot5358, tot5359]
  decide +kernel

theorem arows5354 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5354 = true := by
  rw [show A10K2.u5354 = KTree.node A10K2.t5360 (nat_lit 85778496) (nat_lit 15483700244) (nat_lit 0) A10K2.t5361 from rfl, allE_node, rows5360, irow5354, rows5361]
  all_goals rfl

theorem atot5354 : totK PA10K2 A10K2.u5354 = [0, 0, 0, 1243698913000, 4176427310573, 3716247622904, 690215596658, 23500939800, 0, 0] := by
  rw [show A10K2.u5354 = KTree.node A10K2.t5360 (nat_lit 85778496) (nat_lit 15483700244) (nat_lit 0) A10K2.t5361 from rfl, totK_node, tot5360, tot5361]
  decide +kernel

theorem arows5355 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5355 = true := by
  rw [show A10K2.u5355 = KTree.node A10K2.t5362 (nat_lit 85920068) (nat_lit 11870024144) (nat_lit 0) A10K2.t5363 from rfl, allE_node, rows5362, irow5355, rows5363]
  all_goals rfl

theorem atot5355 : totK PA10K2 A10K2.u5355 = [0, 0, 780629253406, 3041455476951, 3809929928358, 1831387404570, 397120115467, 30751586446, 0, 0] := by
  rw [show A10K2.u5355 = KTree.node A10K2.t5362 (nat_lit 85920068) (nat_lit 11870024144) (nat_lit 0) A10K2.t5363 from rfl, totK_node, tot5362, tot5363]
  decide +kernel

theorem arows5357 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5357 = true := by
  rw [show A10K2.u5357 = KTree.node A10K2.t5364 (nat_lit 85927144) (nat_lit 2577225769) (nat_lit 0) A10K2.t5365 from rfl, allE_node, rows5364, irow5357, rows5365]
  all_goals rfl

theorem atot5357 : totK PA10K2 A10K2.u5357 = [0, 0, 594732628490, 2706122663554, 4082600979040, 2260261243305, 376420562070, 11991740650, 0, 0] := by
  rw [show A10K2.u5357 = KTree.node A10K2.t5364 (nat_lit 85927144) (nat_lit 2577225769) (nat_lit 0) A10K2.t5365 from rfl, totK_node, tot5364, tot5365]
  decide +kernel

theorem arows5358 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5358 = true := by
  rw [show A10K2.u5358 = KTree.node A10K2.t5366 (nat_lit 85942334) (nat_lit 15643009357) (nat_lit 0) A10K2.t5367 from rfl, allE_node, rows5366, irow5358, rows5367]
  all_goals rfl

theorem atot5358 : totK PA10K2 A10K2.u5358 = [0, 0, 553322631842, 2640678470976, 4224656071300, 2305078336094, 337439871461, 7834437697, 0, 0] := by
  rw [show A10K2.u5358 = KTree.node A10K2.t5366 (nat_lit 85942334) (nat_lit 15643009357) (nat_lit 0) A10K2.t5367 from rfl, totK_node, tot5366, tot5367]
  decide +kernel

theorem arows5361 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5361 = true := by
  rw [show A10K2.u5361 = KTree.node A10K2.t5368 (nat_lit 85946867) (nat_lit 7799539766) (nat_lit 0) A10K2.t5369 from rfl, allE_node, rows5368, irow5361, rows5369]
  all_goals rfl

theorem atot5361 : totK PA10K2 A10K2.u5361 = [0, 0, 304495314875, 2061602276727, 4219442817771, 2955944063211, 509347690332, 13653259670, 0, 0] := by
  rw [show A10K2.u5361 = KTree.node A10K2.t5368 (nat_lit 85946867) (nat_lit 7799539766) (nat_lit 0) A10K2.t5369 from rfl, totK_node, tot5368, tot5369]
  decide +kernel

theorem arows5362 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5362 = true := by
  rw [show A10K2.u5362 = KTree.node A10K2.t5370 (nat_lit 88680371) (nat_lit 9868432826) (nat_lit 0) A10K2.t5371 from rfl, allE_node, rows5370, irow5362, rows5371]
  all_goals rfl

theorem atot5362 : totK PA10K2 A10K2.u5362 = [0, 872304469579, 3081739031152, 3119601512441, 1231514995883, 993629446407, 502902642157, 49180423016, 0, 0] := by
  rw [show A10K2.u5362 = KTree.node A10K2.t5370 (nat_lit 88680371) (nat_lit 9868432826) (nat_lit 0) A10K2.t5371 from rfl, totK_node, tot5370, tot5371]
  decide +kernel

theorem arows5364 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5364 = true := by
  rw [show A10K2.u5364 = KTree.node A10K2.t5372 (nat_lit 88684826) (nat_lit 14174292022) (nat_lit 0) A10K2.t5373 from rfl, allE_node, rows5372, irow5364, rows5373]
  all_goals rfl

theorem atot5364 : totK PA10K2 A10K2.u5364 = [0, 229738294190, 1660294941275, 3892473511953, 3081555016497, 648331744380, 31768748853, 0, 0, 0] := by
  rw [show A10K2.u5364 = KTree.node A10K2.t5372 (nat_lit 88684826) (nat_lit 14174292022) (nat_lit 0) A10K2.t5373 from rfl, totK_node, tot5372, tot5373]
  decide +kernel

theorem arows5365 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5365 = true := by
  rw [show A10K2.u5365 = KTree.node A10K2.t5374 (nat_lit 88689412) (nat_lit 13244202344) (nat_lit 0) A10K2.t5375 from rfl, allE_node, rows5374, irow5365, rows5375]
  all_goals rfl

theorem atot5365 : totK PA10K2 A10K2.u5365 = [0, 492150731016, 2696520367910, 4191893243824, 1871090020087, 174775753152, 0, 0, 0, 0] := by
  rw [show A10K2.u5365 = KTree.node A10K2.t5374 (nat_lit 88689412) (nat_lit 13244202344) (nat_lit 0) A10K2.t5375 from rfl, totK_node, tot5374, tot5375]
  decide +kernel

theorem arows5373 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5373 = true := by
  rw [show A10K2.u5373 = KTree.node A10K2.t5376 (nat_lit 88697864) (nat_lit 11044943411) (nat_lit 0) A10K2.t5377 from rfl, allE_node, rows5376, irow5373, rows5377]
  all_goals rfl

theorem atot5373 : totK PA10K2 A10K2.u5373 = [0, 743410903023, 2992244843575, 3941864227548, 1936372346388, 312719258349, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u5373 = KTree.node A10K2.t5376 (nat_lit 88697864) (nat_lit 11044943411) (nat_lit 0) A10K2.t5377 from rfl, totK_node, tot5376, tot5377]
  decide +kernel

theorem arows5374 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5374 = true := by
  rw [show A10K2.u5374 = KTree.node A10K2.t5378 (nat_lit 88702848) (nat_lit 13930236127) (nat_lit 0) A10K2.t5379 from rfl, allE_node, rows5378, irow5374, rows5379]
  all_goals rfl

theorem atot5374 : totK PA10K2 A10K2.u5374 = [0, 0, 1030302410525, 3668201902257, 3844749230947, 1166836487146, 74912841016, 0, 0, 0] := by
  rw [show A10K2.u5374 = KTree.node A10K2.t5378 (nat_lit 88702848) (nat_lit 13930236127) (nat_lit 0) A10K2.t5379 from rfl, totK_node, tot5378, tot5379]
  decide +kernel

theorem arows5376 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5376 = true := by
  rw [show A10K2.u5376 = KTree.node A10K2.t5380 (nat_lit 88716516) (nat_lit 12563449703) (nat_lit 0) A10K2.t5381 from rfl, allE_node, rows5380, irow5376, rows5381]
  all_goals rfl

theorem atot5376 : totK PA10K2 A10K2.u5376 = [0, 0, 325257928870, 2076448037289, 3924261402051, 2559338962332, 538907410839, 31082886609, 0, 0] := by
  rw [show A10K2.u5376 = KTree.node A10K2.t5380 (nat_lit 88716516) (nat_lit 12563449703) (nat_lit 0) A10K2.t5381 from rfl, totK_node, tot5380, tot5381]
  decide +kernel

theorem arows5377 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5377 = true := by
  rw [show A10K2.u5377 = KTree.node A10K2.t5382 (nat_lit 88721123) (nat_lit 10266137991) (nat_lit 0) A10K2.t5383 from rfl, allE_node, rows5382, irow5377, rows5383]
  all_goals rfl

theorem atot5377 : totK PA10K2 A10K2.u5377 = [0, 0, 727485560022, 3168122468227, 4047449948480, 1427550749341, 104123817588, 0, 0, 0] := by
  rw [show A10K2.u5377 = KTree.node A10K2.t5382 (nat_lit 88721123) (nat_lit 10266137991) (nat_lit 0) A10K2.t5383 from rfl, totK_node, tot5382, tot5383]
  decide +kernel

theorem arows5380 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5380 = true := by
  rw [show A10K2.u5380 = KTree.node A10K2.t5384 (nat_lit 88728730) (nat_lit 15217013153) (nat_lit 0) A10K2.t5385 from rfl, allE_node, rows5384, irow5380, rows5385]
  all_goals rfl

theorem atot5380 : totK PA10K2 A10K2.u5380 = [0, 0, 741189484195, 2957769960734, 3909427062359, 1726944381039, 212012257459, 6121173289, 0, 0] := by
  rw [show A10K2.u5380 = KTree.node A10K2.t5384 (nat_lit 88728730) (nat_lit 15217013153) (nat_lit 0) A10K2.t5385 from rfl, totK_node, tot5384, tot5385]
  decide +kernel

theorem arows5381 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5381 = true := by
  rw [show A10K2.u5381 = KTree.node A10K2.t5386 (nat_lit 88738308) (nat_lit 12621675841) (nat_lit 0) A10K2.t5387 from rfl, allE_node, rows5386, irow5381, rows5387]
  all_goals rfl

theorem atot5381 : totK PA10K2 A10K2.u5381 = [0, 468537272203, 2157891651430, 3540701158165, 2452810430325, 766735461958, 68070745818, 0, 0, 0] := by
  rw [show A10K2.u5381 = KTree.node A10K2.t5386 (nat_lit 88738308) (nat_lit 12621675841) (nat_lit 0) A10K2.t5387 from rfl, totK_node, tot5386, tot5387]
  decide +kernel

theorem arows5383 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5383 = true := by
  rw [show A10K2.u5383 = KTree.node A10K2.t5388 (nat_lit 88746304) (nat_lit 12153846593) (nat_lit 0) A10K2.t5389 from rfl, allE_node, rows5388, irow5383, rows5389]
  all_goals rfl

theorem atot5383 : totK PA10K2 A10K2.u5383 = [0, 799877054642, 3235589628252, 3981483785108, 1590361558540, 201354352223, 5460492893, 0, 0, 0] := by
  rw [show A10K2.u5383 = KTree.node A10K2.t5388 (nat_lit 88746304) (nat_lit 12153846593) (nat_lit 0) A10K2.t5389 from rfl, totK_node, tot5388, tot5389]
  decide +kernel

theorem arows5384 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5384 = true := by
  rw [show A10K2.u5384 = KTree.node A10K2.t5390 (nat_lit 88751537) (nat_lit 7223955143) (nat_lit 0) A10K2.t5391 from rfl, allE_node, rows5390, irow5384, rows5391]
  all_goals rfl

theorem atot5384 : totK PA10K2 A10K2.u5384 = [0, 491707397545, 2130115864377, 3596664700818, 2687153490138, 599940303162, 31768748853, 0, 0, 0] := by
  rw [show A10K2.u5384 = KTree.node A10K2.t5390 (nat_lit 88751537) (nat_lit 7223955143) (nat_lit 0) A10K2.t5391 from rfl, totK_node, tot5390, tot5391]
  decide +kernel

theorem arows5388 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5388 = true := by
  rw [show A10K2.u5388 = KTree.node A10K2.t5392 (nat_lit 88757427) (nat_lit 10220401137) (nat_lit 0) A10K2.t5393 from rfl, allE_node, rows5392, irow5388, rows5393]
  all_goals rfl

theorem atot5388 : totK PA10K2 A10K2.u5388 = [0, 298263154340, 2212897264516, 4230439308947, 2297819655871, 308731361296, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u5388 = KTree.node A10K2.t5392 (nat_lit 88757427) (nat_lit 10220401137) (nat_lit 0) A10K2.t5393 from rfl, totK_node, tot5392, tot5393]
  decide +kernel

theorem arows5389 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5389 = true := by
  rw [show A10K2.u5389 = KTree.node A10K2.t5394 (nat_lit 88778142) (nat_lit 15154462020) (nat_lit 0) A10K2.t5395 from rfl, allE_node, rows5394, irow5389, rows5395]
  all_goals rfl

theorem atot5389 : totK PA10K2 A10K2.u5389 = [0, 0, 959851826831, 3616098523724, 3878100387159, 1072013403151, 64458820912, 0, 0, 0] := by
  rw [show A10K2.u5389 = KTree.node A10K2.t5394 (nat_lit 88778142) (nat_lit 15154462020) (nat_lit 0) A10K2.t5395 from rfl, totK_node, tot5394, tot5395]
  decide +kernel

theorem arows5391 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5391 = true := by
  rw [show A10K2.u5391 = KTree.node A10K2.t5396 (nat_lit 88786325) (nat_lit 5580898498) (nat_lit 0) A10K2.t5397 from rfl, allE_node, rows5396, irow5391, rows5397]
  all_goals rfl

theorem atot5391 : totK PA10K2 A10K2.u5391 = [0, 0, 891440647044, 3432705300675, 3860565394623, 1135414054097, 83009222198, 0, 0, 0] := by
  rw [show A10K2.u5391 = KTree.node A10K2.t5396 (nat_lit 88786325) (nat_lit 5580898498) (nat_lit 0) A10K2.t5397 from rfl, totK_node, tot5396, tot5397]
  decide +kernel

theorem arows5392 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5392 = true := by
  rw [show A10K2.u5392 = KTree.node A10K2.t5398 (nat_lit 88804464) (nat_lit 14853042636) (nat_lit 0) A10K2.t5399 from rfl, allE_node, rows5398, irow5392, rows5399]
  all_goals rfl

theorem atot5392 : totK PA10K2 A10K2.u5392 = [0, 448034258811, 1696538381757, 2896199135361, 3034247607299, 1435393536076, 239904770714, 6354482628, 0, 0] := by
  rw [show A10K2.u5392 = KTree.node A10K2.t5398 (nat_lit 88804464) (nat_lit 14853042636) (nat_lit 0) A10K2.t5399 from rfl, totK_node, tot5398, tot5399]
  decide +kernel

theorem arows5395 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5395 = true := by
  rw [show A10K2.u5395 = KTree.node A10K2.t5400 (nat_lit 88812758) (nat_lit 15177660555) (nat_lit 0) A10K2.t5401 from rfl, allE_node, rows5400, irow5395, rows5401]
  all_goals rfl

theorem atot5395 : totK PA10K2 A10K2.u5395 = [0, 644842528050, 2911011382848, 4069336879701, 1959672763802, 323716700682, 20328650499, 0, 0, 0] := by
  rw [show A10K2.u5395 = KTree.node A10K2.t5400 (nat_lit 88812758) (nat_lit 15177660555) (nat_lit 0) A10K2.t5401 from rfl, totK_node, tot5400, tot5401]
  decide +kernel

theorem arows5396 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5396 = true := by
  rw [show A10K2.u5396 = KTree.node A10K2.t5402 (nat_lit 88826334) (nat_lit 15060741965) (nat_lit 0) A10K2.t5403 from rfl, allE_node, rows5402, irow5396, rows5403]
  all_goals rfl

theorem atot5396 : totK PA10K2 A10K2.u5396 = [0, 753383565637, 2873326970970, 3903778912551, 2109234615351, 368327376782, 11418542001, 0, 0, 0] := by
  rw [show A10K2.u5396 = KTree.node A10K2.t5402 (nat_lit 88826334) (nat_lit 15060741965) (nat_lit 0) A10K2.t5403 from rfl, totK_node, tot5402, tot5403]
  decide +kernel

theorem arows5398 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5398 = true := by
  rw [show A10K2.u5398 = KTree.node A10K2.t5404 (nat_lit 88831367) (nat_lit 14546408604) (nat_lit 0) A10K2.t5405 from rfl, allE_node, rows5404, irow5398, rows5405]
  all_goals rfl

theorem atot5398 : totK PA10K2 A10K2.u5398 = [0, 46039240014, 1350083584861, 3997718739678, 3689525895361, 978580670482, 36984672867, 0, 0, 0] := by
  rw [show A10K2.u5398 = KTree.node A10K2.t5404 (nat_lit 88831367) (nat_lit 14546408604) (nat_lit 0) A10K2.t5405 from rfl, totK_node, tot5404, tot5405]
  decide +kernel

theorem arows5399 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5399 = true := by
  rw [show A10K2.u5399 = KTree.node A10K2.t5406 (nat_lit 88843475) (nat_lit 10878723544) (nat_lit 0) A10K2.t5407 from rfl, allE_node, rows5406, irow5399, rows5407]
  all_goals rfl

theorem atot5399 : totK PA10K2 A10K2.u5399 = [0, 0, 864574962501, 3347418164697, 4003564119000, 1589415141605, 160760552925, 0, 0, 0] := by
  rw [show A10K2.u5399 = KTree.node A10K2.t5406 (nat_lit 88843475) (nat_lit 10878723544) (nat_lit 0) A10K2.t5407 from rfl, totK_node, tot5406, tot5407]
  decide +kernel

theorem arows5404 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5404 = true := by
  rw [show A10K2.u5404 = KTree.node A10K2.t5408 (nat_lit 88848090) (nat_lit 13850025289) (nat_lit 0) A10K2.t5409 from rfl, allE_node, rows5408, irow5404, rows5409]
  all_goals rfl

theorem atot5404 : totK PA10K2 A10K2.u5404 = [0, 0, 488754517403, 2518994862835, 4304487843303, 2441034537177, 326000761736, 7047025452, 0, 0] := by
  rw [show A10K2.u5404 = KTree.node A10K2.t5408 (nat_lit 88848090) (nat_lit 13850025289) (nat_lit 0) A10K2.t5409 from rfl, totK_node, tot5408, tot5409]
  decide +kernel

theorem arows5405 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5405 = true := by
  rw [show A10K2.u5405 = KTree.node A10K2.t5410 (nat_lit 88862357) (nat_lit 4799289522) (nat_lit 0) A10K2.t5411 from rfl, allE_node, rows5410, irow5405, rows5411]
  all_goals rfl

theorem atot5405 : totK PA10K2 A10K2.u5405 = [0, 0, 537368149671, 2614004518014, 4166389981797, 2393793105047, 324429697256, 6157148557, 0, 0] := by
  rw [show A10K2.u5405 = KTree.node A10K2.t5410 (nat_lit 88862357) (nat_lit 4799289522) (nat_lit 0) A10K2.t5411 from rfl, totK_node, tot5410, tot5411]
  decide +kernel

theorem arows5407 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5407 = true := by
  rw [show A10K2.u5407 = KTree.node A10K2.t5412 (nat_lit 88942015) (nat_lit 14142963752) (nat_lit 0) A10K2.t5413 from rfl, allE_node, rows5412, irow5407, rows5413]
  all_goals rfl

theorem atot5407 : totK PA10K2 A10K2.u5407 = [0, 0, 755012614725, 2831990573370, 3541128239723, 2009389463836, 538444223359, 35764095907, 0, 0] := by
  rw [show A10K2.u5407 = KTree.node A10K2.t5412 (nat_lit 88942015) (nat_lit 14142963752) (nat_lit 0) A10K2.t5413 from rfl, totK_node, tot5412, tot5413]
  decide +kernel

theorem arows5408 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5408 = true := by
  rw [show A10K2.u5408 = KTree.node A10K2.t5414 (nat_lit 88946466) (nat_lit 13522820991) (nat_lit 0) A10K2.t5415 from rfl, allE_node, rows5414, irow5408, rows5415]
  all_goals rfl

theorem atot5408 : totK PA10K2 A10K2.u5408 = [0, 0, 202691441197, 1704002733917, 4028358571308, 3052139930418, 620688589921, 31768748853, 0, 0] := by
  rw [show A10K2.u5408 = KTree.node A10K2.t5414 (nat_lit 88946466) (nat_lit 13522820991) (nat_lit 0) A10K2.t5415 from rfl, totK_node, tot5414, tot5415]
  decide +kernel

theorem arows5411 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5411 = true := by
  rw [show A10K2.u5411 = KTree.node A10K2.t5416 (nat_lit 88951002) (nat_lit 14025086665) (nat_lit 0) A10K2.t5417 from rfl, allE_node, rows5416, irow5411, rows5417]
  all_goals rfl

theorem atot5411 : totK PA10K2 A10K2.u5411 = [0, 0, 639552187714, 3073311045968, 4120479364459, 1481773696080, 89530459411, 0, 0, 0] := by
  rw [show A10K2.u5411 = KTree.node A10K2.t5416 (nat_lit 88951002) (nat_lit 14025086665) (nat_lit 0) A10K2.t5417 from rfl, totK_node, tot5416, tot5417]
  decide +kernel

theorem arows5412 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5412 = true := by
  rw [show A10K2.u5412 = KTree.node A10K2.t5418 (nat_lit 88958632) (nat_lit 3575396205) (nat_lit 0) A10K2.t5419 from rfl, allE_node, rows5418, irow5412, rows5419]
  all_goals rfl

theorem atot5412 : totK PA10K2 A10K2.u5412 = [0, 0, 742488449518, 2980725335775, 3974079815396, 1815060585609, 231993755768, 6239673734, 0, 0] := by
  rw [show A10K2.u5412 = KTree.node A10K2.t5418 (nat_lit 88958632) (nat_lit 3575396205) (nat_lit 0) A10K2.t5419 from rfl, totK_node, tot5418, tot5419]
  decide +kernel

theorem arows5414 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5414 = true := by
  rw [show A10K2.u5414 = KTree.node A10K2.t5420 (nat_lit 88964615) (nat_lit 11738550817) (nat_lit 8) A10K2.t5421 from rfl, allE_node, rows5420, irow5414, rows5421]
  all_goals rfl

theorem atot5414 : totK PA10K2 A10K2.u5414 = [0, 0, 0, 1059854591397, 3845999046442, 3859639940938, 1031413386496, 62906696551, 0, 0] := by
  rw [show A10K2.u5414 = KTree.node A10K2.t5420 (nat_lit 88964615) (nat_lit 11738550817) (nat_lit 8) A10K2.t5421 from rfl, totK_node, tot5420, tot5421]
  decide +kernel

theorem arows5415 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5415 = true := by
  rw [show A10K2.u5415 = KTree.node A10K2.t5422 (nat_lit 88978618) (nat_lit 15083127022) (nat_lit 0) A10K2.t5423 from rfl, allE_node, rows5422, irow5415, rows5423]
  all_goals rfl

theorem atot5415 : totK PA10K2 A10K2.u5415 = [0, 0, 0, 398047221139, 2238483858799, 3890397878472, 2364989621019, 468987440186, 25565504801, 0] := by
  rw [show A10K2.u5415 = KTree.node A10K2.t5422 (nat_lit 88978618) (nat_lit 15083127022) (nat_lit 0) A10K2.t5423 from rfl, totK_node, tot5422, tot5423]
  decide +kernel

theorem arows5419 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5419 = true := by
  rw [show A10K2.u5419 = KTree.node A10K2.t5424 (nat_lit 88983268) (nat_lit 12755491804) (nat_lit 0) A10K2.t5425 from rfl, allE_node, rows5424, irow5419, rows5425]
  all_goals rfl

theorem atot5419 : totK PA10K2 A10K2.u5419 = [0, 0, 0, 720927804537, 3193678869908, 3893579245310, 1313749546032, 157181258545, 5453062850, 0] := by
  rw [show A10K2.u5419 = KTree.node A10K2.t5424 (nat_lit 88983268) (nat_lit 12755491804) (nat_lit 0) A10K2.t5425 from rfl, totK_node, tot5424, tot5425]
  decide +kernel

theorem arows5420 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5420 = true := by
  rw [show A10K2.u5420 = KTree.node A10K2.t5426 (nat_lit 88991113) (nat_lit 3550382914) (nat_lit 2) A10K2.t5427 from rfl, allE_node, rows5426, irow5420, rows5427]
  all_goals rfl

theorem atot5420 : totK PA10K2 A10K2.u5420 = [0, 0, 103649551945, 948534711534, 2994839531689, 3795539021060, 1663385167863, 217276317630, 5685526223, 0] := by
  rw [show A10K2.u5420 = KTree.node A10K2.t5426 (nat_lit 88991113) (nat_lit 3550382914) (nat_lit 2) A10K2.t5427 from rfl, totK_node, tot5426, tot5427]
  decide +kernel

theorem arows5422 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5422 = true := by
  rw [show A10K2.u5422 = KTree.node A10K2.t5428 (nat_lit 89002266) (nat_lit 8766721568) (nat_lit 0) A10K2.t5429 from rfl, allE_node, rows5428, irow5422, rows5429]
  all_goals rfl

theorem atot5422 : totK PA10K2 A10K2.u5422 = [0, 0, 674305396046, 2889065077900, 3889820156996, 1752433571335, 226998093955, 5460492893, 0, 0] := by
  rw [show A10K2.u5422 = KTree.node A10K2.t5428 (nat_lit 89002266) (nat_lit 8766721568) (nat_lit 0) A10K2.t5429 from rfl, totK_node, tot5428, tot5429]
  decide +kernel

theorem arows5423 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5423 = true := by
  rw [show A10K2.u5423 = KTree.node A10K2.t5430 (nat_lit 89009876) (nat_lit 9409706037) (nat_lit 0) A10K2.t5431 from rfl, allE_node, rows5430, irow5423, rows5431]
  all_goals rfl

theorem atot5423 : totK PA10K2 A10K2.u5423 = [0, 0, 490459378854, 2537098119600, 4057198144102, 2220076016077, 413946677408, 25734533292, 0, 0] := by
  rw [show A10K2.u5423 = KTree.node A10K2.t5430 (nat_lit 89009876) (nat_lit 9409706037) (nat_lit 0) A10K2.t5431 from rfl, totK_node, tot5430, tot5431]
  decide +kernel

theorem arows5426 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5426 = true := by
  rw [show A10K2.u5426 = KTree.node A10K2.t5432 (nat_lit 89015453) (nat_lit 6181965923) (nat_lit 0) A10K2.t5433 from rfl, allE_node, rows5432, irow5426, rows5433]
  all_goals rfl

theorem atot5426 : totK PA10K2 A10K2.u5426 = [0, 0, 789970551885, 2973707543198, 3694928479430, 1754018457262, 246018188550, 6034215561, 0, 0] := by
  rw [show A10K2.u5426 = KTree.node A10K2.t5432 (nat_lit 89015453) (nat_lit 6181965923) (nat_lit 0) A10K2.t5433 from rfl, totK_node, tot5432, tot5433]
  decide +kernel

theorem arows5427 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5427 = true := by
  rw [show A10K2.u5427 = KTree.node A10K2.t5434 (nat_lit 89020776) (nat_lit 9665578208) (nat_lit 0) A10K2.t5435 from rfl, allE_node, rows5434, irow5427, rows5435]
  all_goals rfl

theorem atot5427 : totK PA10K2 A10K2.u5427 = [0, 0, 0, 1487177772332, 4317479114951, 2971193526682, 476401592159, 12477276923, 0, 0] := by
  rw [show A10K2.u5427 = KTree.node A10K2.t5434 (nat_lit 89020776) (nat_lit 9665578208) (nat_lit 0) A10K2.t5435 from rfl, totK_node, tot5434, tot5435]
  decide +kernel

theorem arows5429 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5429 = true := by
  rw [show A10K2.u5429 = KTree.node A10K2.t5436 (nat_lit 89041690) (nat_lit 12802278115) (nat_lit 0) A10K2.t5437 from rfl, allE_node, rows5436, irow5429, rows5437]
  all_goals rfl

theorem atot5429 : totK PA10K2 A10K2.u5429 = [0, 0, 0, 1062104764474, 3829524267514, 3785860735410, 907446693413, 44649496490, 0, 0] := by
  rw [show A10K2.u5429 = KTree.node A10K2.t5436 (nat_lit 89041690) (nat_lit 12802278115) (nat_lit 0) A10K2.t5437 from rfl, totK_node, tot5436, tot5437]
  decide +kernel

theorem arows5430 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5430 = true := by
  rw [show A10K2.u5430 = KTree.node A10K2.t5438 (nat_lit 89051176) (nat_lit 12782016780) (nat_lit 0) A10K2.t5439 from rfl, allE_node, rows5438, irow5430, rows5439]
  all_goals rfl

theorem atot5430 : totK PA10K2 A10K2.u5430 = [0, 0, 120678695417, 671810164464, 2598188938334, 3940170981006, 1715964969445, 222689588241, 6239673734, 0] := by
  rw [show A10K2.u5430 = KTree.node A10K2.t5438 (nat_lit 89051176) (nat_lit 12782016780) (nat_lit 0) A10K2.t5439 from rfl, totK_node, tot5438, tot5439]
  decide +kernel

theorem arows5436 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5436 = true := by
  rw [show A10K2.u5436 = KTree.node A10K2.t5440 (nat_lit 89072981) (nat_lit 6787962896) (nat_lit 0) A10K2.t5441 from rfl, allE_node, rows5440, irow5436, rows5441]
  all_goals rfl

theorem atot5436 : totK PA10K2 A10K2.u5436 = [0, 0, 850696945618, 3392193254901, 4081461430630, 1569474648248, 136113882564, 0, 0, 0] := by
  rw [show A10K2.u5436 = KTree.node A10K2.t5440 (nat_lit 89072981) (nat_lit 6787962896) (nat_lit 0) A10K2.t5441 from rfl, totK_node, tot5440, tot5441]
  decide +kernel

theorem arows5437 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5437 = true := by
  rw [show A10K2.u5437 = KTree.node A10K2.t5442 (nat_lit 89077603) (nat_lit 9296564231) (nat_lit 0) A10K2.t5443 from rfl, allE_node, rows5442, irow5437, rows5443]
  all_goals rfl

theorem atot5437 : totK PA10K2 A10K2.u5437 = [0, 0, 296626856653, 1993988003825, 4097820809340, 2942831080784, 596181232543, 31285368086, 0, 0] := by
  rw [show A10K2.u5437 = KTree.node A10K2.t5442 (nat_lit 89077603) (nat_lit 9296564231) (nat_lit 0) A10K2.t5443 from rfl, totK_node, tot5442, tot5443]
  decide +kernel

theorem arows5439 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5439 = true := by
  rw [show A10K2.u5439 = KTree.node A10K2.t5444 (nat_lit 89091539) (nat_lit 10271059142) (nat_lit 0) A10K2.t5445 from rfl, allE_node, rows5444, irow5439, rows5445]
  all_goals rfl

theorem atot5439 : totK PA10K2 A10K2.u5439 = [0, 0, 606494053456, 2847001855121, 4354611955068, 2152448461076, 222942360236, 0, 0, 0] := by
  rw [show A10K2.u5439 = KTree.node A10K2.t5444 (nat_lit 89091539) (nat_lit 10271059142) (nat_lit 0) A10K2.t5445 from rfl, totK_node, tot5444, tot5445]
  decide +kernel

theorem arows5440 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5440 = true := by
  rw [show A10K2.u5440 = KTree.node A10K2.t5446 (nat_lit 89129220) (nat_lit 12865384108) (nat_lit 0) A10K2.t5447 from rfl, allE_node, rows5446, irow5440, rows5447]
  all_goals rfl

theorem atot5440 : totK PA10K2 A10K2.u5440 = [0, 597780859188, 2091414530811, 2460245972826, 2012304394523, 1901027628026, 651410165105, 42874818239, 0, 0] := by
  rw [show A10K2.u5440 = KTree.node A10K2.t5446 (nat_lit 89129220) (nat_lit 12865384108) (nat_lit 0) A10K2.t5447 from rfl, totK_node, tot5446, tot5447]
  decide +kernel

theorem arows5443 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5443 = true := by
  rw [show A10K2.u5443 = KTree.node A10K2.t5448 (nat_lit 89135160) (nat_lit 14671596437) (nat_lit 0) A10K2.t5449 from rfl, allE_node, rows5448, irow5443, rows5449]
  all_goals rfl

theorem atot5443 : totK PA10K2 A10K2.u5443 = [0, 423410980110, 2265869025193, 3945147985434, 2501609393929, 467027136032, 30831673886, 0, 0, 0] := by
  rw [show A10K2.u5443 = KTree.node A10K2.t5448 (nat_lit 89135160) (nat_lit 14671596437) (nat_lit 0) A10K2.t5449 from rfl, totK_node, tot5448, tot5449]
  decide +kernel

theorem arows5444 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5444 = true := by
  rw [show A10K2.u5444 = KTree.node A10K2.t5450 (nat_lit 89147953) (nat_lit 9666776453) (nat_lit 0) A10K2.t5451 from rfl, allE_node, rows5450, irow5444, rows5451]
  all_goals rfl

theorem atot5444 : totK PA10K2 A10K2.u5444 = [0, 502204280108, 2763972571348, 4334109143432, 1842870466435, 159402439840, 0, 0, 0, 0] := by
  rw [show A10K2.u5444 = KTree.node A10K2.t5450 (nat_lit 89147953) (nat_lit 9666776453) (nat_lit 0) A10K2.t5451 from rfl, totK_node, tot5450, tot5451]
  decide +kernel

theorem arows5446 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5446 = true := by
  rw [show A10K2.u5446 = KTree.node A10K2.t5452 (nat_lit 89163989) (nat_lit 6330654280) (nat_lit 0) A10K2.t5453 from rfl, allE_node, rows5452, irow5446, rows5453]
  all_goals rfl

theorem atot5446 : totK PA10K2 A10K2.u5446 = [0, 0, 756324147962, 3352748702593, 4125180864742, 1289479563504, 77205233541, 0, 0, 0] := by
  rw [show A10K2.u5446 = KTree.node A10K2.t5452 (nat_lit 89163989) (nat_lit 6330654280) (nat_lit 0) A10K2.t5453 from rfl, totK_node, tot5452, tot5453]
  decide +kernel

theorem arows5447 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5447 = true := by
  rw [show A10K2.u5447 = KTree.node A10K2.t5454 (nat_lit 89178226) (nat_lit 4361297840) (nat_lit 0) A10K2.t5455 from rfl, allE_node, rows5454, irow5447, rows5455]
  all_goals rfl

theorem atot5447 : totK PA10K2 A10K2.u5447 = [0, 0, 667492959907, 2634823501537, 3647614138972, 2025466314483, 437914670698, 30650496230, 0, 0] := by
  rw [show A10K2.u5447 = KTree.node A10K2.t5454 (nat_lit 89178226) (nat_lit 4361297840) (nat_lit 0) A10K2.t5455 from rfl, totK_node, tot5454, tot5455]
  decide +kernel

theorem arows5451 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5451 = true := by
  rw [show A10K2.u5451 = KTree.node A10K2.t5456 (nat_lit 89184481) (nat_lit 5052735909) (nat_lit 0) A10K2.t5457 from rfl, allE_node, rows5456, irow5451, rows5457]
  all_goals rfl

theorem atot5451 : totK PA10K2 A10K2.u5451 = [0, 374690907472, 1326203507220, 2670053223936, 3339164772565, 1539166416356, 199083392831, 5546304973, 0, 0] := by
  rw [show A10K2.u5451 = KTree.node A10K2.t5456 (nat_lit 89184481) (nat_lit 5052735909) (nat_lit 0) A10K2.t5457 from rfl, totK_node, tot5456, tot5457]
  decide +kernel

theorem arows5452 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5452 = true := by
  rw [show A10K2.u5452 = KTree.node A10K2.t5458 (nat_lit 89206728) (nat_lit 5602958845) (nat_lit 0) A10K2.t5459 from rfl, allE_node, rows5458, irow5452, rows5459]
  all_goals rfl

theorem atot5452 : totK PA10K2 A10K2.u5452 = [0, 461552447388, 2420043055508, 3959728837442, 2303221424675, 434560263302, 25734533292, 0, 0, 0] := by
  rw [show A10K2.u5452 = KTree.node A10K2.t5458 (nat_lit 89206728) (nat_lit 5602958845) (nat_lit 0) A10K2.t5459 from rfl, totK_node, tot5458, tot5459]
  decide +kernel

theorem arows5454 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5454 = true := by
  rw [show A10K2.u5454 = KTree.node A10K2.t5460 (nat_lit 89212161) (nat_lit 8985100505) (nat_lit 0) A10K2.t5461 from rfl, allE_node, rows5460, irow5454, rows5461]
  all_goals rfl

theorem atot5454 : totK PA10K2 A10K2.u5454 = [0, 770689108024, 3047967513949, 3788818197537, 1707802203464, 244356763346, 6034215561, 0, 0, 0] := by
  rw [show A10K2.u5454 = KTree.node A10K2.t5460 (nat_lit 89212161) (nat_lit 8985100505) (nat_lit 0) A10K2.t5461 from rfl, totK_node, tot5460, tot5461]
  decide +kernel

theorem arows5455 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5455 = true := by
  rw [show A10K2.u5455 = KTree.node A10K2.t5462 (nat_lit 89217814) (nat_lit 5787172120) (nat_lit 0) A10K2.t5463 from rfl, allE_node, rows5462, irow5455, rows5463]
  all_goals rfl

theorem atot5455 : totK PA10K2 A10K2.u5455 = [0, 554803763168, 2591500023862, 4078783291392, 2166644704001, 301874974759, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u5455 = KTree.node A10K2.t5462 (nat_lit 89217814) (nat_lit 5787172120) (nat_lit 0) A10K2.t5463 from rfl, totK_node, tot5462, tot5463]
  decide +kernel

theorem arows5458 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5458 = true := by
  rw [show A10K2.u5458 = KTree.node A10K2.t5464 (nat_lit 89226689) (nat_lit 7060372908) (nat_lit 0) A10K2.t5465 from rfl, allE_node, rows5464, irow5458, rows5465]
  all_goals rfl

theorem atot5458 : totK PA10K2 A10K2.u5458 = [0, 0, 1121828249649, 3801824915171, 3769658069512, 1101136527391, 69341511228, 0, 0, 0] := by
  rw [show A10K2.u5458 = KTree.node A10K2.t5464 (nat_lit 89226689) (nat_lit 7060372908) (nat_lit 0) A10K2.t5465 from rfl, totK_node, tot5464, tot5465]
  decide +kernel

theorem arows5459 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5459 = true := by
  rw [show A10K2.u5459 = KTree.node A10K2.t5466 (nat_lit 89239506) (nat_lit 14872883413) (nat_lit 0) A10K2.t5467 from rfl, allE_node, rows5466, irow5459, rows5467]
  all_goals rfl

theorem atot5459 : totK PA10K2 A10K2.u5459 = [0, 0, 473413749271, 2419570039544, 3913556710875, 2219518086671, 427920917344, 25565504801, 0, 0] := by
  rw [show A10K2.u5459 = KTree.node A10K2.t5466 (nat_lit 89239506) (nat_lit 14872883413) (nat_lit 0) A10K2.t5467 from rfl, totK_node, tot5466, tot5467]
  decide +kernel

theorem arows5461 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5461 = true := by
  rw [show A10K2.u5461 = KTree.node A10K2.t5468 (nat_lit 89245084) (nat_lit 9134907188) (nat_lit 0) A10K2.t5469 from rfl, allE_node, rows5468, irow5461, rows5469]
  all_goals rfl

theorem atot5461 : totK PA10K2 A10K2.u5461 = [0, 0, 770540961848, 3156093295748, 3863168476880, 1540526065363, 189520111989, 5517381808, 0, 0] := by
  rw [show A10K2.u5461 = KTree.node A10K2.t5468 (nat_lit 89245084) (nat_lit 9134907188) (nat_lit 0) A10K2.t5469 from rfl, totK_node, tot5468, tot5469]
  decide +kernel

theorem arows5462 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5462 = true := by
  rw [show A10K2.u5462 = KTree.node A10K2.t5470 (nat_lit 89253074) (nat_lit 15653405069) (nat_lit 0) A10K2.t5471 from rfl, allE_node, rows5470, irow5462, rows5471]
  all_goals rfl

theorem atot5462 : totK PA10K2 A10K2.u5462 = [0, 0, 552451521902, 2628444068191, 4144417375795, 2021261756489, 240344414117, 6121173289, 0, 0] := by
  rw [show A10K2.u5462 = KTree.node A10K2.t5470 (nat_lit 89253074) (nat_lit 15653405069) (nat_lit 0) A10K2.t5471 from rfl, totK_node, tot5470, tot5471]
  decide +kernel

theorem arows5467 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5467 = true := by
  rw [show A10K2.u5467 = KTree.node A10K2.t5472 (nat_lit 89262606) (nat_lit 11394377093) (nat_lit 0) A10K2.t5473 from rfl, allE_node, rows5472, irow5467, rows5473]
  all_goals rfl

theorem atot5467 : totK PA10K2 A10K2.u5467 = [0, 651689738107, 2733998910354, 3635642561380, 1934116843001, 549375614877, 55567120832, 0, 0, 0] := by
  rw [show A10K2.u5467 = KTree.node A10K2.t5472 (nat_lit 89262606) (nat_lit 11394377093) (nat_lit 0) A10K2.t5473 from rfl, totK_node, tot5472, tot5473]
  decide +kernel

theorem arows5468 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5468 = true := by
  rw [show A10K2.u5468 = KTree.node A10K2.t5474 (nat_lit 89270002) (nat_lit 14867522649) (nat_lit 0) A10K2.t5475 from rfl, allE_node, rows5474, irow5468, rows5475]
  all_goals rfl

theorem atot5468 : totK PA10K2 A10K2.u5468 = [0, 765270380182, 2992385065922, 3899520845619, 1747064050002, 216758267469, 5460492893, 0, 0, 0] := by
  rw [show A10K2.u5468 = KTree.node A10K2.t5474 (nat_lit 89270002) (nat_lit 14867522649) (nat_lit 0) A10K2.t5475 from rfl, totK_node, tot5474, tot5475]
  decide +kernel

theorem arows5470 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5470 = true := by
  rw [show A10K2.u5470 = KTree.node A10K2.t5476 (nat_lit 89274724) (nat_lit 13913855522) (nat_lit 0) A10K2.t5477 from rfl, allE_node, rows5476, irow5470, rows5477]
  all_goals rfl

theorem atot5470 : totK PA10K2 A10K2.u5470 = [0, 303780122938, 1836384473255, 3823042331641, 2903509266244, 628142581624, 31768748853, 0, 0, 0] := by
  rw [show A10K2.u5470 = KTree.node A10K2.t5476 (nat_lit 89274724) (nat_lit 13913855522) (nat_lit 0) A10K2.t5477 from rfl, totK_node, tot5476, tot5477]
  decide +kernel

theorem arows5471 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5471 = true := by
  rw [show A10K2.u5471 = KTree.node A10K2.t5478 (nat_lit 89279162) (nat_lit 13519592234) (nat_lit 0) A10K2.t5479 from rfl, allE_node, rows5478, irow5471, rows5479]
  all_goals rfl

theorem atot5471 : totK PA10K2 A10K2.u5471 = [0, 519455835492, 2878825679946, 4261800225892, 1734947075323, 140464755192, 0, 0, 0, 0] := by
  rw [show A10K2.u5471 = KTree.node A10K2.t5478 (nat_lit 89279162) (nat_lit 13519592234) (nat_lit 0) A10K2.t5479 from rfl, totK_node, tot5478, tot5479]
  decide +kernel

theorem arows5474 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5474 = true := by
  rw [show A10K2.u5474 = KTree.node A10K2.t5480 (nat_lit 89295068) (nat_lit 11166600696) (nat_lit 0) A10K2.t5481 from rfl, allE_node, rows5480, irow5474, rows5481]
  all_goals rfl

theorem atot5474 : totK PA10K2 A10K2.u5474 = [0, 0, 948878768467, 3648949775400, 3827035105925, 1035017170429, 65727210316, 0, 0, 0] := by
  rw [show A10K2.u5474 = KTree.node A10K2.t5480 (nat_lit 89295068) (nat_lit 11166600696) (nat_lit 0) A10K2.t5481 from rfl, totK_node, tot5480, tot5481]
  decide +kernel

theorem arows5475 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5475 = true := by
  rw [show A10K2.u5475 = KTree.node A10K2.t5482 (nat_lit 89304978) (nat_lit 15204535253) (nat_lit 0) A10K2.t5483 from rfl, allE_node, rows5482, irow5475, rows5483]
  all_goals rfl

theorem atot5475 : totK PA10K2 A10K2.u5475 = [0, 0, 991501742178, 3621368762840, 3818132926339, 1038847947522, 63118289004, 0, 0, 0] := by
  rw [show A10K2.u5475 = KTree.node A10K2.t5482 (nat_lit 89304978) (nat_lit 15204535253) (nat_lit 0) A10K2.t5483 from rfl, totK_node, tot5482, tot5483]
  decide +kernel

theorem arows5477 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5477 = true := by
  rw [show A10K2.u5477 = KTree.node A10K2.t5484 (nat_lit 89314466) (nat_lit 14377112747) (nat_lit 0) A10K2.t5485 from rfl, allE_node, rows5484, irow5477, rows5485]
  all_goals rfl

theorem atot5477 : totK PA10K2 A10K2.u5477 = [0, 0, 519199330857, 2652744333039, 4043121619780, 1859142201351, 271677105452, 6354482628, 0, 0] := by
  rw [show A10K2.u5477 = KTree.node A10K2.t5484 (nat_lit 89314466) (nat_lit 14377112747) (nat_lit 0) A10K2.t5485 from rfl, totK_node, tot5484, tot5485]
  decide +kernel

theorem arows5478 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5478 = true := by
  rw [show A10K2.u5478 = KTree.node A10K2.t5486 (nat_lit 89394288) (nat_lit 14853042636) (nat_lit 0) A10K2.t5487 from rfl, allE_node, rows5486, irow5478, rows5487]
  all_goals rfl

theorem atot5478 : totK PA10K2 A10K2.u5478 = [0, 0, 546645445476, 2665223940827, 4052903470993, 2017397132909, 340462149470, 25371180993, 0, 0] := by
  rw [show A10K2.u5478 = KTree.node A10K2.t5486 (nat_lit 89394288) (nat_lit 14853042636) (nat_lit 0) A10K2.t5487 from rfl, totK_node, tot5486, tot5487]
  decide +kernel

theorem arows5482 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5482 = true := by
  rw [show A10K2.u5482 = KTree.node A10K2.t5488 (nat_lit 89408288) (nat_lit 13255786215) (nat_lit 0) A10K2.t5489 from rfl, allE_node, rows5488, irow5482, rows5489]
  all_goals rfl

theorem atot5482 : totK PA10K2 A10K2.u5482 = [0, 0, 776671970363, 3054315385741, 3821176425104, 1677179807695, 208950295447, 5447185874, 0, 0] := by
  rw [show A10K2.u5482 = KTree.node A10K2.t5488 (nat_lit 89408288) (nat_lit 13255786215) (nat_lit 0) A10K2.t5489 from rfl, totK_node, tot5488, tot5489]
  decide +kernel

theorem arows5483 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5483 = true := by
  rw [show A10K2.u5483 = KTree.node A10K2.t5490 (nat_lit 89414302) (nat_lit 4917852758) (nat_lit 0) A10K2.t5491 from rfl, allE_node, rows5490, irow5483, rows5491]
  all_goals rfl

theorem atot5483 : totK PA10K2 A10K2.u5483 = [0, 0, 536977226750, 2473556448180, 4076851922820, 2139152100478, 301045053897, 6354482628, 0, 0] := by
  rw [show A10K2.u5483 = KTree.node A10K2.t5490 (nat_lit 89414302) (nat_lit 4917852758) (nat_lit 0) A10K2.t5491 from rfl, totK_node, tot5490, tot5491]
  decide +kernel

theorem arows5485 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5485 = true := by
  rw [show A10K2.u5485 = KTree.node A10K2.t5492 (nat_lit 89470221) (nat_lit 5392115312) (nat_lit 0) A10K2.t5493 from rfl, allE_node, rows5492, irow5485, rows5493]
  all_goals rfl

theorem atot5485 : totK PA10K2 A10K2.u5485 = [0, 0, 299266128110, 2016290827207, 3928280352540, 2680918903068, 548521383307, 31452573850, 0, 0] := by
  rw [show A10K2.u5485 = KTree.node A10K2.t5492 (nat_lit 89470221) (nat_lit 5392115312) (nat_lit 0) A10K2.t5493 from rfl, totK_node, tot5492, tot5493]
  decide +kernel

theorem arows5486 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5486 = true := by
  rw [show A10K2.u5486 = KTree.node A10K2.t5494 (nat_lit 89474714) (nat_lit 15100829552) (nat_lit 0) A10K2.t5495 from rfl, allE_node, rows5494, irow5486, rows5495]
  all_goals rfl

theorem atot5486 : totK PA10K2 A10K2.u5486 = [0, 0, 770689108024, 3196539918516, 3988211883031, 1491858147506, 122984762522, 0, 0, 0] := by
  rw [show A10K2.u5486 = KTree.node A10K2.t5494 (nat_lit 89474714) (nat_lit 15100829552) (nat_lit 0) A10K2.t5495 from rfl, totK_node, tot5494, tot5495]
  decide +kernel

theorem arows5489 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5489 = true := by
  rw [show A10K2.u5489 = KTree.node A10K2.t5496 (nat_lit 89482516) (nat_lit 12607056308) (nat_lit 0) A10K2.t5497 from rfl, allE_node, rows5496, irow5489, rows5497]
  all_goals rfl

theorem atot5489 : totK PA10K2 A10K2.u5489 = [0, 0, 554803763168, 2621844465704, 4104068749694, 2141956922164, 281362691578, 6354482628, 0, 0] := by
  rw [show A10K2.u5489 = KTree.node A10K2.t5496 (nat_lit 89482516) (nat_lit 12607056308) (nat_lit 0) A10K2.t5497 from rfl, totK_node, tot5496, tot5497]
  decide +kernel

theorem arows5490 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5490 = true := by
  rw [show A10K2.u5490 = KTree.node A10K2.t5498 (nat_lit 89522461) (nat_lit 6199480913) (nat_lit 0) A10K2.t5499 from rfl, allE_node, rows5498, irow5490, rows5499]
  all_goals rfl

theorem atot5490 : totK PA10K2 A10K2.u5490 = [0, 0, 651079643912, 2761810148574, 3933031176875, 2075725907691, 316124095472, 6962742351, 0, 0] := by
  rw [show A10K2.u5490 = KTree.node A10K2.t5498 (nat_lit 89522461) (nat_lit 6199480913) (nat_lit 0) A10K2.t5499 from rfl, totK_node, tot5498, tot5499]
  decide +kernel

theorem arows5492 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5492 = true := by
  rw [show A10K2.u5492 = KTree.node A10K2.t5500 (nat_lit 89528865) (nat_lit 10026528292) (nat_lit 0) A10K2.t5501 from rfl, allE_node, rows5500, irow5492, rows5501]
  all_goals rfl

theorem atot5492 : totK PA10K2 A10K2.u5492 = [0, 0, 419653836988, 2147116391149, 3863121955952, 2416450723587, 473139398032, 30074883546, 0, 0] := by
  rw [show A10K2.u5492 = KTree.node A10K2.t5500 (nat_lit 89528865) (nat_lit 10026528292) (nat_lit 0) A10K2.t5501 from rfl, totK_node, tot5500, tot5501]
  decide +kernel

theorem arows5493 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5493 = true := by
  rw [show A10K2.u5493 = KTree.node A10K2.t5502 (nat_lit 89535831) (nat_lit 6088281176) (nat_lit 0) A10K2.t5503 from rfl, allE_node, rows5502, irow5493, rows5503]
  all_goals rfl

theorem atot5493 : totK PA10K2 A10K2.u5493 = [0, 0, 331085228475, 2157214638707, 3998152794102, 2534177890441, 487529497735, 31003444686, 0, 0] := by
  rw [show A10K2.u5493 = KTree.node A10K2.t5502 (nat_lit 89535831) (nat_lit 6088281176) (nat_lit 0) A10K2.t5503 from rfl, totK_node, tot5502, tot5503]
  decide +kernel

theorem arows5500 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5500 = true := by
  rw [show A10K2.u5500 = KTree.node A10K2.t5504 (nat_lit 89540311) (nat_lit 8665570653) (nat_lit 0) A10K2.t5505 from rfl, allE_node, rows5504, irow5500, rows5505]
  all_goals rfl

theorem atot5500 : totK PA10K2 A10K2.u5500 = [0, 0, 836002267270, 3310179189332, 3914476526406, 1293669035809, 91878821505, 0, 0, 0] := by
  rw [show A10K2.u5500 = KTree.node A10K2.t5504 (nat_lit 89540311) (nat_lit 8665570653) (nat_lit 0) A10K2.t5505 from rfl, totK_node, tot5504, tot5505]
  decide +kernel

theorem arows5501 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5501 = true := by
  rw [show A10K2.u5501 = KTree.node A10K2.t5506 (nat_lit 89555044) (nat_lit 13017262675) (nat_lit 0) A10K2.t5507 from rfl, allE_node, rows5506, irow5501, rows5507]
  all_goals rfl

theorem atot5501 : totK PA10K2 A10K2.u5501 = [0, 0, 0, 1196748303073, 3948919155567, 3342978198720, 741251095155, 37547833973, 0, 0] := by
  rw [show A10K2.u5501 = KTree.node A10K2.t5506 (nat_lit 89555044) (nat_lit 13017262675) (nat_lit 0) A10K2.t5507 from rfl, totK_node, tot5506, tot5507]
  decide +kernel

theorem arows5503 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5503 = true := by
  rw [show A10K2.u5503 = KTree.node A10K2.t5508 (nat_lit 89565732) (nat_lit 13639823437) (nat_lit 0) A10K2.t5509 from rfl, allE_node, rows5508, irow5503, rows5509]
  all_goals rfl

theorem atot5503 : totK PA10K2 A10K2.u5503 = [0, 0, 0, 1157590868378, 3849247812762, 3449948383613, 827484803207, 56346053544, 0, 0] := by
  rw [show A10K2.u5503 = KTree.node A10K2.t5508 (nat_lit 89565732) (nat_lit 13639823437) (nat_lit 0) A10K2.t5509 from rfl, totK_node, tot5508, tot5509]
  decide +kernel

theorem arows5504 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5504 = true := by
  rw [show A10K2.u5504 = KTree.node A10K2.t5510 (nat_lit 89574244) (nat_lit 13733019683) (nat_lit 0) A10K2.t5511 from rfl, allE_node, rows5510, irow5504, rows5511]
  all_goals rfl

theorem atot5504 : totK PA10K2 A10K2.u5504 = [0, 0, 0, 466179142761, 2599453321023, 4048974739844, 1790434114365, 199528122827, 0, 0] := by
  rw [show A10K2.u5504 = KTree.node A10K2.t5510 (nat_lit 89574244) (nat_lit 13733019683) (nat_lit 0) A10K2.t5511 from rfl, totK_node, tot5510, tot5511]
  decide +kernel

theorem arows5507 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5507 = true := by
  rw [show A10K2.u5507 = KTree.node A10K2.t5512 (nat_lit 89729691) (nat_lit 9948771239) (nat_lit 0) A10K2.t5513 from rfl, allE_node, rows5512, irow5507, rows5513]
  all_goals rfl

theorem atot5507 : totK PA10K2 A10K2.u5507 = [0, 845571698839, 3309864520716, 3938264268450, 1378919417529, 104020221355, 118623104844, 91540553519, 6354482628, 0] := by
  rw [show A10K2.u5507 = KTree.node A10K2.t5512 (nat_lit 89729691) (nat_lit 9948771239) (nat_lit 0) A10K2.t5513 from rfl, totK_node, tot5512, tot5513]
  decide +kernel

theorem arows5508 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5508 = true := by
  rw [show A10K2.u5508 = KTree.node A10K2.t5514 (nat_lit 89734356) (nat_lit 10488371984) (nat_lit 0) A10K2.t5515 from rfl, allE_node, rows5514, irow5508, rows5515]
  all_goals rfl

theorem atot5508 : totK PA10K2 A10K2.u5508 = [0, 499381326354, 2187358385233, 3720200448098, 2666789098712, 588287865385, 31768748853, 0, 0, 0] := by
  rw [show A10K2.u5508 = KTree.node A10K2.t5514 (nat_lit 89734356) (nat_lit 10488371984) (nat_lit 0) A10K2.t5515 from rfl, totK_node, tot5514, tot5515]
  decide +kernel

theorem arows5510 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5510 = true := by
  rw [show A10K2.u5510 = KTree.node A10K2.t5516 (nat_lit 89742092) (nat_lit 11865991505) (nat_lit 0) A10K2.t5517 from rfl, allE_node, rows5516, irow5510, rows5517]
  all_goals rfl

theorem atot5510 : totK PA10K2 A10K2.u5510 = [0, 549295342237, 2794418596075, 4215740874025, 1966991337926, 237409231098, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u5510 = KTree.node A10K2.t5516 (nat_lit 89742092) (nat_lit 11865991505) (nat_lit 0) A10K2.t5517 from rfl, totK_node, tot5516, tot5517]
  decide +kernel

theorem arows5511 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5511 = true := by
  rw [show A10K2.u5511 = KTree.node A10K2.t5518 (nat_lit 89748081) (nat_lit 7504141171) (nat_lit 0) A10K2.t5519 from rfl, allE_node, rows5518, irow5511, rows5519]
  all_goals rfl

theorem atot5511 : totK PA10K2 A10K2.u5511 = [0, 316779408161, 2010815598557, 4212516574077, 3098775588614, 571765991775, 13814447077, 0, 0, 0] := by
  rw [show A10K2.u5511 = KTree.node A10K2.t5518 (nat_lit 89748081) (nat_lit 7504141171) (nat_lit 0) A10K2.t5519 from rfl, totK_node, tot5518, tot5519]
  decide +kernel

theorem arows5515 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5515 = true := by
  rw [show A10K2.u5515 = KTree.node A10K2.t5520 (nat_lit 89761957) (nat_lit 7264329585) (nat_lit 0) A10K2.t5521 from rfl, allE_node, rows5520, irow5515, rows5521]
  all_goals rfl

theorem atot5515 : totK PA10K2 A10K2.u5515 = [0, 0, 844483260375, 3312500804253, 4034303542911, 1481403223982, 103562654595, 0, 0, 0] := by
  rw [show A10K2.u5515 = KTree.node A10K2.t5520 (nat_lit 89761957) (nat_lit 7264329585) (nat_lit 0) A10K2.t5521 from rfl, totK_node, tot5520, tot5521]
  decide +kernel

theorem arows5516 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5516 = true := by
  rw [show A10K2.u5516 = KTree.node A10K2.t5522 (nat_lit 89766684) (nat_lit 11882068508) (nat_lit 0) A10K2.t5523 from rfl, allE_node, rows5522, irow5516, rows5523]
  all_goals rfl

theorem atot5516 : totK PA10K2 A10K2.u5516 = [0, 0, 353585843985, 2056170532375, 3854875149449, 2631347996710, 563447122409, 31082886609, 0, 0] := by
  rw [show A10K2.u5516 = KTree.node A10K2.t5522 (nat_lit 89766684) (nat_lit 11882068508) (nat_lit 0) A10K2.t5523 from rfl, totK_node, tot5522, tot5523]
  decide +kernel

theorem arows5518 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5518 = true := by
  rw [show A10K2.u5518 = KTree.node A10K2.t5524 (nat_lit 89774407) (nat_lit 1177569622) (nat_lit 0) A10K2.t5525 from rfl, allE_node, rows5524, irow5518, rows5525]
  all_goals rfl

theorem atot5518 : totK PA10K2 A10K2.u5518 = [0, 0, 678774051694, 2979778214040, 4065816703830, 1758377542081, 218136913356, 6121173289, 0, 0] := by
  rw [show A10K2.u5518 = KTree.node A10K2.t5524 (nat_lit 89774407) (nat_lit 1177569622) (nat_lit 0) A10K2.t5525 from rfl, totK_node, tot5524, tot5525]
  decide +kernel

theorem arows5519 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5519 = true := by
  rw [show A10K2.u5519 = KTree.node A10K2.t5526 (nat_lit 89850126) (nat_lit 11121130426) (nat_lit 0) A10K2.t5527 from rfl, allE_node, rows5526, irow5519, rows5527]
  all_goals rfl

theorem atot5519 : totK PA10K2 A10K2.u5519 = [0, 593238721492, 2493032781371, 3696749000547, 2517546244406, 773092834571, 61190578067, 0, 0, 0] := by
  rw [show A10K2.u5519 = KTree.node A10K2.t5526 (nat_lit 89850126) (nat_lit 11121130426) (nat_lit 0) A10K2.t5527 from rfl, totK_node, tot5526, tot5527]
  decide +kernel

theorem arows5522 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5522 = true := by
  rw [show A10K2.u5522 = KTree.node A10K2.t5528 (nat_lit 89859283) (nat_lit 10878723544) (nat_lit 0) A10K2.t5529 from rfl, allE_node, rows5528, irow5522, rows5529]
  all_goals rfl

theorem atot5522 : totK PA10K2 A10K2.u5522 = [0, 632810194696, 2663830825063, 3933945042543, 2237261497241, 410857170432, 13360781053, 0, 0, 0] := by
  rw [show A10K2.u5522 = KTree.node A10K2.t5528 (nat_lit 89859283) (nat_lit 10878723544) (nat_lit 0) A10K2.t5529 from rfl, totK_node, tot5528, tot5529]
  decide +kernel

theorem arows5523 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5523 = true := by
  rw [show A10K2.u5523 = KTree.node A10K2.t5530 (nat_lit 89863940) (nat_lit 7884040418) (nat_lit 0) A10K2.t5531 from rfl, allE_node, rows5530, irow5523, rows5531]
  all_goals rfl

theorem atot5523 : totK PA10K2 A10K2.u5523 = [0, 361184257290, 2059203591914, 3990048076351, 2858000433477, 597305747410, 31677228370, 0, 0, 0] := by
  rw [show A10K2.u5523 = KTree.node A10K2.t5530 (nat_lit 89863940) (nat_lit 7884040418) (nat_lit 0) A10K2.t5531 from rfl, totK_node, tot5530, tot5531]
  decide +kernel

theorem arows5525 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5525 = true := by
  rw [show A10K2.u5525 = KTree.node A10K2.t5532 (nat_lit 89877654) (nat_lit 15438790864) (nat_lit 0) A10K2.t5533 from rfl, allE_node, rows5532, irow5525, rows5533]
  all_goals rfl

theorem atot5525 : totK PA10K2 A10K2.u5525 = [0, 658243994560, 2954054711128, 4178528637804, 1917272198666, 272233003136, 6853348008, 0, 0, 0] := by
  rw [show A10K2.u5525 = KTree.node A10K2.t5532 (nat_lit 89877654) (nat_lit 15438790864) (nat_lit 0) A10K2.t5533 from rfl, totK_node, tot5532, tot5533]
  decide +kernel

theorem arows5526 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5526 = true := by
  rw [show A10K2.u5526 = KTree.node A10K2.t5534 (nat_lit 89882171) (nat_lit 5767473894) (nat_lit 0) A10K2.t5535 from rfl, allE_node, rows5534, irow5526, rows5535]
  all_goals rfl

theorem atot5526 : totK PA10K2 A10K2.u5526 = [0, 0, 1084361412648, 3828484211859, 3972494093440, 1153553330523, 69522345625, 0, 0, 0] := by
  rw [show A10K2.u5526 = KTree.node A10K2.t5534 (nat_lit 89882171) (nat_lit 5767473894) (nat_lit 0) A10K2.t5535 from rfl, totK_node, tot5534, tot5535]
  decide +kernel

theorem arows5531 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5531 = true := by
  rw [show A10K2.u5531 = KTree.node A10K2.t5536 (nat_lit 89889804) (nat_lit 9833182774) (nat_lit 0) A10K2.t5537 from rfl, allE_node, rows5536, irow5531, rows5537]
  all_goals rfl

theorem atot5531 : totK PA10K2 A10K2.u5531 = [0, 0, 523331329943, 2582236497695, 4222974827636, 2332155914857, 307606126651, 6904928264, 0, 0] := by
  rw [show A10K2.u5531 = KTree.node A10K2.t5536 (nat_lit 89889804) (nat_lit 9833182774) (nat_lit 0) A10K2.t5537 from rfl, totK_node, tot5536, tot5537]
  decide +kernel

theorem arows5532 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5532 = true := by
  rw [show A10K2.u5532 = KTree.node A10K2.t5538 (nat_lit 89896150) (nat_lit 14738388334) (nat_lit 0) A10K2.t5539 from rfl, allE_node, rows5538, irow5532, rows5539]
  all_goals rfl

theorem atot5532 : totK PA10K2 A10K2.u5532 = [0, 0, 483979057410, 2517239289404, 4183812041035, 2380530502355, 340035582576, 7047025452, 0, 0] := by
  rw [show A10K2.u5532 = KTree.node A10K2.t5538 (nat_lit 89896150) (nat_lit 14738388334) (nat_lit 0) A10K2.t5539 from rfl, totK_node, tot5538, tot5539]
  decide +kernel

theorem arows5534 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5534 = true := by
  rw [show A10K2.u5534 = KTree.node A10K2.t5540 (nat_lit 89910278) (nat_lit 15385015361) (nat_lit 0) A10K2.t5541 from rfl, allE_node, rows5540, irow5534, rows5541]
  all_goals rfl

theorem atot5534 : totK PA10K2 A10K2.u5534 = [0, 0, 761677496734, 3261689837899, 4191942514959, 1611142043754, 125155277211, 0, 0, 0] := by
  rw [show A10K2.u5534 = KTree.node A10K2.t5540 (nat_lit 89910278) (nat_lit 15385015361) (nat_lit 0) A10K2.t5541 from rfl, totK_node, tot5540, tot5541]
  decide +kernel

theorem arows5535 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5535 = true := by
  rw [show A10K2.u5535 = KTree.node A10K2.t5542 (nat_lit 89914865) (nat_lit 8469339006) (nat_lit 0) A10K2.t5543 from rfl, allE_node, rows5542, irow5535, rows5543]
  all_goals rfl

theorem atot5535 : totK PA10K2 A10K2.u5535 = [0, 0, 316661823121, 1763556256950, 3622556765614, 3165090014803, 894120429397, 61110126106, 0, 0] := by
  rw [show A10K2.u5535 = KTree.node A10K2.t5542 (nat_lit 89914865) (nat_lit 8469339006) (nat_lit 0) A10K2.t5543 from rfl, totK_node, tot5542, tot5543]
  decide +kernel

theorem arows5538 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5538 = true := by
  rw [show A10K2.u5538 = KTree.node A10K2.t5544 (nat_lit 89993139) (nat_lit 9302984323) (nat_lit 0) A10K2.t5545 from rfl, allE_node, rows5544, irow5538, rows5545]
  all_goals rfl

theorem atot5538 : totK PA10K2 A10K2.u5538 = [0, 0, 528909875718, 2483854114337, 3922205637319, 2264034577499, 433828195795, 25680132735, 0, 0] := by
  rw [show A10K2.u5538 = KTree.node A10K2.t5544 (nat_lit 89993139) (nat_lit 9302984323) (nat_lit 0) A10K2.t5545 from rfl, totK_node, tot5544, tot5545]
  decide +kernel

theorem arows5539 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5539 = true := by
  rw [show A10K2.u5539 = KTree.node A10K2.t5546 (nat_lit 89999189) (nat_lit 6588886382) (nat_lit 0) A10K2.t5547 from rfl, allE_node, rows5546, irow5539, rows5547]
  all_goals rfl

theorem atot5539 : totK PA10K2 A10K2.u5539 = [0, 0, 561453450670, 2790741380187, 4133440057684, 1979864824816, 252627903566, 5626791703, 0, 0] := by
  rw [show A10K2.u5539 = KTree.node A10K2.t5546 (nat_lit 89999189) (nat_lit 6588886382) (nat_lit 0) A10K2.t5547 from rfl, totK_node, tot5546, tot5547]
  decide +kernel

theorem arows5541 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5541 = true := by
  rw [show A10K2.u5541 = KTree.node A10K2.t5548 (nat_lit 90007002) (nat_lit 14610077557) (nat_lit 0) A10K2.t5549 from rfl, allE_node, rows5548, irow5541, rows5549]
  all_goals rfl

theorem atot5541 : totK PA10K2 A10K2.u5541 = [0, 0, 804002626082, 3100689691588, 4007716155688, 1831982048405, 235645102243, 6239673734, 0, 0] := by
  rw [show A10K2.u5541 = KTree.node A10K2.t5548 (nat_lit 90007002) (nat_lit 14610077557) (nat_lit 0) A10K2.t5549 from rfl, totK_node, tot5548, tot5549]
  decide +kernel

theorem arows5542 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5542 = true := by
  rw [show A10K2.u5542 = KTree.node A10K2.t5550 (nat_lit 90012906) (nat_lit 12028032108) (nat_lit 0) A10K2.t5551 from rfl, allE_node, rows5550, irow5542, rows5551]
  all_goals rfl

theorem atot5542 : totK PA10K2 A10K2.u5542 = [0, 0, 0, 1074956281214, 3916813864022, 3978040295909, 1076203714563, 63421456344, 0, 0] := by
  rw [show A10K2.u5542 = KTree.node A10K2.t5550 (nat_lit 90012906) (nat_lit 12028032108) (nat_lit 0) A10K2.t5551 from rfl, totK_node, tot5550, tot5551]
  decide +kernel

theorem arows5546 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5546 = true := by
  rw [show A10K2.u5546 = KTree.node A10K2.t5552 (nat_lit 90025904) (nat_lit 13007162933) (nat_lit 0) A10K2.t5553 from rfl, allE_node, rows5552, irow5546, rows5553]
  all_goals rfl

theorem atot5546 : totK PA10K2 A10K2.u5546 = [0, 0, 0, 524869949689, 2700578764467, 4153504194536, 2011246924566, 283854156916, 7151180950, 0] := by
  rw [show A10K2.u5546 = KTree.node A10K2.t5552 (nat_lit 90025904) (nat_lit 13007162933) (nat_lit 0) A10K2.t5553 from rfl, totK_node, tot5552, tot5553]
  decide +kernel

theorem arows5547 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5547 = true := by
  rw [show A10K2.u5547 = KTree.node A10K2.t5554 (nat_lit 90038711) (nat_lit 15084722603) (nat_lit 0) A10K2.t5555 from rfl, allE_node, rows5554, irow5547, rows5555]
  all_goals rfl

theorem atot5547 : totK PA10K2 A10K2.u5547 = [0, 0, 0, 1358463729123, 4256065092026, 3548636001724, 798029302945, 42307386006, 0, 0] := by
  rw [show A10K2.u5547 = KTree.node A10K2.t5554 (nat_lit 90038711) (nat_lit 15084722603) (nat_lit 0) A10K2.t5555 from rfl, totK_node, tot5554, tot5555]
  decide +kernel

theorem arows5549 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5549 = true := by
  rw [show A10K2.u5549 = KTree.node A10K2.t5556 (nat_lit 90115507) (nat_lit 8835684311) (nat_lit 0) A10K2.t5557 from rfl, allE_node, rows5556, irow5549, rows5557]
  all_goals rfl

theorem atot5549 : totK PA10K2 A10K2.u5549 = [0, 0, 592737332747, 2565202434707, 3877687102624, 2467811870492, 603607116703, 40355690693, 0, 0] := by
  rw [show A10K2.u5549 = KTree.node A10K2.t5556 (nat_lit 90115507) (nat_lit 8835684311) (nat_lit 0) A10K2.t5557 from rfl, totK_node, tot5556, tot5557]
  decide +kernel

theorem arows5550 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5550 = true := by
  rw [show A10K2.u5550 = KTree.node A10K2.t5558 (nat_lit 90122532) (nat_lit 13845175929) (nat_lit 0) A10K2.t5559 from rfl, allE_node, rows5558, irow5550, rows5559]
  all_goals rfl

theorem atot5550 : totK PA10K2 A10K2.u5550 = [0, 0, 783895901686, 3264790831097, 4158621004419, 1631651995130, 143949651135, 0, 0, 0] := by
  rw [show A10K2.u5550 = KTree.node A10K2.t5558 (nat_lit 90122532) (nat_lit 13845175929) (nat_lit 0) A10K2.t5559 from rfl, totK_node, tot5558, tot5559]
  decide +kernel

theorem arows5553 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5553 = true := by
  rw [show A10K2.u5553 = KTree.node A10K2.t5560 (nat_lit 90127857) (nat_lit 7896861979) (nat_lit 0) A10K2.t5561 from rfl, allE_node, rows5560, irow5553, rows5561]
  all_goals rfl

theorem atot5553 : totK PA10K2 A10K2.u5553 = [0, 0, 538234243656, 2453542518574, 3959959967328, 2493110559387, 435589932154, 12219140272, 0, 0] := by
  rw [show A10K2.u5553 = KTree.node A10K2.t5560 (nat_lit 90127857) (nat_lit 7896861979) (nat_lit 0) A10K2.t5561 from rfl, totK_node, tot5560, tot5561]
  decide +kernel

theorem arows5554 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5554 = true := by
  rw [show A10K2.u5554 = KTree.node A10K2.t5562 (nat_lit 90141111) (nat_lit 15084722603) (nat_lit 0) A10K2.t5563 from rfl, allE_node, rows5562, irow5554, rows5563]
  all_goals rfl

theorem atot5554 : totK PA10K2 A10K2.u5554 = [0, 0, 329115212409, 2086441617418, 4184881810941, 2941707526911, 500063871652, 13653259670, 0, 0] := by
  rw [show A10K2.u5554 = KTree.node A10K2.t5562 (nat_lit 90141111) (nat_lit 15084722603) (nat_lit 0) A10K2.t5563 from rfl, totK_node, tot5562, tot5563]
  decide +kernel

theorem arows5556 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5556 = true := by
  rw [show A10K2.u5556 = KTree.node A10K2.t5564 (nat_lit 92275501) (nat_lit 6534279636) (nat_lit 0) A10K2.t5565 from rfl, allE_node, rows5564, irow5556, rows5565]
  all_goals rfl

theorem atot5556 : totK PA10K2 A10K2.u5556 = [0, 845543753839, 2932463804465, 2959464788535, 1370016388779, 1118804348728, 509383549815, 49180423016, 0, 0] := by
  rw [show A10K2.u5556 = KTree.node A10K2.t5564 (nat_lit 92275501) (nat_lit 6534279636) (nat_lit 0) A10K2.t5565 from rfl, totK_node, tot5564, tot5565]
  decide +kernel

theorem arows5557 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5557 = true := by
  rw [show A10K2.u5557 = KTree.node A10K2.t5566 (nat_lit 92281061) (nat_lit 7046136024) (nat_lit 0) A10K2.t5567 from rfl, allE_node, rows5566, irow5557, rows5567]
  all_goals rfl

theorem atot5557 : totK PA10K2 A10K2.u5557 = [0, 292130592925, 1877553633403, 3892858044577, 2806158737178, 579242973996, 30831673886, 0, 0, 0] := by
  rw [show A10K2.u5557 = KTree.node A10K2.t5566 (nat_lit 92281061) (nat_lit 7046136024) (nat_lit 0) A10K2.t5567 from rfl, totK_node, tot5566, tot5567]
  decide +kernel

theorem arows5563 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5563 = true := by
  rw [show A10K2.u5563 = KTree.node A10K2.t5568 (nat_lit 92293790) (nat_lit 4996906601) (nat_lit 0) A10K2.t5569 from rfl, allE_node, rows5568, irow5563, rows5569]
  all_goals rfl

theorem atot5563 : totK PA10K2 A10K2.u5563 = [0, 455179774352, 2572480543187, 4237114073969, 1940687633515, 180021466785, 0, 0, 0, 0] := by
  rw [show A10K2.u5563 = KTree.node A10K2.t5568 (nat_lit 92293790) (nat_lit 4996906601) (nat_lit 0) A10K2.t5569 from rfl, totK_node, tot5568, tot5569]
  decide +kernel

theorem arows5564 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5564 = true := by
  rw [show A10K2.u5564 = KTree.node A10K2.t5570 (nat_lit 92302513) (nat_lit 6804465152) (nat_lit 0) A10K2.t5571 from rfl, allE_node, rows5570, irow5564, rows5571]
  all_goals rfl

theorem atot5564 : totK PA10K2 A10K2.u5564 = [0, 625789152892, 2605558662939, 3832993663664, 2365367306544, 447163943930, 13207830636, 0, 0, 0] := by
  rw [show A10K2.u5564 = KTree.node A10K2.t5570 (nat_lit 92302513) (nat_lit 6804465152) (nat_lit 0) A10K2.t5571 from rfl, totK_node, tot5570, tot5571]
  decide +kernel

theorem arows5566 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5566 = true := by
  rw [show A10K2.u5566 = KTree.node A10K2.t5572 (nat_lit 92307954) (nat_lit 11539759144) (nat_lit 0) A10K2.t5573 from rfl, allE_node, rows5572, irow5566, rows5573]
  all_goals rfl

theorem atot5566 : totK PA10K2 A10K2.u5566 = [0, 0, 1113731594504, 3806972647198, 3726907533512, 1025196157789, 67007577595, 0, 0, 0] := by
  rw [show A10K2.u5566 = KTree.node A10K2.t5572 (nat_lit 92307954) (nat_lit 11539759144) (nat_lit 0) A10K2.t5573 from rfl, totK_node, tot5572, tot5573]
  decide +kernel

theorem arows5567 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5567 = true := by
  rw [show A10K2.u5567 = KTree.node A10K2.t5574 (nat_lit 92313635) (nat_lit 6513735025) (nat_lit 0) A10K2.t5575 from rfl, allE_node, rows5574, irow5567, rows5575]
  all_goals rfl

theorem atot5567 : totK PA10K2 A10K2.u5567 = [0, 0, 335936265880, 2004235849291, 3858710458548, 2614301895620, 549802920840, 30650496230, 0, 0] := by
  rw [show A10K2.u5567 = KTree.node A10K2.t5574 (nat_lit 92313635) (nat_lit 6513735025) (nat_lit 0) A10K2.t5575 from rfl, totK_node, tot5574, tot5575]
  decide +kernel

theorem arows5570 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5570 = true := by
  rw [show A10K2.u5570 = KTree.node A10K2.t5576 (nat_lit 92326437) (nat_lit 7293157351) (nat_lit 0) A10K2.t5577 from rfl, allE_node, rows5576, irow5570, rows5577]
  all_goals rfl

theorem atot5570 : totK PA10K2 A10K2.u5570 = [0, 0, 453883021376, 2706639531583, 4339745643514, 1715325031727, 129769859185, 0, 0, 0] := by
  rw [show A10K2.u5570 = KTree.node A10K2.t5576 (nat_lit 92326437) (nat_lit 7293157351) (nat_lit 0) A10K2.t5577 from rfl, totK_node, tot5576, tot5577]
  decide +kernel

theorem arows5571 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5571 = true := by
  rw [show A10K2.u5571 = KTree.node A10K2.t5578 (nat_lit 92335518) (nat_lit 15676680037) (nat_lit 0) A10K2.t5579 from rfl, allE_node, rows5578, irow5571, rows5579]
  all_goals rfl

theorem atot5571 : totK PA10K2 A10K2.u5571 = [0, 345421315675, 1778329642468, 3489011331208, 2980060067059, 1117750701120, 157955897687, 5546304973, 0, 0] := by
  rw [show A10K2.u5571 = KTree.node A10K2.t5578 (nat_lit 92335518) (nat_lit 15676680037) (nat_lit 0) A10K2.t5579 from rfl, totK_node, tot5578, tot5579]
  decide +kernel

theorem arows5573 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5573 = true := by
  rw [show A10K2.u5573 = KTree.node A10K2.t5580 (nat_lit 92409907) (nat_lit 3297056772) (nat_lit 0) A10K2.t5581 from rfl, allE_node, rows5580, irow5573, rows5581]
  all_goals rfl

theorem atot5573 : totK PA10K2 A10K2.u5573 = [0, 433354746640, 2260631857963, 3918468817646, 2442315622366, 463149194459, 25371180993, 0, 0, 0] := by
  rw [show A10K2.u5573 = KTree.node A10K2.t5580 (nat_lit 92409907) (nat_lit 3297056772) (nat_lit 0) A10K2.t5581 from rfl, totK_node, tot5580, tot5581]
  decide +kernel

theorem arows5574 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5574 = true := by
  rw [show A10K2.u5574 = KTree.node A10K2.t5582 (nat_lit 92416213) (nat_lit 6347289791) (nat_lit 0) A10K2.t5583 from rfl, allE_node, rows5582, irow5574, rows5583]
  all_goals rfl

theorem atot5574 : totK PA10K2 A10K2.u5574 = [0, 558446574997, 2571538425647, 3799390137146, 2138920424751, 475132846271, 31195026185, 0, 0, 0] := by
  rw [show A10K2.u5574 = KTree.node A10K2.t5582 (nat_lit 92416213) (nat_lit 6347289791) (nat_lit 0) A10K2.t5583 from rfl, totK_node, tot5582, tot5583]
  decide +kernel

theorem arows5578 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5578 = true := by
  rw [show A10K2.u5578 = KTree.node A10K2.t5584 (nat_lit 92423054) (nat_lit 12864952470) (nat_lit 0) A10K2.t5585 from rfl, allE_node, rows5584, irow5578, rows5585]
  all_goals rfl

theorem atot5578 : totK PA10K2 A10K2.u5578 = [0, 820244515340, 3080608491276, 3687081015376, 1657114533599, 228422066303, 6034215561, 0, 0, 0] := by
  rw [show A10K2.u5578 = KTree.node A10K2.t5584 (nat_lit 92423054) (nat_lit 12864952470) (nat_lit 0) A10K2.t5585 from rfl, totK_node, tot5584, tot5585]
  decide +kernel

theorem arows5579 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5579 = true := by
  rw [show A10K2.u5579 = KTree.node A10K2.t5586 (nat_lit 92428629) (nat_lit 6970753704) (nat_lit 0) A10K2.t5587 from rfl, allE_node, rows5586, irow5579, rows5587]
  all_goals rfl

theorem atot5579 : totK PA10K2 A10K2.u5579 = [0, 0, 1403331125375, 4177792848319, 3249337466627, 650887208797, 31987755669, 0, 0, 0] := by
  rw [show A10K2.u5579 = KTree.node A10K2.t5586 (nat_lit 92428629) (nat_lit 6970753704) (nat_lit 0) A10K2.t5587 from rfl, totK_node, tot5586, tot5587]
  decide +kernel

theorem arows5581 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5581 = true := by
  rw [show A10K2.u5581 = KTree.node A10K2.t5588 (nat_lit 92448154) (nat_lit 15023698103) (nat_lit 0) A10K2.t5589 from rfl, allE_node, rows5588, irow5581, rows5589]
  all_goals rfl

theorem atot5581 : totK PA10K2 A10K2.u5581 = [0, 0, 1004113955614, 3707569819989, 3818620418422, 987180626976, 45620856191, 0, 0, 0] := by
  rw [show A10K2.u5581 = KTree.node A10K2.t5588 (nat_lit 92448154) (nat_lit 15023698103) (nat_lit 0) A10K2.t5589 from rfl, totK_node, tot5588, tot5589]
  decide +kernel

theorem arows5582 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5582 = true := by
  rw [show A10K2.u5582 = KTree.node A10K2.t5590 (nat_lit 92457030) (nat_lit 11055069919) (nat_lit 0) A10K2.t5591 from rfl, allE_node, rows5590, irow5582, rows5591]
  all_goals rfl

theorem atot5582 : totK PA10K2 A10K2.u5582 = [0, 0, 670269767058, 3142257117159, 4067328037199, 1354492478368, 108770940573, 0, 0, 0] := by
  rw [show A10K2.u5582 = KTree.node A10K2.t5590 (nat_lit 92457030) (nat_lit 11055069919) (nat_lit 0) A10K2.t5591 from rfl, totK_node, tot5590, tot5591]
  decide +kernel

theorem arows5585 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5585 = true := by
  rw [show A10K2.u5585 = KTree.node A10K2.t5592 (nat_lit 92471914) (nat_lit 3685074547) (nat_lit 0) A10K2.t5593 from rfl, allE_node, rows5592, irow5585, rows5593]
  all_goals rfl

theorem atot5585 : totK PA10K2 A10K2.u5585 = [0, 770688507529, 2743516325288, 3137673252488, 1882725448293, 940564262609, 207269719194, 6354482628, 0, 0] := by
  rw [show A10K2.u5585 = KTree.node A10K2.t5592 (nat_lit 92471914) (nat_lit 3685074547) (nat_lit 0) A10K2.t5593 from rfl, totK_node, tot5592, tot5593]
  decide +kernel

theorem arows5586 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5586 = true := by
  rw [show A10K2.u5586 = KTree.node A10K2.t5594 (nat_lit 92478214) (nat_lit 8274133015) (nat_lit 0) A10K2.t5595 from rfl, allE_node, rows5594, irow5586, rows5595]
  all_goals rfl

theorem atot5586 : totK PA10K2 A10K2.u5586 = [0, 390797214289, 2090236278034, 3976468189785, 2758187401504, 577844437080, 30810868011, 0, 0, 0] := by
  rw [show A10K2.u5586 = KTree.node A10K2.t5594 (nat_lit 92478214) (nat_lit 8274133015) (nat_lit 0) A10K2.t5595 from rfl, totK_node, tot5594, tot5595]
  decide +kernel

theorem arows5588 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5588 = true := by
  rw [show A10K2.u5588 = KTree.node A10K2.t5596 (nat_lit 92500592) (nat_lit 14521993959) (nat_lit 0) A10K2.t5597 from rfl, allE_node, rows5596, irow5588, rows5597]
  all_goals rfl

theorem atot5588 : totK PA10K2 A10K2.u5588 = [0, 202896141557, 1814381720109, 4207208233119, 3148697895528, 657469941437, 32380877673, 0, 0, 0] := by
  rw [show A10K2.u5588 = KTree.node A10K2.t5596 (nat_lit 92500592) (nat_lit 14521993959) (nat_lit 0) A10K2.t5597 from rfl, totK_node, tot5596, tot5597]
  decide +kernel

theorem arows5589 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5589 = true := by
  rw [show A10K2.u5589 = KTree.node A10K2.t5598 (nat_lit 92508169) (nat_lit 9807832142) (nat_lit 0) A10K2.t5599 from rfl, allE_node, rows5598, irow5589, rows5599]
  all_goals rfl

theorem atot5589 : totK PA10K2 A10K2.u5589 = [0, 0, 464509768748, 2521018270717, 4276268303294, 2253066073620, 296470857942, 6904928264, 0, 0] := by
  rw [show A10K2.u5589 = KTree.node A10K2.t5598 (nat_lit 92508169) (nat_lit 9807832142) (nat_lit 0) A10K2.t5599 from rfl, totK_node, tot5598, tot5599]
  decide +kernel

theorem arows5594 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5594 = true := by
  rw [show A10K2.u5594 = KTree.node A10K2.t5600 (nat_lit 92532370) (nat_lit 15544065974) (nat_lit 0) A10K2.t5601 from rfl, allE_node, rows5600, irow5594, rows5601]
  all_goals rfl

theorem atot5594 : totK PA10K2 A10K2.u5594 = [0, 0, 593115420863, 2758612009795, 4201359248390, 2217703334433, 271247895482, 6066958478, 0, 0] := by
  rw [show A10K2.u5594 = KTree.node A10K2.t5600 (nat_lit 92532370) (nat_lit 15544065974) (nat_lit 0) A10K2.t5601 from rfl, totK_node, tot5600, tot5601]
  decide +kernel

theorem arows5595 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5595 = true := by
  rw [show A10K2.u5595 = KTree.node A10K2.t5602 (nat_lit 92539434) (nat_lit 7690534960) (nat_lit 0) A10K2.t5603 from rfl, allE_node, rows5602, irow5595, rows5603]
  all_goals rfl

theorem atot5595 : totK PA10K2 A10K2.u5595 = [0, 0, 842999727690, 3320473072445, 3922419659110, 1373544829081, 115286297843, 0, 0, 0] := by
  rw [show A10K2.u5595 = KTree.node A10K2.t5602 (nat_lit 92539434) (nat_lit 7690534960) (nat_lit 0) A10K2.t5603 from rfl, totK_node, tot5602, tot5603]
  decide +kernel

theorem arows5597 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5597 = true := by
  rw [show A10K2.u5597 = KTree.node A10K2.t5604 (nat_lit 92544191) (nat_lit 14089911145) (nat_lit 0) A10K2.t5605 from rfl, allE_node, rows5604, irow5597, rows5605]
  all_goals rfl

theorem atot5597 : totK PA10K2 A10K2.u5597 = [0, 0, 461371995414, 2222947459226, 3752917327188, 2441173646067, 534206212347, 30831673886, 0, 0] := by
  rw [show A10K2.u5597 = KTree.node A10K2.t5604 (nat_lit 92544191) (nat_lit 14089911145) (nat_lit 0) A10K2.t5605 from rfl, totK_node, tot5604, tot5605]
  decide +kernel

theorem arows5598 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5598 = true := by
  rw [show A10K2.u5598 = KTree.node A10K2.t5606 (nat_lit 92558572) (nat_lit 11421021769) (nat_lit 0) A10K2.t5607 from rfl, allE_node, rows5606, irow5598, rows5607]
  all_goals rfl

theorem atot5598 : totK PA10K2 A10K2.u5598 = [0, 0, 578061788812, 2679318667261, 3992747255243, 1851699982585, 212058150804, 5705019915, 0, 0] := by
  rw [show A10K2.u5598 = KTree.node A10K2.t5606 (nat_lit 92558572) (nat_lit 11421021769) (nat_lit 0) A10K2.t5607 from rfl, totK_node, tot5606, tot5607]
  decide +kernel

theorem arows5601 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5601 = true := by
  rw [show A10K2.u5601 = KTree.node A10K2.t5608 (nat_lit 92565610) (nat_lit 3237625045) (nat_lit 0) A10K2.t5609 from rfl, allE_node, rows5608, irow5601, rows5609]
  all_goals rfl

theorem atot5601 : totK PA10K2 A10K2.u5601 = [0, 0, 332048780867, 2290446845757, 4448059706701, 2591229197717, 348718298985, 6853348008, 0, 0] := by
  rw [show A10K2.u5601 = KTree.node A10K2.t5608 (nat_lit 92565610) (nat_lit 3237625045) (nat_lit 0) A10K2.t5609 from rfl, totK_node, tot5608, tot5609]
  decide +kernel

theorem arows5602 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5602 = true := by
  rw [show A10K2.u5602 = KTree.node A10K2.t5610 (nat_lit 92572854) (nat_lit 16299434441) (nat_lit 0) A10K2.t5611 from rfl, allE_node, rows5610, irow5602, rows5611]
  all_goals rfl

theorem atot5602 : totK PA10K2 A10K2.u5602 = [0, 0, 0, 580782566641, 2793099793717, 3907150875357, 1828839366154, 331409082613, 25239774317, 0] := by
  rw [show A10K2.u5602 = KTree.node A10K2.t5610 (nat_lit 92572854) (nat_lit 16299434441) (nat_lit 0) A10K2.t5611 from rfl, totK_node, tot5610, tot5611]
  decide +kernel

theorem arows5604 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5604 = true := by
  rw [show A10K2.u5604 = KTree.node A10K2.t5612 (nat_lit 92586788) (nat_lit 13928628647) (nat_lit 0) A10K2.t5613 from rfl, allE_node, rows5612, irow5604, rows5613]
  all_goals rfl

theorem atot5604 : totK PA10K2 A10K2.u5604 = [0, 0, 0, 737146113695, 3118557633629, 3735894649341, 1378346951008, 179663746211, 5365973533, 0] := by
  rw [show A10K2.u5604 = KTree.node A10K2.t5612 (nat_lit 92586788) (nat_lit 13928628647) (nat_lit 0) A10K2.t5613 from rfl, totK_node, tot5612, tot5613]
  decide +kernel

theorem arows5605 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5605 = true := by
  rw [show A10K2.u5605 = KTree.node A10K2.t5614 (nat_lit 92594282) (nat_lit 3134791679) (nat_lit 0) A10K2.t5615 from rfl, allE_node, rows5614, irow5605, rows5615]
  all_goals rfl

theorem atot5605 : totK PA10K2 A10K2.u5605 = [0, 0, 304573652302, 1377356373392, 2818503746511, 3308527567667, 1473471520249, 198525315368, 5528811039, 0] := by
  rw [show A10K2.u5605 = KTree.node A10K2.t5614 (nat_lit 92594282) (nat_lit 3134791679) (nat_lit 0) A10K2.t5615 from rfl, totK_node, tot5614, tot5615]
  decide +kernel

theorem arows5609 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5609 = true := by
  rw [show A10K2.u5609 = KTree.node A10K2.t5616 (nat_lit 92671419) (nat_lit 2191276314) (nat_lit 0) A10K2.t5617 from rfl, allE_node, rows5616, irow5609, rows5617]
  all_goals rfl

theorem atot5609 : totK PA10K2 A10K2.u5609 = [0, 0, 474026294606, 2547517416484, 4053885493201, 2108024489815, 373656102339, 25371180993, 0, 0] := by
  rw [show A10K2.u5609 = KTree.node A10K2.t5616 (nat_lit 92671419) (nat_lit 2191276314) (nat_lit 0) A10K2.t5617 from rfl, totK_node, tot5616, tot5617]
  decide +kernel

theorem arows5610 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5610 = true := by
  rw [show A10K2.u5610 = KTree.node A10K2.t5618 (nat_lit 92677910) (nat_lit 10964562729) (nat_lit 0) A10K2.t5619 from rfl, allE_node, rows5618, irow5610, rows5619]
  all_goals rfl

theorem atot5610 : totK PA10K2 A10K2.u5610 = [0, 0, 558195267532, 2674486547237, 4070741122801, 1935064342131, 229806880557, 5460492893, 0, 0] := by
  rw [show A10K2.u5610 = KTree.node A10K2.t5618 (nat_lit 92677910) (nat_lit 10964562729) (nat_lit 0) A10K2.t5619 from rfl, totK_node, tot5618, tot5619]
  decide +kernel

theorem arows5612 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5612 = true := by
  rw [show A10K2.u5612 = KTree.node A10K2.t5620 (nat_lit 92685196) (nat_lit 8644543329) (nat_lit 0) A10K2.t5621 from rfl, allE_node, rows5620, irow5612, rows5621]
  all_goals rfl

theorem atot5612 : totK PA10K2 A10K2.u5612 = [0, 0, 819545818442, 3070919012240, 3673425118928, 1576196399878, 219459889582, 6034215561, 0, 0] := by
  rw [show A10K2.u5612 = KTree.node A10K2.t5620 (nat_lit 92685196) (nat_lit 8644543329) (nat_lit 0) A10K2.t5621 from rfl, totK_node, tot5620, tot5621]
  decide +kernel

theorem arows5613 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5613 = true := by
  rw [show A10K2.u5613 = KTree.node A10K2.t5622 (nat_lit 92690785) (nat_lit 8876587849) (nat_lit 0) A10K2.t5623 from rfl, allE_node, rows5622, irow5613, rows5623]
  all_goals rfl

theorem atot5613 : totK PA10K2 A10K2.u5613 = [0, 0, 0, 1396711468396, 4208472813944, 3125030143190, 610668569162, 31987755669, 0, 0] := by
  rw [show A10K2.u5613 = KTree.node A10K2.t5622 (nat_lit 92690785) (nat_lit 8876587849) (nat_lit 0) A10K2.t5623 from rfl, totK_node, tot5622, tot5623]
  decide +kernel

theorem arows5616 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5616 = true := by
  rw [show A10K2.u5616 = KTree.node A10K2.t5624 (nat_lit 92710918) (nat_lit 8585469506) (nat_lit 0) A10K2.t5625 from rfl, allE_node, rows5624, irow5616, rows5625]
  all_goals rfl

theorem atot5616 : totK PA10K2 A10K2.u5616 = [0, 0, 0, 1130134118249, 3932550634098, 3562784440009, 730577824051, 38471704398, 0, 0] := by
  rw [show A10K2.u5616 = KTree.node A10K2.t5624 (nat_lit 92710918) (nat_lit 8585469506) (nat_lit 0) A10K2.t5625 from rfl, totK_node, tot5624, tot5625]
  decide +kernel

theorem arows5617 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5617 = true := by
  rw [show A10K2.u5617 = KTree.node A10K2.t5626 (nat_lit 92719914) (nat_lit 11754173865) (nat_lit 0) A10K2.t5627 from rfl, allE_node, rows5626, irow5617, rows5627]
  all_goals rfl

theorem atot5617 : totK PA10K2 A10K2.u5617 = [0, 0, 27745223503, 553708377651, 2756800150367, 3933372965432, 1649630838300, 203613753835, 5676195732, 0] := by
  rw [show A10K2.u5617 = KTree.node A10K2.t5626 (nat_lit 92719914) (nat_lit 11754173865) (nat_lit 0) A10K2.t5627 from rfl, totK_node, tot5626, tot5627]
  decide +kernel

theorem arows5619 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5619 = true := by
  rw [show A10K2.u5619 = KTree.node A10K2.t5628 (nat_lit 92736526) (nat_lit 14594430816) (nat_lit 0) A10K2.t5629 from rfl, allE_node, rows5628, irow5619, rows5629]
  all_goals rfl

theorem atot5619 : totK PA10K2 A10K2.u5619 = [0, 0, 724887399103, 3086422322913, 3959749289322, 1720655194416, 264852921966, 20058242317, 0, 0] := by
  rw [show A10K2.u5619 = KTree.node A10K2.t5628 (nat_lit 92736526) (nat_lit 14594430816) (nat_lit 0) A10K2.t5629 from rfl, totK_node, tot5628, tot5629]
  decide +kernel

theorem arows5620 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5620 = true := by
  rw [show A10K2.u5620 = KTree.node A10K2.t5630 (nat_lit 92758627) (nat_lit 980510732) (nat_lit 0) A10K2.t5631 from rfl, allE_node, rows5630, irow5620, rows5631]
  all_goals rfl

theorem atot5620 : totK PA10K2 A10K2.u5620 = [0, 0, 592748306228, 2833428386896, 4329477579666, 2054508177795, 206277469121, 0, 0, 0] := by
  rw [show A10K2.u5620 = KTree.node A10K2.t5630 (nat_lit 92758627) (nat_lit 980510732) (nat_lit 0) A10K2.t5631 from rfl, totK_node, tot5630, tot5631]
  decide +kernel

theorem arows5629 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5629 = true := by
  rw [show A10K2.u5629 = KTree.node A10K2.t5632 (nat_lit 92874395) (nat_lit 10048540901) (nat_lit 0) A10K2.t5633 from rfl, allE_node, rows5632, irow5629, rows5633]
  all_goals rfl

theorem atot5629 : totK PA10K2 A10K2.u5629 = [0, 816677920148, 2666040662324, 2873661883949, 2012822739343, 1267879456639, 248448880970, 6853348008, 0, 0] := by
  rw [show A10K2.u5629 = KTree.node A10K2.t5632 (nat_lit 92874395) (nat_lit 10048540901) (nat_lit 0) A10K2.t5633 from rfl, totK_node, tot5632, tot5633]
  decide +kernel

theorem arows5630 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5630 = true := by
  rw [show A10K2.u5630 = KTree.node A10K2.t5634 (nat_lit 92878782) (nat_lit 15278244843) (nat_lit 0) A10K2.t5635 from rfl, allE_node, rows5634, irow5630, rows5635]
  all_goals rfl

theorem atot5630 : totK PA10K2 A10K2.u5630 = [0, 186012126271, 1739544748750, 3965530487002, 3011992291435, 620538417593, 31768748853, 0, 0, 0] := by
  rw [show A10K2.u5630 = KTree.node A10K2.t5634 (nat_lit 92878782) (nat_lit 15278244843) (nat_lit 0) A10K2.t5635 from rfl, totK_node, tot5634, tot5635]
  decide +kernel

theorem arows5632 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5632 = true := by
  rw [show A10K2.u5632 = KTree.node A10K2.t5636 (nat_lit 92883200) (nat_lit 12484028996) (nat_lit 0) A10K2.t5637 from rfl, allE_node, rows5636, irow5632, rows5637]
  all_goals rfl

theorem atot5632 : totK PA10K2 A10K2.u5632 = [0, 579135734717, 2900897374855, 4193924484769, 1697628783030, 139032749336, 0, 0, 0, 0] := by
  rw [show A10K2.u5632 = KTree.node A10K2.t5636 (nat_lit 92883200) (nat_lit 12484028996) (nat_lit 0) A10K2.t5637 from rfl, totK_node, tot5636, tot5637]
  decide +kernel

theorem arows5633 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5633 = true := by
  rw [show A10K2.u5633 = KTree.node A10K2.t5638 (nat_lit 92890977) (nat_lit 4421769672) (nat_lit 0) A10K2.t5639 from rfl, allE_node, rows5638, irow5633, rows5639]
  all_goals rfl

theorem atot5633 : totK PA10K2 A10K2.u5633 = [0, 628467226016, 2745463832630, 4088409387763, 2173790385795, 316468101558, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u5633 = KTree.node A10K2.t5638 (nat_lit 92890977) (nat_lit 4421769672) (nat_lit 0) A10K2.t5639 from rfl, totK_node, tot5638, tot5639]
  decide +kernel

theorem arows5636 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5636 = true := by
  rw [show A10K2.u5636 = KTree.node A10K2.t5640 (nat_lit 92906771) (nat_lit 10823858322) (nat_lit 0) A10K2.t5641 from rfl, allE_node, rows5640, irow5636, rows5641]
  all_goals rfl

theorem atot5636 : totK PA10K2 A10K2.u5636 = [0, 0, 895393159533, 3557399797260, 4028577154053, 1216902668000, 75394373957, 0, 0, 0] := by
  rw [show A10K2.u5636 = KTree.node A10K2.t5640 (nat_lit 92906771) (nat_lit 10823858322) (nat_lit 0) A10K2.t5641 from rfl, totK_node, tot5640, tot5641]
  decide +kernel

theorem arows5637 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5637 = true := by
  rw [show A10K2.u5637 = KTree.node A10K2.t5642 (nat_lit 92911322) (nat_lit 13971053593) (nat_lit 0) A10K2.t5643 from rfl, allE_node, rows5642, irow5637, rows5643]
  all_goals rfl

theorem atot5637 : totK PA10K2 A10K2.u5637 = [0, 0, 319590198939, 1940832538027, 3887290061376, 2732956896471, 567727731755, 31082886609, 0, 0] := by
  rw [show A10K2.u5637 = KTree.node A10K2.t5642 (nat_lit 92911322) (nat_lit 13971053593) (nat_lit 0) A10K2.t5643 from rfl, totK_node, tot5642, tot5643]
  decide +kernel

theorem arows5639 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5639 = true := by
  rw [show A10K2.u5639 = KTree.node A10K2.t5644 (nat_lit 92915873) (nat_lit 8088243184) (nat_lit 0) A10K2.t5645 from rfl, allE_node, rows5644, irow5639, rows5645]
  all_goals rfl

theorem atot5639 : totK PA10K2 A10K2.u5639 = [0, 0, 674495185239, 3090736655754, 4109856191142, 1433881266237, 89010550227, 0, 0, 0] := by
  rw [show A10K2.u5639 = KTree.node A10K2.t5644 (nat_lit 92915873) (nat_lit 8088243184) (nat_lit 0) A10K2.t5645 from rfl, totK_node, tot5644, tot5645]
  decide +kernel

theorem arows5640 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5640 = true := by
  rw [show A10K2.u5640 = KTree.node A10K2.t5646 (nat_lit 92923666) (nat_lit 15138099196) (nat_lit 0) A10K2.t5647 from rfl, allE_node, rows5646, irow5640, rows5647]
  all_goals rfl

theorem atot5640 : totK PA10K2 A10K2.u5640 = [0, 273815470041, 1321584210068, 2897559027361, 3404441142084, 1640912021265, 225186928940, 6121173289, 0, 0] := by
  rw [show A10K2.u5640 = KTree.node A10K2.t5646 (nat_lit 92923666) (nat_lit 15138099196) (nat_lit 0) A10K2.t5647 from rfl, totK_node, tot5646, tot5647]
  decide +kernel

theorem arows5644 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5644 = true := by
  rw [show A10K2.u5644 = KTree.node A10K2.t5648 (nat_lit 92934469) (nat_lit 6569926694) (nat_lit 0) A10K2.t5649 from rfl, allE_node, rows5648, irow5644, rows5649]
  all_goals rfl

theorem atot5644 : totK PA10K2 A10K2.u5644 = [0, 398950871247, 2185119645094, 3861469396748, 2450829439803, 502221087962, 30831673886, 0, 0, 0] := by
  rw [show A10K2.u5644 = KTree.node A10K2.t5648 (nat_lit 92934469) (nat_lit 6569926694) (nat_lit 0) A10K2.t5649 from rfl, totK_node, tot5648, tot5649]
  decide +kernel

theorem arows5645 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5645 = true := by
  rw [show A10K2.u5645 = KTree.node A10K2.t5650 (nat_lit 92941152) (nat_lit 10947380688) (nat_lit 0) A10K2.t5651 from rfl, allE_node, rows5650, irow5645, rows5651]
  all_goals rfl

theorem atot5645 : totK PA10K2 A10K2.u5645 = [0, 657152906540, 2851168495966, 3915305995005, 1960103468394, 356938100743, 20340910120, 0, 0, 0] := by
  rw [show A10K2.u5645 = KTree.node A10K2.t5650 (nat_lit 92941152) (nat_lit 10947380688) (nat_lit 0) A10K2.t5651 from rfl, totK_node, tot5650, tot5651]
  decide +kernel

theorem arows5647 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5647 = true := by
  rw [show A10K2.u5647 = KTree.node A10K2.t5652 (nat_lit 92946772) (nat_lit 13026333276) (nat_lit 0) A10K2.t5653 from rfl, allE_node, rows5652, irow5647, rows5653]
  all_goals rfl

theorem atot5647 : totK PA10K2 A10K2.u5647 = [0, 608194195297, 2596008032301, 3841485399655, 2133317002157, 331139772202, 11427838733, 0, 0, 0] := by
  rw [show A10K2.u5647 = KTree.node A10K2.t5652 (nat_lit 92946772) (nat_lit 13026333276) (nat_lit 0) A10K2.t5653 from rfl, totK_node, tot5652, tot5653]
  decide +kernel

theorem arows5648 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5648 = true := by
  rw [show A10K2.u5648 = KTree.node A10K2.t5654 (nat_lit 92952018) (nat_lit 15049581016) (nat_lit 0) A10K2.t5655 from rfl, allE_node, rows5654, irow5648, rows5655]
  all_goals rfl

theorem atot5648 : totK PA10K2 A10K2.u5648 = [0, 196962003141, 1951186023582, 4183377794893, 2637192704415, 455505789199, 21329223247, 0, 0, 0] := by
  rw [show A10K2.u5648 = KTree.node A10K2.t5654 (nat_lit 92952018) (nat_lit 15049581016) (nat_lit 0) A10K2.t5655 from rfl, totK_node, tot5654, tot5655]
  decide +kernel

theorem arows5651 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5651 = true := by
  rw [show A10K2.u5651 = KTree.node A10K2.t5656 (nat_lit 92972531) (nat_lit 9023718657) (nat_lit 0) A10K2.t5657 from rfl, allE_node, rows5656, irow5651, rows5657]
  all_goals rfl

theorem atot5651 : totK PA10K2 A10K2.u5651 = [0, 0, 1062004307046, 3752730991070, 3798142703575, 970238575572, 49484080293, 0, 0, 0] := by
  rw [show A10K2.u5651 = KTree.node A10K2.t5656 (nat_lit 92972531) (nat_lit 9023718657) (nat_lit 0) A10K2.t5657 from rfl, totK_node, tot5656, tot5657]
  decide +kernel

theorem arows5652 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5652 = true := by
  rw [show A10K2.u5652 = KTree.node A10K2.t5658 (nat_lit 92980699) (nat_lit 6835401418) (nat_lit 0) A10K2.t5659 from rfl, allE_node, rows5658, irow5652, rows5659]
  all_goals rfl

theorem atot5652 : totK PA10K2 A10K2.u5652 = [0, 0, 816634122601, 3396126425977, 3950879799700, 1153871234098, 83009222198, 0, 0, 0] := by
  rw [show A10K2.u5652 = KTree.node A10K2.t5658 (nat_lit 92980699) (nat_lit 6835401418) (nat_lit 0) A10K2.t5659 from rfl, totK_node, tot5658, tot5659]
  decide +kernel

theorem arows5654 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5654 = true := by
  rw [show A10K2.u5654 = KTree.node A10K2.t5660 (nat_lit 93005028) (nat_lit 12660168957) (nat_lit 0) A10K2.t5661 from rfl, allE_node, rows5660, irow5654, rows5661]
  all_goals rfl

theorem atot5654 : totK PA10K2 A10K2.u5654 = [0, 661422287142, 2180579581983, 2710067193576, 2487304817018, 1345456003715, 239904770714, 6354482628, 0, 0] := by
  rw [show A10K2.u5654 = KTree.node A10K2.t5660 (nat_lit 93005028) (nat_lit 12660168957) (nat_lit 0) A10K2.t5661 from rfl, totK_node, tot5660, tot5661]
  decide +kernel

theorem arows5655 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5655 = true := by
  rw [show A10K2.u5655 = KTree.node A10K2.t5662 (nat_lit 93009762) (nat_lit 12816487829) (nat_lit 0) A10K2.t5663 from rfl, allE_node, rows5662, irow5655, rows5663]
  all_goals rfl

theorem atot5655 : totK PA10K2 A10K2.u5655 = [0, 400267849178, 2119181785961, 3970829657242, 2837771005816, 584612112861, 31747192500, 0, 0, 0] := by
  rw [show A10K2.u5655 = KTree.node A10K2.t5662 (nat_lit 93009762) (nat_lit 12816487829) (nat_lit 0) A10K2.t5663 from rfl, totK_node, tot5662, tot5663]
  decide +kernel

theorem arows5660 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5660 = true := by
  rw [show A10K2.u5660 = KTree.node A10K2.t5664 (nat_lit 93025450) (nat_lit 12779633272) (nat_lit 0) A10K2.t5665 from rfl, allE_node, rows5664, irow5660, rows5665]
  all_goals rfl

theorem atot5660 : totK PA10K2 A10K2.u5660 = [0, 307923820525, 2283569404194, 4555439985741, 2693102732547, 377123861411, 6962742351, 0, 0, 0] := by
  rw [show A10K2.u5660 = KTree.node A10K2.t5664 (nat_lit 93025450) (nat_lit 12779633272) (nat_lit 0) A10K2.t5665 from rfl, totK_node, tot5664, tot5665]
  decide +kernel

theorem arows5661 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5661 = true := by
  rw [show A10K2.u5661 = KTree.node A10K2.t5666 (nat_lit 93040057) (nat_lit 6781821685) (nat_lit 0) A10K2.t5667 from rfl, allE_node, rows5666, irow5661, rows5667]
  all_goals rfl

theorem atot5661 : totK PA10K2 A10K2.u5661 = [0, 0, 571801115216, 2778446563888, 4170699820267, 2081592060309, 285966743095, 7047025452, 0, 0] := by
  rw [show A10K2.u5661 = KTree.node A10K2.t5666 (nat_lit 93040057) (nat_lit 6781821685) (nat_lit 0) A10K2.t5667 from rfl, totK_node, tot5666, tot5667]
  decide +kernel

theorem arows5663 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5663 = true := by
  rw [show A10K2.u5663 = KTree.node A10K2.t5668 (nat_lit 93056155) (nat_lit 9878357186) (nat_lit 0) A10K2.t5669 from rfl, allE_node, rows5668, irow5663, rows5669]
  all_goals rfl

theorem atot5663 : totK PA10K2 A10K2.u5663 = [0, 0, 595236583059, 2756841276431, 4268866882845, 2198349964962, 259567026030, 6157148557, 0, 0] := by
  rw [show A10K2.u5663 = KTree.node A10K2.t5668 (nat_lit 93056155) (nat_lit 9878357186) (nat_lit 0) A10K2.t5669 from rfl, totK_node, tot5668, tot5669]
  decide +kernel

theorem arows5664 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5664 = true := by
  rw [show A10K2.u5664 = KTree.node A10K2.t5670 (nat_lit 93136827) (nat_lit 7045562274) (nat_lit 0) A10K2.t5671 from rfl, allE_node, rows5670, irow5664, rows5671]
  all_goals rfl

theorem atot5664 : totK PA10K2 A10K2.u5664 = [0, 0, 845829470152, 3333625503875, 3964571354748, 1462988614603, 124109187599, 0, 0, 0] := by
  rw [show A10K2.u5664 = KTree.node A10K2.t5670 (nat_lit 93136827) (nat_lit 7045562274) (nat_lit 0) A10K2.t5671 from rfl, totK_node, tot5670, tot5671]
  decide +kernel

theorem arows5667 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5667 = true := by
  rw [show A10K2.u5667 = KTree.node A10K2.t5672 (nat_lit 93141345) (nat_lit 7137177950) (nat_lit 0) A10K2.t5673 from rfl, allE_node, rows5672, irow5667, rows5673]
  all_goals rfl

theorem atot5667 : totK PA10K2 A10K2.u5667 = [0, 0, 344552455730, 1873859046718, 3800671921569, 2832566725791, 601031643711, 31768748853, 0, 0] := by
  rw [show A10K2.u5667 = KTree.node A10K2.t5672 (nat_lit 93141345) (nat_lit 7137177950) (nat_lit 0) A10K2.t5673 from rfl, totK_node, tot5672, tot5673]
  decide +kernel

theorem arows5668 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5668 = true := by
  rw [show A10K2.u5668 = KTree.node A10K2.t5674 (nat_lit 93147143) (nat_lit 9171489499) (nat_lit 0) A10K2.t5675 from rfl, allE_node, rows5674, irow5668, rows5675]
  all_goals rfl

theorem atot5668 : totK PA10K2 A10K2.u5668 = [0, 0, 402692973434, 2465886536397, 4182453055935, 2091171261989, 218707154964, 0, 0, 0] := by
  rw [show A10K2.u5668 = KTree.node A10K2.t5674 (nat_lit 93147143) (nat_lit 9171489499) (nat_lit 0) A10K2.t5675 from rfl, totK_node, tot5674, tot5675]
  decide +kernel

theorem arows5670 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5670 = true := by
  rw [show A10K2.u5670 = KTree.node A10K2.t5676 (nat_lit 93154815) (nat_lit 14004808951) (nat_lit 0) A10K2.t5677 from rfl, allE_node, rows5676, irow5670, rows5677]
  all_goals rfl

theorem atot5670 : totK PA10K2 A10K2.u5670 = [0, 0, 627544772511, 2824977242593, 4188772112173, 2191938219138, 316620336489, 13202416085, 0, 0] := by
  rw [show A10K2.u5670 = KTree.node A10K2.t5676 (nat_lit 93154815) (nat_lit 14004808951) (nat_lit 0) A10K2.t5677 from rfl, totK_node, tot5676, tot5677]
  decide +kernel

theorem arows5671 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5671 = true := by
  rw [show A10K2.u5671 = KTree.node A10K2.t5678 (nat_lit 93169947) (nat_lit 9964074265) (nat_lit 0) A10K2.t5679 from rfl, allE_node, rows5678, irow5671, rows5679]
  all_goals rfl

theorem atot5671 : totK PA10K2 A10K2.u5671 = [0, 0, 0, 946616008869, 3616008284725, 3904865655820, 1151525891294, 73475212350, 0, 0] := by
  rw [show A10K2.u5671 = KTree.node A10K2.t5678 (nat_lit 93169947) (nat_lit 9964074265) (nat_lit 0) A10K2.t5679 from rfl, totK_node, tot5678, tot5679]
  decide +kernel

theorem arows5675 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5675 = true := by
  rw [show A10K2.u5675 = KTree.node A10K2.t5680 (nat_lit 93176070) (nat_lit 4929284025) (nat_lit 0) A10K2.t5681 from rfl, allE_node, rows5680, irow5675, rows5681]
  all_goals rfl

theorem atot5675 : totK PA10K2 A10K2.u5675 = [0, 0, 0, 630988918538, 2558505998649, 3552766186124, 2018288343839, 441757140046, 31018567651, 0] := by
  rw [show A10K2.u5675 = KTree.node A10K2.t5680 (nat_lit 93176070) (nat_lit 4929284025) (nat_lit 0) A10K2.t5681 from rfl, totK_node, tot5680, tot5681]
  decide +kernel

theorem arows5676 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5676 = true := by
  rw [show A10K2.u5676 = KTree.node A10K2.t5682 (nat_lit 93182194) (nat_lit 13904215011) (nat_lit 0) A10K2.t5683 from rfl, allE_node, rows5682, irow5676, rows5683]
  all_goals rfl

theorem atot5676 : totK PA10K2 A10K2.u5676 = [0, 0, 0, 648994886812, 2887368151893, 4016919425534, 1690889897232, 209544971195, 5685526223, 0] := by
  rw [show A10K2.u5676 = KTree.node A10K2.t5682 (nat_lit 93182194) (nat_lit 13904215011) (nat_lit 0) A10K2.t5683 from rfl, totK_node, tot5682, tot5683]
  decide +kernel

theorem arows5678 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5678 = true := by
  rw [show A10K2.u5678 = KTree.node A10K2.t5684 (nat_lit 93194761) (nat_lit 9709433456) (nat_lit 0) A10K2.t5685 from rfl, allE_node, rows5684, irow5678, rows5685]
  all_goals rfl

theorem atot5678 : totK PA10K2 A10K2.u5678 = [0, 0, 584568996914, 2669766179441, 4038560731189, 1916490341094, 243758789389, 5460492893, 0, 0] := by
  rw [show A10K2.u5678 = KTree.node A10K2.t5684 (nat_lit 93194761) (nat_lit 9709433456) (nat_lit 0) A10K2.t5685 from rfl, totK_node, tot5684, tot5685]
  decide +kernel

theorem arows5679 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5679 = true := by
  rw [show A10K2.u5679 = KTree.node A10K2.t5686 (nat_lit 93203107) (nat_lit 10480732544) (nat_lit 0) A10K2.t5687 from rfl, allE_node, rows5686, irow5679, rows5687]
  all_goals rfl

theorem atot5679 : totK PA10K2 A10K2.u5679 = [0, 0, 738796459887, 3136001725931, 3952324128891, 1654724168963, 244851473096, 20340910120, 0, 0] := by
  rw [show A10K2.u5679 = KTree.node A10K2.t5686 (nat_lit 93203107) (nat_lit 10480732544) (nat_lit 0) A10K2.t5687 from rfl, totK_node, tot5686, tot5687]
  decide +kernel

theorem arows5682 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5682 = true := by
  rw [show A10K2.u5682 = KTree.node A10K2.t5688 (nat_lit 93208839) (nat_lit 8430565036) (nat_lit 0) A10K2.t5689 from rfl, allE_node, rows5688, irow5682, rows5689]
  all_goals rfl

theorem atot5682 : totK PA10K2 A10K2.u5682 = [0, 0, 607829555444, 2477869951157, 3758901776341, 2230885602364, 373431864287, 11427838733, 0, 0] := by
  rw [show A10K2.u5682 = KTree.node A10K2.t5688 (nat_lit 93208839) (nat_lit 8430565036) (nat_lit 0) A10K2.t5689 from rfl, totK_node, tot5688, tot5689]
  decide +kernel

theorem arows5683 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5683 = true := by
  rw [show A10K2.u5683 = KTree.node A10K2.t5690 (nat_lit 93214051) (nat_lit 9355842215) (nat_lit 0) A10K2.t5691 from rfl, allE_node, rows5690, irow5683, rows5691]
  all_goals rfl

theorem atot5683 : totK PA10K2 A10K2.u5683 = [0, 0, 212197739899, 2054809196474, 4284220231307, 2433744877207, 335743176052, 6354482628, 0, 0] := by
  rw [show A10K2.u5683 = KTree.node A10K2.t5690 (nat_lit 93214051) (nat_lit 9355842215) (nat_lit 0) A10K2.t5691 from rfl, totK_node, tot5690, tot5691]
  decide +kernel

theorem arows5685 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5685 = true := by
  rw [show A10K2.u5685 = KTree.node A10K2.t5692 (nat_lit 93234844) (nat_lit 11253491165) (nat_lit 0) A10K2.t5693 from rfl, allE_node, rows5692, irow5685, rows5693]
  all_goals rfl

theorem atot5685 : totK PA10K2 A10K2.u5685 = [0, 0, 0, 1058316904522, 3839664827226, 3716632219178, 825721013613, 43864921862, 0, 0] := by
  rw [show A10K2.u5685 = KTree.node A10K2.t5692 (nat_lit 93234844) (nat_lit 11253491165) (nat_lit 0) A10K2.t5693 from rfl, totK_node, tot5692, tot5693]
  decide +kernel

theorem arows5686 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5686 = true := by
  rw [show A10K2.u5686 = KTree.node A10K2.t5694 (nat_lit 93243149) (nat_lit 5544247775) (nat_lit 0) A10K2.t5695 from rfl, allE_node, rows5694, irow5686, rows5695]
  all_goals rfl

theorem atot5686 : totK PA10K2 A10K2.u5686 = [0, 0, 0, 815009446895, 3417111496677, 3937230824387, 1034553859819, 55841124735, 0, 0] := by
  rw [show A10K2.u5686 = KTree.node A10K2.t5694 (nat_lit 93243149) (nat_lit 5544247775) (nat_lit 0) A10K2.t5695 from rfl, totK_node, tot5694, tot5695]
  decide +kernel

theorem arows5692 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5692 = true := by
  rw [show A10K2.u5692 = KTree.node A10K2.t5696 (nat_lit 93267406) (nat_lit 14361836361) (nat_lit 0) A10K2.t5697 from rfl, allE_node, rows5696, irow5692, rows5697]
  all_goals rfl

theorem atot5692 : totK PA10K2 A10K2.u5692 = [0, 0, 770786377514, 2601573202915, 2873365312744, 2033358984012, 1072317935489, 196635035010, 6239673734, 0] := by
  rw [show A10K2.u5692 = KTree.node A10K2.t5696 (nat_lit 93267406) (nat_lit 14361836361) (nat_lit 0) A10K2.t5697 from rfl, totK_node, tot5696, tot5697]
  decide +kernel

theorem arows5693 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5693 = true := by
  rw [show A10K2.u5693 = KTree.node A10K2.t5698 (nat_lit 93272341) (nat_lit 6986069194) (nat_lit 0) A10K2.t5699 from rfl, allE_node, rows5698, irow5693, rows5699]
  all_goals rfl

theorem atot5693 : totK PA10K2 A10K2.u5693 = [0, 0, 368745577193, 2236885346514, 4233757211515, 2631666473082, 466580747633, 25660650750, 0, 0] := by
  rw [show A10K2.u5693 = KTree.node A10K2.t5698 (nat_lit 93272341) (nat_lit 6986069194) (nat_lit 0) A10K2.t5699 from rfl, totK_node, tot5698, tot5699]
  decide +kernel

theorem arows5695 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5695 = true := by
  rw [show A10K2.u5695 = KTree.node A10K2.t5700 (nat_lit 93288183) (nat_lit 10750950298) (nat_lit 0) A10K2.t5701 from rfl, allE_node, rows5700, irow5695, rows5701]
  all_goals rfl

theorem atot5695 : totK PA10K2 A10K2.u5695 = [0, 310366196018, 1300010465555, 2622695819482, 3444123995599, 2075420370951, 323530357665, 6962742351, 0, 0] := by
  rw [show A10K2.u5695 = KTree.node A10K2.t5700 (nat_lit 93288183) (nat_lit 10750950298) (nat_lit 0) A10K2.t5701 from rfl, totK_node, tot5700, tot5701]
  decide +kernel

theorem arows5696 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5696 = true := by
  rw [show A10K2.u5696 = KTree.node A10K2.t5702 (nat_lit 93327288) (nat_lit 13898329239) (nat_lit 0) A10K2.t5703 from rfl, allE_node, rows5702, irow5696, rows5703]
  all_goals rfl

theorem atot5696 : totK PA10K2 A10K2.u5696 = [0, 490160962616, 2414463554534, 3889497404668, 2185549343198, 418072005300, 25371180993, 0, 0, 0] := by
  rw [show A10K2.u5696 = KTree.node A10K2.t5702 (nat_lit 93327288) (nat_lit 13898329239) (nat_lit 0) A10K2.t5703 from rfl, totK_node, tot5702, tot5703]
  decide +kernel

theorem arows5699 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5699 = true := by
  rw [show A10K2.u5699 = KTree.node A10K2.t5704 (nat_lit 93340592) (nat_lit 14613243873) (nat_lit 0) A10K2.t5705 from rfl, allE_node, rows5704, irow5699, rows5705]
  all_goals rfl

theorem atot5699 : totK PA10K2 A10K2.u5699 = [0, 786377939935, 3074411667972, 3802985557272, 1630456584293, 215669747449, 5460492893, 0, 0, 0] := by
  rw [show A10K2.u5699 = KTree.node A10K2.t5704 (nat_lit 93340592) (nat_lit 14613243873) (nat_lit 0) A10K2.t5705 from rfl, totK_node, tot5704, tot5705]
  decide +kernel

theorem arows5700 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5700 = true := by
  rw [show A10K2.u5700 = KTree.node A10K2.t5706 (nat_lit 93346582) (nat_lit 5131906063) (nat_lit 0) A10K2.t5707 from rfl, allE_node, rows5706, irow5700, rows5707]
  all_goals rfl

theorem atot5700 : totK PA10K2 A10K2.u5700 = [0, 458520426296, 2457450613314, 4151705964384, 2233921687319, 307888086474, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u5700 = KTree.node A10K2.t5706 (nat_lit 93346582) (nat_lit 5131906063) (nat_lit 0) A10K2.t5707 from rfl, totK_node, tot5706, tot5707]
  decide +kernel

theorem arows5702 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5702 = true := by
  rw [show A10K2.u5702 = KTree.node A10K2.t5708 (nat_lit 93356104) (nat_lit 13804082660) (nat_lit 0) A10K2.t5709 from rfl, allE_node, rows5708, irow5702, rows5709]
  all_goals rfl

theorem atot5702 : totK PA10K2 A10K2.u5702 = [0, 0, 1035102939668, 3807106153004, 3800349791253, 929727197627, 44048945087, 0, 0, 0] := by
  rw [show A10K2.u5702 = KTree.node A10K2.t5708 (nat_lit 93356104) (nat_lit 13804082660) (nat_lit 0) A10K2.t5709 from rfl, totK_node, tot5708, tot5709]
  decide +kernel

theorem arows5703 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5703 = true := by
  rw [show A10K2.u5703 = KTree.node A10K2.t5710 (nat_lit 93360904) (nat_lit 13873415710) (nat_lit 0) A10K2.t5711 from rfl, allE_node, rows5710, irow5703, rows5711]
  all_goals rfl

theorem atot5703 : totK PA10K2 A10K2.u5703 = [0, 0, 393490345705, 1957985342246, 3798556924803, 2535778210844, 497554368418, 30650496230, 0, 0] := by
  rw [show A10K2.u5703 = KTree.node A10K2.t5710 (nat_lit 93360904) (nat_lit 13873415710) (nat_lit 0) A10K2.t5711 from rfl, totK_node, tot5710, tot5711]
  decide +kernel

theorem arows5707 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5707 = true := by
  rw [show A10K2.u5707 = KTree.node A10K2.t5712 (nat_lit 93374691) (nat_lit 10076610976) (nat_lit 0) A10K2.t5713 from rfl, allE_node, rows5712, irow5707, rows5713]
  all_goals rfl

theorem atot5707 : totK PA10K2 A10K2.u5707 = [0, 0, 610444215268, 3127325125996, 4267334149769, 1429854833583, 96935201668, 0, 0, 0] := by
  rw [show A10K2.u5707 = KTree.node A10K2.t5712 (nat_lit 93374691) (nat_lit 10076610976) (nat_lit 0) A10K2.t5713 from rfl, totK_node, tot5712, tot5713]
  decide +kernel

theorem arows5708 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5708 = true := by
  rw [show A10K2.u5708 = KTree.node A10K2.t5714 (nat_lit 93384118) (nat_lit 17179869184) (nat_lit 0) A10K2.t5715 from rfl, allE_node, rows5714, irow5708, rows5715]
  all_goals rfl

theorem atot5708 : totK PA10K2 A10K2.u5708 = [0, 449259150676, 1883815494422, 3141920427920, 2756305474456, 1183265538338, 166497135796, 5546304973, 0, 0] := by
  rw [show A10K2.u5708 = KTree.node A10K2.t5714 (nat_lit 93384118) (nat_lit 17179869184) (nat_lit 0) A10K2.t5715 from rfl, totK_node, tot5714, tot5715]
  decide +kernel

theorem arows5710 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5710 = true := by
  rw [show A10K2.u5710 = KTree.node A10K2.t5716 (nat_lit 93402338) (nat_lit 14311337129) (nat_lit 0) A10K2.t5717 from rfl, allE_node, rows5716, irow5710, rows5717]
  all_goals rfl

theorem atot5710 : totK PA10K2 A10K2.u5710 = [0, 339451561926, 2086036694102, 3895342060944, 2619481858010, 517052000601, 25734533292, 0, 0, 0] := by
  rw [show A10K2.u5710 = KTree.node A10K2.t5716 (nat_lit 93402338) (nat_lit 14311337129) (nat_lit 0) A10K2.t5717 from rfl, totK_node, tot5716, tot5717]
  decide +kernel

theorem arows5711 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5711 = true := by
  rw [show A10K2.u5711 = KTree.node A10K2.t5718 (nat_lit 93406677) (nat_lit 5287672699) (nat_lit 0) A10K2.t5719 from rfl, allE_node, rows5718, irow5711, rows5719]
  all_goals rfl

theorem atot5711 : totK PA10K2 A10K2.u5711 = [0, 786989521176, 3218117219125, 3914853522986, 1491960720437, 177661306664, 6034215561, 0, 0, 0] := by
  rw [show A10K2.u5711 = KTree.node A10K2.t5718 (nat_lit 93406677) (nat_lit 5287672699) (nat_lit 0) A10K2.t5719 from rfl, totK_node, tot5718, tot5719]
  decide +kernel

theorem arows5714 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5714 = true := by
  rw [show A10K2.u5714 = KTree.node A10K2.t5720 (nat_lit 93414590) (nat_lit 15659313499) (nat_lit 0) A10K2.t5721 from rfl, allE_node, rows5720, irow5714, rows5721]
  all_goals rfl

theorem atot5714 : totK PA10K2 A10K2.u5714 = [0, 461607179050, 2453240924029, 4182248781685, 2285681614932, 308434567298, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u5714 = KTree.node A10K2.t5720 (nat_lit 93414590) (nat_lit 15659313499) (nat_lit 0) A10K2.t5721 from rfl, totK_node, tot5720, tot5721]
  decide +kernel

theorem arows5715 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5715 = true := by
  rw [show A10K2.u5715 = KTree.node A10K2.t5722 (nat_lit 93431169) (nat_lit 1447612559) (nat_lit 0) A10K2.t5723 from rfl, allE_node, rows5722, irow5715, rows5723]
  all_goals rfl

theorem atot5715 : totK PA10K2 A10K2.u5715 = [0, 0, 1059223002643, 3774423900547, 3794046668046, 1018358982362, 51126336279, 0, 0, 0] := by
  rw [show A10K2.u5715 = KTree.node A10K2.t5722 (nat_lit 93431169) (nat_lit 1447612559) (nat_lit 0) A10K2.t5723 from rfl, totK_node, tot5722, tot5723]
  decide +kernel

theorem arows5717 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5717 = true := by
  rw [show A10K2.u5717 = KTree.node A10K2.t5724 (nat_lit 93435832) (nat_lit 2663468752) (nat_lit 128) A10K2.t5725 from rfl, allE_node, rows5724, irow5717, rows5725]
  all_goals rfl

theorem atot5717 : totK PA10K2 A10K2.u5717 = [0, 0, 291209524724, 1974254297907, 3948419627344, 2594452324161, 507434788408, 31082886609, 0, 0] := by
  rw [show A10K2.u5717 = KTree.node A10K2.t5724 (nat_lit 93435832) (nat_lit 2663468752) (nat_lit 128) A10K2.t5725 from rfl, totK_node, tot5724, tot5725]
  decide +kernel

theorem arows5718 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5718 = true := by
  rw [show A10K2.u5718 = KTree.node A10K2.t5726 (nat_lit 93440352) (nat_lit 12213653678) (nat_lit 0) A10K2.t5727 from rfl, allE_node, rows5726, irow5718, rows5727]
  all_goals rfl

theorem atot5718 : totK PA10K2 A10K2.u5718 = [0, 0, 584263778251, 2937028791014, 4252354594341, 1578488514197, 109291298544, 0, 0, 0] := by
  rw [show A10K2.u5718 = KTree.node A10K2.t5726 (nat_lit 93440352) (nat_lit 12213653678) (nat_lit 0) A10K2.t5727 from rfl, totK_node, tot5726, tot5727]
  decide +kernel

theorem arows5723 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5723 = true := by
  rw [show A10K2.u5723 = KTree.node A10K2.t5728 (nat_lit 93449657) (nat_lit 6222452711) (nat_lit 0) A10K2.t5729 from rfl, allE_node, rows5728, irow5723, rows5729]
  all_goals rfl

theorem atot5723 : totK PA10K2 A10K2.u5723 = [0, 470021399381, 1924297716777, 3076578359497, 2711174388667, 1247116139085, 180622073188, 6121173289, 0, 0] := by
  rw [show A10K2.u5723 = KTree.node A10K2.t5728 (nat_lit 93449657) (nat_lit 6222452711) (nat_lit 0) A10K2.t5729 from rfl, totK_node, tot5728, tot5729]
  decide +kernel

theorem arows5724 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5724 = true := by
  rw [show A10K2.u5724 = KTree.node A10K2.t5730 (nat_lit 93458839) (nat_lit 8418235729) (nat_lit 0) A10K2.t5731 from rfl, allE_node, rows5730, irow5724, rows5731]
  all_goals rfl

theorem atot5724 : totK PA10K2 A10K2.u5724 = [0, 272659432210, 1958920647478, 3971895587005, 2637293565377, 535678467166, 30831673886, 0, 0, 0] := by
  rw [show A10K2.u5724 = KTree.node A10K2.t5730 (nat_lit 93458839) (nat_lit 8418235729) (nat_lit 0) A10K2.t5731 from rfl, totK_node, tot5730, tot5731]
  decide +kernel

theorem arows5726 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5726 = true := by
  rw [show A10K2.u5726 = KTree.node A10K2.t5732 (nat_lit 93465122) (nat_lit 8858867674) (nat_lit 0) A10K2.t5733 from rfl, allE_node, rows5732, irow5726, rows5733]
  all_goals rfl

theorem atot5726 : totK PA10K2 A10K2.u5726 = [0, 746072176619, 3015143163575, 3858738084762, 1705587530558, 249577441325, 15171143123, 0, 0, 0] := by
  rw [show A10K2.u5726 = KTree.node A10K2.t5732 (nat_lit 93465122) (nat_lit 8858867674) (nat_lit 0) A10K2.t5733 from rfl, totK_node, tot5732, tot5733]
  decide +kernel

theorem arows5727 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5727 = true := by
  rw [show A10K2.u5727 = KTree.node A10K2.t5734 (nat_lit 93470977) (nat_lit 10329861105) (nat_lit 0) A10K2.t5735 from rfl, allE_node, rows5734, irow5727, rows5735]
  all_goals rfl

theorem atot5727 : totK PA10K2 A10K2.u5727 = [0, 544026290360, 2420296262414, 3780154578925, 2330517315160, 422043866323, 16597605730, 0, 0, 0] := by
  rw [show A10K2.u5727 = KTree.node A10K2.t5734 (nat_lit 93470977) (nat_lit 10329861105) (nat_lit 0) A10K2.t5735 from rfl, totK_node, tot5734, tot5735]
  decide +kernel

theorem arows5730 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5730 = true := by
  rw [show A10K2.u5730 = KTree.node A10K2.t5736 (nat_lit 93476082) (nat_lit 14618489455) (nat_lit 0) A10K2.t5737 from rfl, allE_node, rows5736, irow5730, rows5737]
  all_goals rfl

theorem atot5730 : totK PA10K2 A10K2.u5730 = [0, 311053418201, 2253931451998, 4297954402820, 2350555494532, 309305900333, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u5730 = KTree.node A10K2.t5736 (nat_lit 93476082) (nat_lit 14618489455) (nat_lit 0) A10K2.t5737 from rfl, totK_node, tot5736, tot5737]
  decide +kernel

theorem arows5731 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5731 = true := by
  rw [show A10K2.u5731 = KTree.node A10K2.t5738 (nat_lit 93490566) (nat_lit 13846446273) (nat_lit 0) A10K2.t5739 from rfl, allE_node, rows5738, irow5731, rows5739]
  all_goals rfl

theorem atot5731 : totK PA10K2 A10K2.u5731 = [0, 0, 936477568179, 3522067203552, 3876653013218, 1103560458399, 64899520130, 0, 0, 0] := by
  rw [show A10K2.u5731 = KTree.node A10K2.t5738 (nat_lit 93490566) (nat_lit 13846446273) (nat_lit 0) A10K2.t5739 from rfl, totK_node, tot5738, tot5739]
  decide +kernel

theorem arows5733 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5733 = true := by
  rw [show A10K2.u5733 = KTree.node A10K2.t5740 (nat_lit 93504006) (nat_lit 13205391669) (nat_lit 0) A10K2.t5741 from rfl, allE_node, rows5740, irow5733, rows5741]
  all_goals rfl

theorem atot5733 : totK PA10K2 A10K2.u5733 = [0, 0, 1009891550690, 3645281935069, 3788919512238, 993640561927, 63495312472, 0, 0, 0] := by
  rw [show A10K2.u5733 = KTree.node A10K2.t5740 (nat_lit 93504006) (nat_lit 13205391669) (nat_lit 0) A10K2.t5741 from rfl, totK_node, tot5740, tot5741]
  decide +kernel

theorem arows5734 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5734 = true := by
  rw [show A10K2.u5734 = KTree.node A10K2.t5742 (nat_lit 93509741) (nat_lit 5502651488) (nat_lit 0) A10K2.t5743 from rfl, allE_node, rows5742, irow5734, rows5743]
  all_goals rfl

theorem atot5734 : totK PA10K2 A10K2.u5734 = [0, 0, 422940515978, 2524264407634, 4180448538093, 1956018731214, 286048911365, 6354482628, 0, 0] := by
  rw [show A10K2.u5734 = KTree.node A10K2.t5742 (nat_lit 93509741) (nat_lit 5502651488) (nat_lit 0) A10K2.t5743 from rfl, totK_node, tot5742, tot5743]
  decide +kernel

theorem arows5738 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5738 = true := by
  rw [show A10K2.u5738 = KTree.node A10K2.t5744 (nat_lit 93589389) (nat_lit 2875981312) (nat_lit 0) A10K2.t5745 from rfl, allE_node, rows5744, irow5738, rows5745]
  all_goals rfl

theorem atot5738 : totK PA10K2 A10K2.u5738 = [0, 0, 489555400315, 2450157879131, 3920963228820, 2118099701785, 364457948112, 25371180993, 0, 0] := by
  rw [show A10K2.u5738 = KTree.node A10K2.t5744 (nat_lit 93589389) (nat_lit 2875981312) (nat_lit 0) A10K2.t5745 from rfl, totK_node, tot5744, tot5745]
  decide +kernel

theorem arows5739 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5739 = true := by
  rw [show A10K2.u5739 = KTree.node A10K2.t5746 (nat_lit 93602739) (nat_lit 1511357737) (nat_lit 0) A10K2.t5747 from rfl, allE_node, rows5746, irow5739, rows5747]
  all_goals rfl

theorem atot5739 : totK PA10K2 A10K2.u5739 = [0, 0, 784354618750, 3060223030636, 3776512161283, 1604529241261, 208315861582, 5447185874, 0, 0] := by
  rw [show A10K2.u5739 = KTree.node A10K2.t5746 (nat_lit 93602739) (nat_lit 1511357737) (nat_lit 0) A10K2.t5747 from rfl, totK_node, tot5746, tot5747]
  decide +kernel

theorem arows5741 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5741 = true := by
  rw [show A10K2.u5741 = KTree.node A10K2.t5748 (nat_lit 93608732) (nat_lit 11939802195) (nat_lit 0) A10K2.t5749 from rfl, allE_node, rows5748, irow5741, rows5749]
  all_goals rfl

theorem atot5741 : totK PA10K2 A10K2.u5741 = [0, 0, 458520426296, 2438001715705, 4140209675896, 2193856946455, 306383320544, 6354482628, 0, 0] := by
  rw [show A10K2.u5741 = KTree.node A10K2.t5748 (nat_lit 93608732) (nat_lit 11939802195) (nat_lit 0) A10K2.t5749 from rfl, totK_node, tot5748, tot5749]
  decide +kernel

theorem arows5742 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5742 = true := by
  rw [show A10K2.u5742 = KTree.node A10K2.t5750 (nat_lit 93660631) (nat_lit 14184824711) (nat_lit 0) A10K2.t5751 from rfl, allE_node, rows5750, irow5742, rows5751]
  all_goals rfl

theorem atot5742 : totK PA10K2 A10K2.u5742 = [0, 0, 764715118522, 2960101993514, 3914043446327, 1778066618633, 200317047661, 6853348008, 0, 0] := by
  rw [show A10K2.u5742 = KTree.node A10K2.t5750 (nat_lit 93660631) (nat_lit 14184824711) (nat_lit 0) A10K2.t5751 from rfl, totK_node, tot5750, tot5751]
  decide +kernel

theorem arows5745 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5745 = true := by
  rw [show A10K2.u5745 = KTree.node A10K2.t5752 (nat_lit 93665345) (nat_lit 9329127298) (nat_lit 0) A10K2.t5753 from rfl, allE_node, rows5752, irow5745, rows5753]
  all_goals rfl

theorem atot5745 : totK PA10K2 A10K2.u5745 = [0, 0, 240176859263, 1833095643226, 3921010676504, 2805188528743, 540518389853, 31452573850, 0, 0] := by
  rw [show A10K2.u5745 = KTree.node A10K2.t5752 (nat_lit 93665345) (nat_lit 9329127298) (nat_lit 0) A10K2.t5753 from rfl, totK_node, tot5752, tot5753]
  decide +kernel

theorem arows5746 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5746 = true := by
  rw [show A10K2.u5746 = KTree.node A10K2.t5754 (nat_lit 93669677) (nat_lit 6651382109) (nat_lit 0) A10K2.t5755 from rfl, allE_node, rows5754, irow5746, rows5755]
  all_goals rfl

theorem atot5746 : totK PA10K2 A10K2.u5746 = [0, 0, 583313821732, 2896628608453, 4227208802414, 1702498751582, 137609064481, 0, 0, 0] := by
  rw [show A10K2.u5746 = KTree.node A10K2.t5754 (nat_lit 93669677) (nat_lit 6651382109) (nat_lit 0) A10K2.t5755 from rfl, totK_node, tot5754, tot5755]
  decide +kernel

theorem arows5748 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5748 = true := by
  rw [show A10K2.u5748 = KTree.node A10K2.t5756 (nat_lit 93678820) (nat_lit 9104023529) (nat_lit 0) A10K2.t5757 from rfl, allE_node, rows5756, irow5748, rows5757]
  all_goals rfl

theorem atot5748 : totK PA10K2 A10K2.u5748 = [0, 0, 560451036135, 2399638715097, 3980131958994, 2414817571326, 378747886464, 13317224979, 0, 0] := by
  rw [show A10K2.u5748 = KTree.node A10K2.t5756 (nat_lit 93678820) (nat_lit 9104023529) (nat_lit 0) A10K2.t5757 from rfl, totK_node, tot5756, tot5757]
  decide +kernel

theorem arows5749 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5749 = true := by
  rw [show A10K2.u5749 = KTree.node A10K2.t5758 (nat_lit 93719310) (nat_lit 7621376772) (nat_lit 0) A10K2.t5759 from rfl, allE_node, rows5758, irow5749, rows5759]
  all_goals rfl

theorem atot5749 : totK PA10K2 A10K2.u5749 = [0, 0, 628258742488, 2843049253895, 3799051987585, 1719756075531, 308675878207, 24614390653, 0, 0] := by
  rw [show A10K2.u5749 = KTree.node A10K2.t5758 (nat_lit 93719310) (nat_lit 7621376772) (nat_lit 0) A10K2.t5759 from rfl, totK_node, tot5758, tot5759]
  decide +kernel

theorem arows5756 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5756 = true := by
  rw [show A10K2.u5756 = KTree.node A10K2.t5760 (nat_lit 93726170) (nat_lit 14670462402) (nat_lit 0) A10K2.t5761 from rfl, allE_node, rows5760, irow5756, rows5761]
  all_goals rfl

theorem atot5756 : totK PA10K2 A10K2.u5756 = [0, 0, 745073480358, 2946997295879, 3852142553530, 1731122308048, 210133399220, 5460492893, 0, 0] := by
  rw [show A10K2.u5756 = KTree.node A10K2.t5760 (nat_lit 93726170) (nat_lit 14670462402) (nat_lit 0) A10K2.t5761 from rfl, totK_node, tot5760, tot5761]
  decide +kernel

theorem arows5757 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5757 = true := by
  rw [show A10K2.u5757 = KTree.node A10K2.t5762 (nat_lit 93731098) (nat_lit 14174292022) (nat_lit 0) A10K2.t5763 from rfl, allE_node, rows5762, irow5757, rows5763]
  all_goals rfl

theorem atot5757 : totK PA10K2 A10K2.u5757 = [0, 0, 270189285852, 1894863291511, 3953489374791, 2643636289356, 513559548322, 31003444686, 0, 0] := by
  rw [show A10K2.u5757 = KTree.node A10K2.t5762 (nat_lit 93731098) (nat_lit 14174292022) (nat_lit 0) A10K2.t5763 from rfl, totK_node, tot5762, tot5763]
  decide +kernel

theorem arows5759 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5759 = true := by
  rw [show A10K2.u5759 = KTree.node A10K2.t5764 (nat_lit 93735480) (nat_lit 12710794095) (nat_lit 0) A10K2.t5765 from rfl, allE_node, rows5764, irow5759, rows5765]
  all_goals rfl

theorem atot5759 : totK PA10K2 A10K2.u5759 = [0, 0, 581670111060, 2883248938704, 4170184138143, 1656404216505, 138456623420, 0, 0, 0] := by
  rw [show A10K2.u5759 = KTree.node A10K2.t5764 (nat_lit 93735480) (nat_lit 12710794095) (nat_lit 0) A10K2.t5765 from rfl, totK_node, tot5764, tot5765]
  decide +kernel

theorem arows5760 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5760 = true := by
  rw [show A10K2.u5760 = KTree.node A10K2.t5766 (nat_lit 93751373) (nat_lit 5597859899) (nat_lit 0) A10K2.t5767 from rfl, allE_node, rows5766, irow5760, rows5767]
  all_goals rfl

theorem atot5760 : totK PA10K2 A10K2.u5760 = [0, 0, 0, 1141837697596, 3936992995983, 3461846336773, 751823938354, 37547833973, 0, 0] := by
  rw [show A10K2.u5760 = KTree.node A10K2.t5766 (nat_lit 93751373) (nat_lit 5597859899) (nat_lit 0) A10K2.t5767 from rfl, totK_node, tot5766, tot5767]
  decide +kernel

theorem arows5763 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5763 = true := by
  rw [show A10K2.u5763 = KTree.node A10K2.t5768 (nat_lit 93765696) (nat_lit 15398834173) (nat_lit 0) A10K2.t5769 from rfl, allE_node, rows5768, irow5763, rows5769]
  all_goals rfl

theorem atot5763 : totK PA10K2 A10K2.u5763 = [0, 0, 0, 981128040741, 3502231502324, 3600608927797, 1030393544405, 81800179711, 0, 0] := by
  rw [show A10K2.u5763 = KTree.node A10K2.t5768 (nat_lit 93765696) (nat_lit 15398834173) (nat_lit 0) A10K2.t5769 from rfl, totK_node, tot5768, tot5769]
  decide +kernel

theorem arows5764 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5764 = true := by
  rw [show A10K2.u5764 = KTree.node A10K2.t5770 (nat_lit 93771048) (nat_lit 10388644638) (nat_lit 0) A10K2.t5771 from rfl, allE_node, rows5770, irow5764, rows5771]
  all_goals rfl

theorem atot5764 : totK PA10K2 A10K2.u5764 = [0, 0, 319364639558, 1207239382693, 2523005792634, 3315244066911, 1652978909975, 265614550179, 6354482628, 0] := by
  rw [show A10K2.u5764 = KTree.node A10K2.t5770 (nat_lit 93771048) (nat_lit 10388644638) (nat_lit 0) A10K2.t5771 from rfl, totK_node, tot5770, tot5771]
  decide +kernel

theorem arows5766 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5766 = true := by
  rw [show A10K2.u5766 = KTree.node A10K2.t5772 (nat_lit 94375358) (nat_lit 16429612840) (nat_lit 0) A10K2.t5773 from rfl, allE_node, rows5772, irow5766, rows5773]
  all_goals rfl

theorem atot5766 : totK PA10K2 A10K2.u5766 = [0, 0, 526179114281, 2536743808132, 3927173771896, 2116393109075, 401283129201, 25371180993, 0, 0] := by
  rw [show A10K2.u5766 = KTree.node A10K2.t5772 (nat_lit 94375358) (nat_lit 16429612840) (nat_lit 0) A10K2.t5773 from rfl, totK_node, tot5772, tot5773]
  decide +kernel

theorem arows5767 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5767 = true := by
  rw [show A10K2.u5767 = KTree.node A10K2.t5774 (nat_lit 94388613) (nat_lit 5546391446) (nat_lit 0) A10K2.t5775 from rfl, allE_node, rows5774, irow5767, rows5775]
  all_goals rfl

theorem atot5767 : totK PA10K2 A10K2.u5767 = [0, 0, 704094552235, 2726440923612, 3763109261310, 1922851578649, 253883221634, 5460492893, 0, 0] := by
  rw [show A10K2.u5767 = KTree.node A10K2.t5774 (nat_lit 94388613) (nat_lit 5546391446) (nat_lit 0) A10K2.t5775 from rfl, totK_node, tot5774, tot5775]
  decide +kernel

theorem arows5771 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5771 = true := by
  rw [show A10K2.u5771 = KTree.node A10K2.t5776 (nat_lit 94394604) (nat_lit 11988709622) (nat_lit 0) A10K2.t5777 from rfl, allE_node, rows5776, irow5771, rows5777]
  all_goals rfl

theorem atot5771 : totK PA10K2 A10K2.u5771 = [0, 0, 393250294167, 2496261885950, 4188292056844, 2148344439163, 300511238796, 6354482628, 0, 0] := by
  rw [show A10K2.u5771 = KTree.node A10K2.t5776 (nat_lit 94394604) (nat_lit 11988709622) (nat_lit 0) A10K2.t5777 from rfl, totK_node, tot5776, tot5777]
  decide +kernel

theorem arows5772 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5772 = true := by
  rw [show A10K2.u5772 = KTree.node A10K2.t5778 (nat_lit 94401092) (nat_lit 10560850304) (nat_lit 0) A10K2.t5779 from rfl, allE_node, rows5778, irow5772, rows5779]
  all_goals rfl

theorem atot5772 : totK PA10K2 A10K2.u5772 = [0, 0, 259442569539, 1932383418183, 4292337560579, 3063110627724, 475636602708, 12746179907, 0, 0] := by
  rw [show A10K2.u5772 = KTree.node A10K2.t5778 (nat_lit 94401092) (nat_lit 10560850304) (nat_lit 0) A10K2.t5779 from rfl, totK_node, tot5778, tot5779]
  decide +kernel

theorem arows5774 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5774 = true := by
  rw [show A10K2.u5774 = KTree.node A10K2.t5780 (nat_lit 94408123) (nat_lit 6474745540) (nat_lit 0) A10K2.t5781 from rfl, allE_node, rows5780, irow5774, rows5781]
  all_goals rfl

theorem atot5774 : totK PA10K2 A10K2.u5774 = [0, 0, 0, 524186088667, 2692335998607, 4028279659438, 1890351813901, 336891700230, 25239774317, 0] := by
  rw [show A10K2.u5774 = KTree.node A10K2.t5780 (nat_lit 94408123) (nat_lit 6474745540) (nat_lit 0) A10K2.t5781 from rfl, totK_node, tot5780, tot5781]
  decide +kernel

theorem arows5775 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5775 = true := by
  rw [show A10K2.u5775 = KTree.node A10K2.t5782 (nat_lit 94421894) (nat_lit 15162412658) (nat_lit 0) A10K2.t5783 from rfl, allE_node, rows5782, irow5775, rows5783]
  all_goals rfl

theorem atot5775 : totK PA10K2 A10K2.u5775 = [0, 0, 0, 736611499333, 3099181749238, 3844372061963, 1458042476405, 177733912959, 5410721913, 0] := by
  rw [show A10K2.u5775 = KTree.node A10K2.t5782 (nat_lit 94421894) (nat_lit 15162412658) (nat_lit 0) A10K2.t5783 from rfl, totK_node, tot5782, tot5783]
  decide +kernel

theorem arows5778 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5778 = true := by
  rw [show A10K2.u5778 = KTree.node A10K2.t5784 (nat_lit 94429444) (nat_lit 12108312291) (nat_lit 0) A10K2.t5785 from rfl, allE_node, rows5784, irow5778, rows5785]
  all_goals rfl

theorem atot5778 : totK PA10K2 A10K2.u5778 = [0, 0, 253038457361, 1253403170796, 2898391057793, 3460650943694, 1498850065430, 202191612473, 5546304973, 0] := by
  rw [show A10K2.u5778 = KTree.node A10K2.t5784 (nat_lit 94429444) (nat_lit 12108312291) (nat_lit 0) A10K2.t5785 from rfl, totK_node, tot5784, tot5785]
  decide +kernel

theorem arows5779 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5779 = true := by
  rw [show A10K2.u5779 = KTree.node A10K2.t5786 (nat_lit 94506103) (nat_lit 14531099539) (nat_lit 0) A10K2.t5787 from rfl, allE_node, rows5786, irow5779, rows5787]
  all_goals rfl

theorem atot5779 : totK PA10K2 A10K2.u5779 = [0, 0, 513385147762, 2612527979911, 4037867826649, 2099837027573, 374238494871, 25371180993, 0, 0] := by
  rw [show A10K2.u5779 = KTree.node A10K2.t5786 (nat_lit 94506103) (nat_lit 14531099539) (nat_lit 0) A10K2.t5787 from rfl, totK_node, tot5786, tot5787]
  decide +kernel

theorem arows5781 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5781 = true := by
  rw [show A10K2.u5781 = KTree.node A10K2.t5788 (nat_lit 94512860) (nat_lit 10859328874) (nat_lit 0) A10K2.t5789 from rfl, allE_node, rows5788, irow5781, rows5789]
  all_goals rfl

theorem atot5781 : totK PA10K2 A10K2.u5781 = [0, 0, 551845602139, 2611582071472, 3982913117813, 2031201294799, 241475208379, 5460492893, 0, 0] := by
  rw [show A10K2.u5781 = KTree.node A10K2.t5788 (nat_lit 94512860) (nat_lit 10859328874) (nat_lit 0) A10K2.t5789 from rfl, totK_node, tot5788, tot5789]
  decide +kernel

theorem arows5782 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5782 = true := by
  rw [show A10K2.u5782 = KTree.node A10K2.t5790 (nat_lit 94519728) (nat_lit 14574101339) (nat_lit 0) A10K2.t5791 from rfl, allE_node, rows5790, irow5782, rows5791]
  all_goals rfl

theorem atot5782 : totK PA10K2 A10K2.u5782 = [0, 0, 696480544684, 2525418349931, 3442832020387, 2123350278462, 464989421082, 31333686660, 0, 0] := by
  rw [show A10K2.u5782 = KTree.node A10K2.t5790 (nat_lit 94519728) (nat_lit 14574101339) (nat_lit 0) A10K2.t5791 from rfl, totK_node, tot5790, tot5791]
  decide +kernel

theorem arows5787 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5787 = true := by
  rw [show A10K2.u5787 = KTree.node A10K2.t5792 (nat_lit 94525453) (nat_lit 5823242822) (nat_lit 0) A10K2.t5793 from rfl, allE_node, rows5792, irow5787, rows5793]
  all_goals rfl

theorem atot5787 : totK PA10K2 A10K2.u5787 = [0, 0, 112109183544, 1819976004096, 4246150947629, 2736270713729, 478377394897, 26601763172, 0, 0] := by
  rw [show A10K2.u5787 = KTree.node A10K2.t5792 (nat_lit 94525453) (nat_lit 5823242822) (nat_lit 0) A10K2.t5793 from rfl, totK_node, tot5792, tot5793]
  decide +kernel

theorem arows5788 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5788 = true := by
  rw [show A10K2.u5788 = KTree.node A10K2.t5794 (nat_lit 94539657) (nat_lit 7368686664) (nat_lit 32) A10K2.t5795 from rfl, allE_node, rows5794, irow5788, rows5795]
  all_goals rfl

theorem atot5788 : totK PA10K2 A10K2.u5788 = [0, 0, 0, 1023244390498, 3758160913562, 3792578086658, 868884050420, 44217177393, 0, 0] := by
  rw [show A10K2.u5788 = KTree.node A10K2.t5794 (nat_lit 94539657) (nat_lit 7368686664) (nat_lit 32) A10K2.t5795 from rfl, totK_node, tot5794, tot5795]
  decide +kernel

theorem arows5790 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5790 = true := by
  rw [show A10K2.u5790 = KTree.node A10K2.t5796 (nat_lit 94553818) (nat_lit 12609508753) (nat_lit 0) A10K2.t5797 from rfl, allE_node, rows5796, irow5790, rows5797]
  all_goals rfl

theorem atot5790 : totK PA10K2 A10K2.u5790 = [0, 0, 0, 809574965205, 3290000597591, 3889058010400, 1203297158895, 88866877739, 0, 0] := by
  rw [show A10K2.u5790 = KTree.node A10K2.t5796 (nat_lit 94553818) (nat_lit 12609508753) (nat_lit 0) A10K2.t5797 from rfl, totK_node, tot5796, tot5797]
  decide +kernel

theorem arows5791 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5791 = true := by
  rw [show A10K2.u5791 = KTree.node A10K2.t5798 (nat_lit 94568836) (nat_lit 8880320963) (nat_lit 0) A10K2.t5799 from rfl, allE_node, rows5798, irow5791, rows5799]
  all_goals rfl

theorem atot5791 : totK PA10K2 A10K2.u5791 = [0, 0, 770688507529, 2467669121012, 2714078756282, 2125048067992, 1192673246786, 233528391130, 6354482628, 0] := by
  rw [show A10K2.u5791 = KTree.node A10K2.t5798 (nat_lit 94568836) (nat_lit 8880320963) (nat_lit 0) A10K2.t5799 from rfl, totK_node, tot5798, tot5799]
  decide +kernel

theorem arows5794 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5794 = true := by
  rw [show A10K2.u5794 = KTree.node A10K2.t5800 (nat_lit 94574657) (nat_lit 10302278770) (nat_lit 0) A10K2.t5801 from rfl, allE_node, rows5800, irow5794, rows5801]
  all_goals rfl

theorem atot5794 : totK PA10K2 A10K2.u5794 = [0, 0, 286131565344, 1972282369774, 4129116337528, 2809481202866, 571522840010, 30810868011, 0, 0] := by
  rw [show A10K2.u5794 = KTree.node A10K2.t5800 (nat_lit 94574657) (nat_lit 10302278770) (nat_lit 0) A10K2.t5801 from rfl, totK_node, tot5800, tot5801]
  decide +kernel

theorem arows5795 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5795 = true := by
  rw [show A10K2.u5795 = KTree.node A10K2.t5802 (nat_lit 94597509) (nat_lit 4702062112) (nat_lit 0) A10K2.t5803 from rfl, allE_node, rows5802, irow5795, rows5803]
  all_goals rfl

theorem atot5795 : totK PA10K2 A10K2.u5795 = [0, 0, 627621874494, 2794207918533, 4172321134181, 2254959328161, 325501661295, 6853348008, 0, 0] := by
  rw [show A10K2.u5795 = KTree.node A10K2.t5802 (nat_lit 94597509) (nat_lit 4702062112) (nat_lit 0) A10K2.t5803 from rfl, totK_node, tot5802, tot5803]
  decide +kernel

theorem arows5797 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5797 = true := by
  rw [show A10K2.u5797 = KTree.node A10K2.t5804 (nat_lit 94973361) (nat_lit 7992631616) (nat_lit 0) A10K2.t5805 from rfl, allE_node, rows5804, irow5797, rows5805]
  all_goals rfl

theorem atot5797 : totK PA10K2 A10K2.u5797 = [0, 0, 527762187806, 2523918592109, 3940526873624, 2178133701360, 407801371018, 25734533292, 0, 0] := by
  rw [show A10K2.u5797 = KTree.node A10K2.t5804 (nat_lit 94973361) (nat_lit 7992631616) (nat_lit 0) A10K2.t5805 from rfl, totK_node, tot5804, tot5805]
  decide +kernel

theorem arows5798 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5798 = true := by
  rw [show A10K2.u5798 = KTree.node A10K2.t5806 (nat_lit 94978564) (nat_lit 11938764297) (nat_lit 0) A10K2.t5807 from rfl, allE_node, rows5806, irow5798, rows5807]
  all_goals rfl

theorem atot5798 : totK PA10K2 A10K2.u5798 = [0, 0, 649103519334, 2666053492906, 3813882089591, 2027248002641, 287908015045, 6034215561, 0, 0] := by
  rw [show A10K2.u5798 = KTree.node A10K2.t5806 (nat_lit 94978564) (nat_lit 11938764297) (nat_lit 0) A10K2.t5807 from rfl, totK_node, tot5806, tot5807]
  decide +kernel

theorem arows5802 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5802 = true := by
  rw [show A10K2.u5802 = KTree.node A10K2.t5808 (nat_lit 94984402) (nat_lit 14973476751) (nat_lit 0) A10K2.t5809 from rfl, allE_node, rows5808, irow5802, rows5809]
  all_goals rfl

theorem atot5802 : totK PA10K2 A10K2.u5802 = [0, 0, 463641269796, 2546737505276, 4145746850051, 2120148924223, 295422302315, 6354482628, 0, 0] := by
  rw [show A10K2.u5802 = KTree.node A10K2.t5808 (nat_lit 94984402) (nat_lit 14973476751) (nat_lit 0) A10K2.t5809 from rfl, totK_node, tot5808, tot5809]
  decide +kernel

theorem arows5803 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5803 = true := by
  rw [show A10K2.u5803 = KTree.node A10K2.t5810 (nat_lit 94991800) (nat_lit 12472043129) (nat_lit 0) A10K2.t5811 from rfl, allE_node, rows5810, irow5803, rows5811]
  all_goals rfl

theorem atot5803 : totK PA10K2 A10K2.u5803 = [0, 0, 260403760671, 2005984771720, 4361391171224, 3009612471075, 480805665473, 12926121504, 0, 0] := by
  rw [show A10K2.u5803 = KTree.node A10K2.t5810 (nat_lit 94991800) (nat_lit 12472043129) (nat_lit 0) A10K2.t5811 from rfl, totK_node, tot5810, tot5811]
  decide +kernel

theorem arows5805 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5805 = true := by
  rw [show A10K2.u5805 = KTree.node A10K2.t5812 (nat_lit 95006100) (nat_lit 8220109681) (nat_lit 0) A10K2.t5813 from rfl, allE_node, rows5812, irow5805, rows5813]
  all_goals rfl

theorem atot5805 : totK PA10K2 A10K2.u5805 = [0, 0, 0, 524045853115, 2733684575707, 4101978669349, 1907922035341, 339439695357, 25565504801, 0] := by
  rw [show A10K2.u5805 = KTree.node A10K2.t5812 (nat_lit 95006100) (nat_lit 8220109681) (nat_lit 0) A10K2.t5813 from rfl, totK_node, tot5812, tot5813]
  decide +kernel

theorem arows5806 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5806 = true := by
  rw [show A10K2.u5806 = KTree.node A10K2.t5814 (nat_lit 95012138) (nat_lit 12499765938) (nat_lit 0) A10K2.t5815 from rfl, allE_node, rows5814, irow5806, rows5815]
  all_goals rfl

theorem atot5806 : totK PA10K2 A10K2.u5806 = [0, 0, 0, 739001697644, 3122713923299, 3834775592928, 1483238932329, 186835151693, 5517381808, 0] := by
  rw [show A10K2.u5806 = KTree.node A10K2.t5814 (nat_lit 95012138) (nat_lit 12499765938) (nat_lit 0) A10K2.t5815 from rfl, totK_node, tot5814, tot5815]
  decide +kernel

theorem arows5809 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5809 = true := by
  rw [show A10K2.u5809 = KTree.node A10K2.t5816 (nat_lit 95020218) (nat_lit 15041214133) (nat_lit 0) A10K2.t5817 from rfl, allE_node, rows5816, irow5809, rows5817]
  all_goals rfl

theorem atot5809 : totK PA10K2 A10K2.u5809 = [0, 0, 270642845702, 1270087991144, 2814318195387, 3492093942744, 1578995794860, 209974721294, 6121173289, 0] := by
  rw [show A10K2.u5809 = KTree.node A10K2.t5816 (nat_lit 95020218) (nat_lit 15041214133) (nat_lit 0) A10K2.t5817 from rfl, totK_node, tot5816, tot5817]
  decide +kernel

theorem arows5810 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5810 = true := by
  rw [show A10K2.u5810 = KTree.node A10K2.t5818 (nat_lit 95031636) (nat_lit 12318947998) (nat_lit 0) A10K2.t5819 from rfl, allE_node, rows5818, irow5810, rows5819]
  all_goals rfl

theorem atot5810 : totK PA10K2 A10K2.u5810 = [0, 0, 456221090788, 2248093352617, 3767002626275, 2276767807491, 466588614986, 30402056026, 0, 0] := by
  rw [show A10K2.u5810 = KTree.node A10K2.t5818 (nat_lit 95031636) (nat_lit 12318947998) (nat_lit 0) A10K2.t5819 from rfl, totK_node, tot5818, tot5819]
  decide +kernel

theorem arows5812 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5812 = true := by
  rw [show A10K2.u5812 = KTree.node A10K2.t5820 (nat_lit 95038619) (nat_lit 9975195466) (nat_lit 0) A10K2.t5821 from rfl, allE_node, rows5820, irow5812, rows5821]
  all_goals rfl

theorem atot5812 : totK PA10K2 A10K2.u5812 = [0, 0, 604896214083, 2762323326245, 3965513135048, 2021504738912, 362632202874, 25734533292, 0, 0] := by
  rw [show A10K2.u5812 = KTree.node A10K2.t5820 (nat_lit 95038619) (nat_lit 9975195466) (nat_lit 0) A10K2.t5821 from rfl, totK_node, tot5820, tot5821]
  decide +kernel

theorem arows5813 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5813 = true := by
  rw [show A10K2.u5813 = KTree.node A10K2.t5822 (nat_lit 95044037) (nat_lit 5102077419) (nat_lit 0) A10K2.t5823 from rfl, allE_node, rows5822, irow5813, rows5823]
  all_goals rfl

theorem atot5813 : totK PA10K2 A10K2.u5813 = [0, 0, 701445824746, 2727396579430, 3739042478818, 1996753334350, 268884703740, 6034215561, 0, 0] := by
  rw [show A10K2.u5813 = KTree.node A10K2.t5822 (nat_lit 95044037) (nat_lit 5102077419) (nat_lit 0) A10K2.t5823 from rfl, totK_node, tot5822, tot5823]
  decide +kernel

theorem arows5819 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5819 = true := by
  rw [show A10K2.u5819 = KTree.node A10K2.t5824 (nat_lit 95049761) (nat_lit 9986687839) (nat_lit 0) A10K2.t5825 from rfl, allE_node, rows5824, irow5819, rows5825]
  all_goals rfl

theorem atot5819 : totK PA10K2 A10K2.u5819 = [0, 0, 112111361307, 1781898337635, 4187653423154, 2747609858175, 478422404049, 26172145312, 0, 0] := by
  rw [show A10K2.u5819 = KTree.node A10K2.t5824 (nat_lit 95049761) (nat_lit 9986687839) (nat_lit 0) A10K2.t5825 from rfl, totK_node, tot5824, tot5825]
  decide +kernel

theorem arows5820 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5820 = true := by
  rw [show A10K2.u5820 = KTree.node A10K2.t5826 (nat_lit 95069887) (nat_lit 6846167004) (nat_lit 128) A10K2.t5827 from rfl, allE_node, rows5826, irow5820, rows5827]
  all_goals rfl

theorem atot5820 : totK PA10K2 A10K2.u5820 = [0, 0, 0, 1058593806861, 3804945377671, 3774099120598, 904553858852, 44211540368, 0, 0] := by
  rw [show A10K2.u5820 = KTree.node A10K2.t5826 (nat_lit 95069887) (nat_lit 6846167004) (nat_lit 128) A10K2.t5827 from rfl, totK_node, tot5826, tot5827]
  decide +kernel

theorem arows5822 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5822 = true := by
  rw [show A10K2.u5822 = KTree.node A10K2.t5828 (nat_lit 95078120) (nat_lit 4597275155) (nat_lit 0) A10K2.t5829 from rfl, allE_node, rows5828, irow5822, rows5829]
  all_goals rfl

theorem atot5822 : totK PA10K2 A10K2.u5822 = [0, 0, 0, 809799373458, 3319155776336, 3886958089680, 1171686078080, 89385601782, 0, 0] := by
  rw [show A10K2.u5822 = KTree.node A10K2.t5828 (nat_lit 95078120) (nat_lit 4597275155) (nat_lit 0) A10K2.t5829 from rfl, totK_node, tot5828, tot5829]
  decide +kernel

theorem arows5823 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5823 = true := by
  rw [show A10K2.u5823 = KTree.node A10K2.t5830 (nat_lit 95102350) (nat_lit 14695116818) (nat_lit 0) A10K2.t5831 from rfl, allE_node, rows5830, irow5823, rows5831]
  all_goals rfl

theorem atot5823 : totK PA10K2 A10K2.u5823 = [0, 0, 773889436601, 2493455572196, 2755502639684, 2150451288292, 1198961431070, 233528391130, 6354482628, 0] := by
  rw [show A10K2.u5823 = KTree.node A10K2.t5830 (nat_lit 95102350) (nat_lit 14695116818) (nat_lit 0) A10K2.t5831 from rfl, totK_node, tot5830, tot5831]
  decide +kernel

theorem arows5826 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5826 = true := by
  rw [show A10K2.u5826 = KTree.node A10K2.t5832 (nat_lit 95107284) (nat_lit 11710791693) (nat_lit 0) A10K2.t5833 from rfl, allE_node, rows5832, irow5826, rows5833]
  all_goals rfl

theorem atot5826 : totK PA10K2 A10K2.u5826 = [0, 0, 287800699719, 1996675243698, 4118601166550, 2912125532992, 596639373771, 31522233512, 0, 0] := by
  rw [show A10K2.u5826 = KTree.node A10K2.t5832 (nat_lit 95107284) (nat_lit 11710791693) (nat_lit 0) A10K2.t5833 from rfl, totK_node, tot5832, tot5833]
  decide +kernel

theorem arows5827 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5827 = true := by
  rw [show A10K2.u5827 = KTree.node A10K2.t5834 (nat_lit 95122789) (nat_lit 6776729326) (nat_lit 0) A10K2.t5835 from rfl, allE_node, rows5834, irow5827, rows5835]
  all_goals rfl

theorem atot5827 : totK PA10K2 A10K2.u5827 = [0, 0, 614791512994, 2718982059437, 4159941216425, 2310934243609, 329428730992, 6962742351, 0, 0] := by
  rw [show A10K2.u5827 = KTree.node A10K2.t5834 (nat_lit 95122789) (nat_lit 6776729326) (nat_lit 0) A10K2.t5835 from rfl, totK_node, tot5834, tot5835]
  decide +kernel

theorem arows5829 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5829 = true := by
  rw [show A10K2.u5829 = KTree.node A10K2.t5836 (nat_lit 95423950) (nat_lit 14788148207) (nat_lit 0) A10K2.t5837 from rfl, allE_node, rows5836, irow5829, rows5837]
  all_goals rfl

theorem atot5829 : totK PA10K2 A10K2.u5829 = [0, 0, 490159822480, 2478007946880, 3957553268194, 2137875593463, 379459528818, 25371180993, 0, 0] := by
  rw [show A10K2.u5829 = KTree.node A10K2.t5836 (nat_lit 95423950) (nat_lit 14788148207) (nat_lit 0) A10K2.t5837 from rfl, totK_node, tot5836, tot5837]
  decide +kernel

theorem arows5830 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5830 = true := by
  rw [show A10K2.u5830 = KTree.node A10K2.t5838 (nat_lit 95437381) (nat_lit 5962076897) (nat_lit 0) A10K2.t5839 from rfl, allE_node, rows5838, irow5830, rows5839]
  all_goals rfl

theorem atot5830 : totK PA10K2 A10K2.u5830 = [0, 0, 779788147571, 2969484270803, 3727546197278, 1741130753408, 221515602542, 5460492893, 0, 0] := by
  rw [show A10K2.u5830 = KTree.node A10K2.t5838 (nat_lit 95437381) (nat_lit 5962076897) (nat_lit 0) A10K2.t5839 from rfl, totK_node, tot5838, tot5839]
  decide +kernel

theorem arows5834 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5834 = true := by
  rw [show A10K2.u5834 = KTree.node A10K2.t5840 (nat_lit 95443271) (nat_lit 4555883597) (nat_lit 0) A10K2.t5841 from rfl, allE_node, rows5840, irow5834, rows5841]
  all_goals rfl

theorem atot5834 : totK PA10K2 A10K2.u5834 = [0, 0, 458520426296, 2510380548110, 4142946495894, 2110773062072, 301105607360, 6354482628, 0, 0] := by
  rw [show A10K2.u5834 = KTree.node A10K2.t5840 (nat_lit 95443271) (nat_lit 4555883597) (nat_lit 0) A10K2.t5841 from rfl, totK_node, tot5840, tot5841]
  decide +kernel

theorem arows5835 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5835 = true := by
  rw [show A10K2.u5835 = KTree.node A10K2.t5842 (nat_lit 95453682) (nat_lit 8699173401) (nat_lit 0) A10K2.t5843 from rfl, allE_node, rows5842, irow5835, rows5843]
  all_goals rfl

theorem atot5835 : totK PA10K2 A10K2.u5835 = [0, 0, 0, 1209093264489, 4023200125036, 3548367851886, 687964478836, 38075759485, 0, 0] := by
  rw [show A10K2.u5835 = KTree.node A10K2.t5842 (nat_lit 95453682) (nat_lit 8699173401) (nat_lit 0) A10K2.t5843 from rfl, totK_node, tot5842, tot5843]
  decide +kernel

theorem arows5837 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5837 = true := by
  rw [show A10K2.u5837 = KTree.node A10K2.t5844 (nat_lit 95459669) (nat_lit 6717794447) (nat_lit 0) A10K2.t5845 from rfl, allE_node, rows5844, irow5837, rows5845]
  all_goals rfl

theorem atot5837 : totK PA10K2 A10K2.u5837 = [0, 0, 0, 377675826816, 2180568705841, 3841298436110, 2213575704754, 468143748032, 30220878370, 0] := by
  rw [show A10K2.u5837 = KTree.node A10K2.t5844 (nat_lit 95459669) (nat_lit 6717794447) (nat_lit 0) A10K2.t5845 from rfl, totK_node, tot5844, tot5845]
  decide +kernel

theorem arows5838 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5838 = true := by
  rw [show A10K2.u5838 = KTree.node A10K2.t5846 (nat_lit 95473927) (nat_lit 9489106768) (nat_lit 0) A10K2.t5847 from rfl, allE_node, rows5846, irow5838, rows5847]
  all_goals rfl

theorem atot5838 : totK PA10K2 A10K2.u5838 = [0, 0, 0, 582324954846, 2791115330029, 4037933682682, 1709539850711, 204530396330, 5546304973, 0] := by
  rw [show A10K2.u5838 = KTree.node A10K2.t5846 (nat_lit 95473927) (nat_lit 9489106768) (nat_lit 0) A10K2.t5847 from rfl, totK_node, tot5846, tot5847]
  decide +kernel

theorem arows5841 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5841 = true := by
  rw [show A10K2.u5841 = KTree.node A10K2.t5848 (nat_lit 95495940) (nat_lit 12113968189) (nat_lit 0) A10K2.t5849 from rfl, allE_node, rows5848, irow5841, rows5849]
  all_goals rfl

theorem atot5841 : totK PA10K2 A10K2.u5841 = [0, 0, 800824215886, 3078139799118, 3863203256724, 1726764322132, 203276177544, 9556858200, 0, 0] := by
  rw [show A10K2.u5841 = KTree.node A10K2.t5848 (nat_lit 95495940) (nat_lit 12113968189) (nat_lit 0) A10K2.t5849 from rfl, totK_node, tot5848, tot5849]
  decide +kernel

theorem arows5842 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5842 = true := by
  rw [show A10K2.u5842 = KTree.node A10K2.t5850 (nat_lit 95500589) (nat_lit 6639924910) (nat_lit 0) A10K2.t5851 from rfl, allE_node, rows5850, irow5842, rows5851]
  all_goals rfl

theorem atot5842 : totK PA10K2 A10K2.u5842 = [0, 0, 311731273616, 1834917307378, 3801578236738, 2893674017741, 564562003081, 31768748853, 0, 0] := by
  rw [show A10K2.u5842 = KTree.node A10K2.t5850 (nat_lit 95500589) (nat_lit 6639924910) (nat_lit 0) A10K2.t5851 from rfl, totK_node, tot5850, tot5851]
  decide +kernel

theorem arows5844 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5844 = true := by
  rw [show A10K2.u5844 = KTree.node A10K2.t5852 (nat_lit 95505180) (nat_lit 11988937714) (nat_lit 0) A10K2.t5853 from rfl, allE_node, rows5852, irow5844, rows5853]
  all_goals rfl

theorem atot5844 : totK PA10K2 A10K2.u5844 = [0, 0, 468642839883, 2666604883459, 4291724751875, 1931530086630, 175378113633, 0, 0, 0] := by
  rw [show A10K2.u5844 = KTree.node A10K2.t5852 (nat_lit 95505180) (nat_lit 11988937714) (nat_lit 0) A10K2.t5853 from rfl, totK_node, tot5852, tot5853]
  decide +kernel

theorem arows5845 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5845 = true := by
  rw [show A10K2.u5845 = KTree.node A10K2.t5854 (nat_lit 95515922) (nat_lit 15182336454) (nat_lit 0) A10K2.t5855 from rfl, allE_node, rows5854, irow5845, rows5855]
  all_goals rfl

theorem atot5845 : totK PA10K2 A10K2.u5845 = [0, 0, 461607179050, 2269636876137, 3903426218652, 2581914421514, 504291354398, 28519990413, 0, 0] := by
  rw [show A10K2.u5845 = KTree.node A10K2.t5854 (nat_lit 95515922) (nat_lit 15182336454) (nat_lit 0) A10K2.t5855 from rfl, totK_node, tot5854, tot5855]
  decide +kernel

theorem arows5850 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5850 = true := by
  rw [show A10K2.u5850 = KTree.node A10K2.t5856 (nat_lit 95530738) (nat_lit 14849180383) (nat_lit 0) A10K2.t5857 from rfl, allE_node, rows5856, irow5850, rows5857]
  all_goals rfl

theorem atot5850 : totK PA10K2 A10K2.u5850 = [0, 0, 0, 490383956341, 2483390702868, 3944660269378, 1963202099515, 367217457621, 25130442608, 0] := by
  rw [show A10K2.u5850 = KTree.node A10K2.t5856 (nat_lit 95530738) (nat_lit 14849180383) (nat_lit 0) A10K2.t5857 from rfl, totK_node, tot5856, tot5857]
  decide +kernel

theorem arows5851 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5851 = true := by
  rw [show A10K2.u5851 = KTree.node A10K2.t5858 (nat_lit 95536854) (nat_lit 13276597812) (nat_lit 0) A10K2.t5859 from rfl, allE_node, rows5858, irow5851, rows5859]
  all_goals rfl

theorem atot5851 : totK PA10K2 A10K2.u5851 = [0, 0, 0, 776948436827, 3326338252410, 3903556006516, 1286142568624, 151812195226, 5517381808, 0] := by
  rw [show A10K2.u5851 = KTree.node A10K2.t5858 (nat_lit 95536854) (nat_lit 13276597812) (nat_lit 0) A10K2.t5859 from rfl, totK_node, tot5858, tot5859]
  decide +kernel

theorem arows5853 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5853 = true := by
  rw [show A10K2.u5853 = KTree.node A10K2.t5860 (nat_lit 95544732) (nat_lit 8660900068) (nat_lit 0) A10K2.t5861 from rfl, allE_node, rows5860, irow5853, rows5861]
  all_goals rfl

theorem atot5853 : totK PA10K2 A10K2.u5853 = [0, 0, 286479695196, 1429928056323, 2949908647165, 3110010401949, 1419679327909, 216297653748, 6121173289, 0] := by
  rw [show A10K2.u5853 = KTree.node A10K2.t5860 (nat_lit 95544732) (nat_lit 8660900068) (nat_lit 0) A10K2.t5861 from rfl, totK_node, tot5860, tot5861]
  decide +kernel

theorem arows5854 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5854 = true := by
  rw [show A10K2.u5854 = KTree.node A10K2.t5862 (nat_lit 95555642) (nat_lit 6478019593) (nat_lit 0) A10K2.t5863 from rfl, allE_node, rows5862, irow5854, rows5863]
  all_goals rfl

theorem atot5854 : totK PA10K2 A10K2.u5854 = [0, 0, 446546377714, 2234698032514, 3835862817871, 2374869891795, 423633888363, 25371180993, 0, 0] := by
  rw [show A10K2.u5854 = KTree.node A10K2.t5862 (nat_lit 95555642) (nat_lit 6478019593) (nat_lit 0) A10K2.t5863 from rfl, totK_node, tot5862, tot5863]
  decide +kernel

theorem arows5857 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5857 = true := by
  rw [show A10K2.u5857 = KTree.node A10K2.t5864 (nat_lit 95561952) (nat_lit 8350058040) (nat_lit 0) A10K2.t5865 from rfl, allE_node, rows5864, irow5857, rows5865]
  all_goals rfl

theorem atot5857 : totK PA10K2 A10K2.u5857 = [0, 0, 736374845472, 3105065794330, 3949050170692, 1521761608794, 162602606890, 5460492893, 0, 0] := by
  rw [show A10K2.u5857 = KTree.node A10K2.t5864 (nat_lit 95561952) (nat_lit 8350058040) (nat_lit 0) A10K2.t5865 from rfl, totK_node, tot5864, tot5865]
  decide +kernel

theorem arows5858 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5858 = true := by
  rw [show A10K2.u5858 = KTree.node A10K2.t5866 (nat_lit 95567881) (nat_lit 9802626900) (nat_lit 0) A10K2.t5867 from rfl, allE_node, rows5866, irow5858, rows5867]
  all_goals rfl

theorem atot5858 : totK PA10K2 A10K2.u5858 = [0, 0, 537202621427, 2266334425857, 3549850506730, 2444647004625, 530378174609, 31768748853, 0, 0] := by
  rw [show A10K2.u5858 = KTree.node A10K2.t5866 (nat_lit 95567881) (nat_lit 9802626900) (nat_lit 0) A10K2.t5867 from rfl, totK_node, tot5866, tot5867]
  decide +kernel

theorem arows5860 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5860 = true := by
  rw [show A10K2.u5860 = KTree.node A10K2.t5868 (nat_lit 95573140) (nat_lit 12505876131) (nat_lit 0) A10K2.t5869 from rfl, allE_node, rows5868, irow5860, rows5869]
  all_goals rfl

theorem atot5860 : totK PA10K2 A10K2.u5860 = [0, 0, 311053418201, 2245148888863, 4281820924713, 2320148441185, 308845306249, 6354482628, 0, 0] := by
  rw [show A10K2.u5860 = KTree.node A10K2.t5868 (nat_lit 95573140) (nat_lit 12505876131) (nat_lit 0) A10K2.t5869 from rfl, totK_node, tot5868, tot5869]
  decide +kernel

theorem arows5861 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5861 = true := by
  rw [show A10K2.u5861 = KTree.node A10K2.t5870 (nat_lit 95587337) (nat_lit 9732766126) (nat_lit 0) A10K2.t5871 from rfl, allE_node, rows5870, irow5861, rows5871]
  all_goals rfl

theorem atot5861 : totK PA10K2 A10K2.u5861 = [0, 0, 0, 978281950216, 3537336971733, 3753416856791, 988813432551, 64468465779, 0, 0] := by
  rw [show A10K2.u5861 = KTree.node A10K2.t5870 (nat_lit 95587337) (nat_lit 9732766126) (nat_lit 0) A10K2.t5871 from rfl, totK_node, tot5870, tot5871]
  decide +kernel

theorem arows5865 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5865 = true := by
  rw [show A10K2.u5865 = KTree.node A10K2.t5872 (nat_lit 95601094) (nat_lit 12249892016) (nat_lit 0) A10K2.t5873 from rfl, allE_node, rows5872, irow5865, rows5873]
  all_goals rfl

theorem atot5865 : totK PA10K2 A10K2.u5865 = [0, 0, 0, 1054770501607, 3660721527565, 3677853336016, 937790191544, 63057910800, 0, 0] := by
  rw [show A10K2.u5865 = KTree.node A10K2.t5872 (nat_lit 95601094) (nat_lit 12249892016) (nat_lit 0) A10K2.t5873 from rfl, totK_node, tot5872, tot5873]
  decide +kernel

theorem arows5866 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5866 = true := by
  rw [show A10K2.u5866 = KTree.node A10K2.t5874 (nat_lit 95606853) (nat_lit 6202701764) (nat_lit 0) A10K2.t5875 from rfl, allE_node, rows5874, irow5866, rows5875]
  all_goals rfl

theorem atot5866 : totK PA10K2 A10K2.u5866 = [0, 0, 0, 428246377555, 2564887185535, 4115532896524, 1912302637166, 286048911365, 6354482628, 0] := by
  rw [show A10K2.u5866 = KTree.node A10K2.t5874 (nat_lit 95606853) (nat_lit 6202701764) (nat_lit 0) A10K2.t5875 from rfl, totK_node, tot5874, tot5875]
  decide +kernel

theorem arows5868 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5868 = true := by
  rw [show A10K2.u5868 = KTree.node A10K2.t5876 (nat_lit 95686578) (nat_lit 6854066531) (nat_lit 0) A10K2.t5877 from rfl, allE_node, rows5876, irow5868, rows5877]
  all_goals rfl

theorem atot5868 : totK PA10K2 A10K2.u5868 = [0, 0, 0, 488672855123, 2400451773870, 3971862564449, 2040363513938, 371408807234, 24941563133, 0] := by
  rw [show A10K2.u5868 = KTree.node A10K2.t5876 (nat_lit 95686578) (nat_lit 6854066531) (nat_lit 0) A10K2.t5877 from rfl, totK_node, tot5876, tot5877]
  decide +kernel

theorem arows5869 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5869 = true := by
  rw [show A10K2.u5869 = KTree.node A10K2.t5878 (nat_lit 95700330) (nat_lit 9914255567) (nat_lit 0) A10K2.t5879 from rfl, allE_node, rows5878, irow5869, rows5879]
  all_goals rfl

theorem atot5869 : totK PA10K2 A10K2.u5869 = [0, 0, 0, 774854541756, 3241168949544, 3885844419880, 1398503764231, 172746301049, 5447185874, 0] := by
  rw [show A10K2.u5869 = KTree.node A10K2.t5878 (nat_lit 95700330) (nat_lit 9914255567) (nat_lit 0) A10K2.t5879 from rfl, totK_node, tot5878, tot5879]
  decide +kernel

theorem arows5872 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5872 = true := by
  rw [show A10K2.u5872 = KTree.node A10K2.t5880 (nat_lit 95707462) (nat_lit 11785411376) (nat_lit 0) A10K2.t5881 from rfl, allE_node, rows5880, irow5872, rows5881]
  all_goals rfl

theorem atot5872 : totK PA10K2 A10K2.u5872 = [0, 0, 0, 767269006385, 2968054332979, 3762381589875, 1708133354195, 281618282186, 6354482628, 0] := by
  rw [show A10K2.u5872 = KTree.node A10K2.t5880 (nat_lit 95707462) (nat_lit 11785411376) (nat_lit 0) A10K2.t5881 from rfl, totK_node, tot5880, tot5881]
  decide +kernel

theorem arows5873 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5873 = true := by
  rw [show A10K2.u5873 = KTree.node A10K2.t5882 (nat_lit 95760114) (nat_lit 14849180383) (nat_lit 0) A10K2.t5883 from rfl, allE_node, rows5882, irow5873, rows5883]
  all_goals rfl

theorem atot5873 : totK PA10K2 A10K2.u5873 = [0, 0, 0, 490584767793, 2492532234898, 3997668476653, 2028085525247, 365548846679, 25299471099, 0] := by
  rw [show A10K2.u5873 = KTree.node A10K2.t5882 (nat_lit 95760114) (nat_lit 14849180383) (nat_lit 0) A10K2.t5883 from rfl, totK_node, tot5882, tot5883]
  decide +kernel

theorem arows5875 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5875 = true := by
  rw [show A10K2.u5875 = KTree.node A10K2.t5884 (nat_lit 95766178) (nat_lit 14360341732) (nat_lit 0) A10K2.t5885 from rfl, allE_node, rows5884, irow5875, rows5885]
  all_goals rfl

theorem atot5875 : totK PA10K2 A10K2.u5875 = [0, 0, 0, 775434810997, 3206100126063, 3842729471842, 1434640559482, 180983906574, 5718040558, 0] := by
  rw [show A10K2.u5875 = KTree.node A10K2.t5884 (nat_lit 95766178) (nat_lit 14360341732) (nat_lit 0) A10K2.t5885 from rfl, totK_node, tot5884, tot5885]
  decide +kernel

theorem arows5876 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5876 = true := by
  rw [show A10K2.u5876 = KTree.node A10K2.t5886 (nat_lit 95773985) (nat_lit 7246840781) (nat_lit 0) A10K2.t5887 from rfl, allE_node, rows5886, irow5876, rows5887]
  all_goals rfl

theorem atot5876 : totK PA10K2 A10K2.u5876 = [0, 0, 0, 747650834336, 2978514122787, 3780074234174, 1720907398828, 288766099099, 6354482628, 0] := by
  rw [show A10K2.u5876 = KTree.node A10K2.t5886 (nat_lit 95773985) (nat_lit 7246840781) (nat_lit 0) A10K2.t5887 from rfl, totK_node, tot5886, tot5887]
  decide +kernel

theorem arows5884 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5884 = true := by
  rw [show A10K2.u5884 = KTree.node A10K2.t5888 (nat_lit 95817798) (nat_lit 14327027697) (nat_lit 0) A10K2.t5889 from rfl, allE_node, rows5888, irow5884, rows5889]
  all_goals rfl

theorem atot5884 : totK PA10K2 A10K2.u5884 = [0, 0, 0, 444597179661, 2252917288458, 3827394797766, 2215881525612, 447182766279, 30074883546, 0] := by
  rw [show A10K2.u5884 = KTree.node A10K2.t5888 (nat_lit 95817798) (nat_lit 14327027697) (nat_lit 0) A10K2.t5889 from rfl, totK_node, tot5888, tot5889]
  decide +kernel

theorem arows5885 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5885 = true := by
  rw [show A10K2.u5885 = KTree.node A10K2.t5890 (nat_lit 95824214) (nat_lit 9810340264) (nat_lit 0) A10K2.t5891 from rfl, allE_node, rows5890, irow5885, rows5891]
  all_goals rfl

theorem atot5885 : totK PA10K2 A10K2.u5885 = [0, 0, 0, 733980708112, 2965063489999, 3779817903692, 1587712108913, 263457371970, 19575605953, 0] := by
  rw [show A10K2.u5885 = KTree.node A10K2.t5890 (nat_lit 95824214) (nat_lit 9810340264) (nat_lit 0) A10K2.t5891 from rfl, totK_node, tot5890, tot5891]
  decide +kernel

theorem arows5887 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5887 = true := by
  rw [show A10K2.u5887 = KTree.node A10K2.t5892 (nat_lit 95830532) (nat_lit 11938764297) (nat_lit 0) A10K2.t5893 from rfl, allE_node, rows5892, irow5887, rows5893]
  all_goals rfl

theorem atot5887 : totK PA10K2 A10K2.u5887 = [0, 0, 0, 727383222114, 2825975630726, 3695713450473, 1773887212877, 288018970344, 11427838733, 0] := by
  rw [show A10K2.u5887 = KTree.node A10K2.t5892 (nat_lit 95830532) (nat_lit 11938764297) (nat_lit 0) A10K2.t5893 from rfl, totK_node, tot5892, tot5893]
  decide +kernel

theorem arows5888 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5888 = true := by
  rw [show A10K2.u5888 = KTree.node A10K2.t5894 (nat_lit 95836196) (nat_lit 13755931144) (nat_lit 0) A10K2.t5895 from rfl, allE_node, rows5894, irow5888, rows5895]
  all_goals rfl

theorem atot5888 : totK PA10K2 A10K2.u5888 = [0, 0, 0, 113126642960, 1777983012670, 4244552252787, 2625111638101, 466063329021, 25807237568, 0] := by
  rw [show A10K2.u5888 = KTree.node A10K2.t5894 (nat_lit 95836196) (nat_lit 13755931144) (nat_lit 0) A10K2.t5895 from rfl, totK_node, tot5894, tot5895]
  decide +kernel

theorem arows5891 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5891 = true := by
  rw [show A10K2.u5891 = KTree.node A10K2.t5896 (nat_lit 95856049) (nat_lit 1526893024) (nat_lit 0) A10K2.t5897 from rfl, allE_node, rows5896, irow5891, rows5897]
  all_goals rfl

theorem atot5891 : totK PA10K2 A10K2.u5891 = [0, 0, 0, 0, 1246087965286, 3855071168479, 3285509349296, 819539103468, 43431380149, 0] := by
  rw [show A10K2.u5891 = KTree.node A10K2.t5896 (nat_lit 95856049) (nat_lit 1526893024) (nat_lit 0) A10K2.t5897 from rfl, totK_node, tot5896, tot5897]
  decide +kernel

theorem arows5892 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5892 = true := by
  rw [show A10K2.u5892 = KTree.node A10K2.t5898 (nat_lit 95864725) (nat_lit 5192459796) (nat_lit 0) A10K2.t5899 from rfl, allE_node, rows5898, irow5892, rows5899]
  all_goals rfl

theorem atot5892 : totK PA10K2 A10K2.u5892 = [0, 0, 0, 0, 736636004605, 3220742773235, 3744089594432, 1212169378863, 102081032701, 0] := by
  rw [show A10K2.u5892 = KTree.node A10K2.t5898 (nat_lit 95864725) (nat_lit 5192459796) (nat_lit 0) A10K2.t5899 from rfl, totK_node, tot5898, tot5899]
  decide +kernel

theorem arows5894 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5894 = true := by
  rw [show A10K2.u5894 = KTree.node A10K2.t5900 (nat_lit 100663820) (nat_lit 11039129715) (nat_lit 0) A10K2.t5901 from rfl, allE_node, rows5900, irow5894, rows5901]
  all_goals rfl

theorem atot5894 : totK PA10K2 A10K2.u5894 = [825194005158, 2683431091492, 2478297740176, 603456998753, 32040661968, 374263588326, 1233212591026, 990914908768, 213642913445, 6354482628] := by
  rw [show A10K2.u5894 = KTree.node A10K2.t5900 (nat_lit 100663820) (nat_lit 11039129715) (nat_lit 0) A10K2.t5901 from rfl, totK_node, tot5900, tot5901]
  decide +kernel

theorem arows5895 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5895 = true := by
  rw [show A10K2.u5895 = KTree.node A10K2.t5902 (nat_lit 100668311) (nat_lit 13548381217) (nat_lit 0) A10K2.t5903 from rfl, allE_node, rows5902, irow5895, rows5903]
  all_goals rfl

theorem atot5895 : totK PA10K2 A10K2.u5895 = [233443272613, 1770584389017, 4046089789377, 2999375730059, 603123193524, 30831673886, 0, 0, 0, 0] := by
  rw [show A10K2.u5895 = KTree.node A10K2.t5902 (nat_lit 100668311) (nat_lit 13548381217) (nat_lit 0) A10K2.t5903 from rfl, totK_node, tot5902, tot5903]
  decide +kernel

theorem arows5899 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5899 = true := by
  rw [show A10K2.u5899 = KTree.node A10K2.t5904 (nat_lit 100682053) (nat_lit 6961576414) (nat_lit 0) A10K2.t5905 from rfl, allE_node, rows5904, irow5899, rows5905]
  all_goals rfl

theorem atot5899 : totK PA10K2 A10K2.u5899 = [482777079011, 2748021246675, 4079261688649, 1631248886176, 127902322250, 0, 0, 0, 0, 0] := by
  rw [show A10K2.u5899 = KTree.node A10K2.t5904 (nat_lit 100682053) (nat_lit 6961576414) (nat_lit 0) A10K2.t5905 from rfl, totK_node, tot5904, tot5905]
  decide +kernel

theorem arows5900 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5900 = true := by
  rw [show A10K2.u5900 = KTree.node A10K2.t5906 (nat_lit 100689364) (nat_lit 3633566512) (nat_lit 0) A10K2.t5907 from rfl, allE_node, rows5906, irow5900, rows5907]
  all_goals rfl

theorem atot5900 : totK PA10K2 A10K2.u5900 = [787080240479, 3048866587659, 3967114535917, 1875020448812, 273423191379, 6354482628, 0, 0, 0, 0] := by
  rw [show A10K2.u5900 = KTree.node A10K2.t5906 (nat_lit 100689364) (nat_lit 3633566512) (nat_lit 0) A10K2.t5907 from rfl, totK_node, tot5906, tot5907]
  decide +kernel

theorem arows5902 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5902 = true := by
  rw [show A10K2.u5902 = KTree.node A10K2.t5908 (nat_lit 100695489) (nat_lit 9589311726) (nat_lit 0) A10K2.t5909 from rfl, allE_node, rows5908, irow5902, rows5909]
  all_goals rfl

theorem atot5902 : totK PA10K2 A10K2.u5902 = [0, 950900579710, 3638086108971, 4077723248743, 1261201388398, 88333970525, 0, 0, 0, 0] := by
  rw [show A10K2.u5902 = KTree.node A10K2.t5908 (nat_lit 100695489) (nat_lit 9589311726) (nat_lit 0) A10K2.t5909 from rfl, totK_node, tot5908, tot5909]
  decide +kernel

theorem arows5903 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5903 = true := by
  rw [show A10K2.u5903 = KTree.node A10K2.t5910 (nat_lit 100700039) (nat_lit 14605439975) (nat_lit 0) A10K2.t5911 from rfl, allE_node, rows5910, irow5903, rows5911]
  all_goals rfl

theorem atot5903 : totK PA10K2 A10K2.u5903 = [0, 547280950923, 2605008974811, 3928615157859, 1998671210798, 390478982252, 25239774317, 0, 0, 0] := by
  rw [show A10K2.u5903 = KTree.node A10K2.t5910 (nat_lit 100700039) (nat_lit 14605439975) (nat_lit 0) A10K2.t5911 from rfl, totK_node, tot5910, tot5911]
  decide +kernel

theorem arows5906 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5906 = true := by
  rw [show A10K2.u5906 = KTree.node A10K2.t5912 (nat_lit 100713315) (nat_lit 5036384781) (nat_lit 0) A10K2.t5913 from rfl, allE_node, rows5912, irow5906, rows5913]
  all_goals rfl

theorem atot5906 : totK PA10K2 A10K2.u5906 = [0, 679821306780, 2865251125162, 3769113428676, 1686175371240, 223334271906, 5410721913, 0, 0, 0] := by
  rw [show A10K2.u5906 = KTree.node A10K2.t5912 (nat_lit 100713315) (nat_lit 5036384781) (nat_lit 0) A10K2.t5913 from rfl, totK_node, tot5912, tot5913]
  decide +kernel

theorem arows5907 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5907 = true := by
  rw [show A10K2.u5907 = KTree.node A10K2.t5914 (nat_lit 100720996) (nat_lit 13141932967) (nat_lit 0) A10K2.t5915 from rfl, allE_node, rows5914, irow5907, rows5915]
  all_goals rfl

theorem atot5907 : totK PA10K2 A10K2.u5907 = [0, 784550567112, 3073898338258, 3929081518594, 1646292567760, 199248494970, 5546304973, 0, 0, 0] := by
  rw [show A10K2.u5907 = KTree.node A10K2.t5914 (nat_lit 100720996) (nat_lit 13141932967) (nat_lit 0) A10K2.t5915 from rfl, totK_node, tot5914, tot5915]
  decide +kernel

theorem arows5909 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5909 = true := by
  rw [show A10K2.u5909 = KTree.node A10K2.t5916 (nat_lit 100796448) (nat_lit 13959179896) (nat_lit 0) A10K2.t5917 from rfl, allE_node, rows5916, irow5909, rows5917]
  all_goals rfl

theorem atot5909 : totK PA10K2 A10K2.u5909 = [795409072615, 2960724657265, 3580395388784, 1923252736187, 584944848562, 50300197778, 0, 0, 0, 0] := by
  rw [show A10K2.u5909 = KTree.node A10K2.t5916 (nat_lit 100796448) (nat_lit 13959179896) (nat_lit 0) A10K2.t5917 from rfl, totK_node, tot5916, tot5917]
  decide +kernel

theorem arows5910 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5910 = true := by
  rw [show A10K2.u5910 = KTree.node A10K2.t5918 (nat_lit 100801299) (nat_lit 9468517272) (nat_lit 0) A10K2.t5919 from rfl, allE_node, rows5918, irow5910, rows5919]
  all_goals rfl

theorem atot5910 : totK PA10K2 A10K2.u5910 = [251956656316, 1852040011419, 3937200395649, 2819174008806, 582447781483, 30831673886, 0, 0, 0, 0] := by
  rw [show A10K2.u5910 = KTree.node A10K2.t5918 (nat_lit 100801299) (nat_lit 9468517272) (nat_lit 0) A10K2.t5919 from rfl, totK_node, tot5918, tot5919]
  decide +kernel

theorem arows5915 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5915 = true := by
  rw [show A10K2.u5915 = KTree.node A10K2.t5920 (nat_lit 100812101) (nat_lit 6926122644) (nat_lit 0) A10K2.t5921 from rfl, allE_node, rows5920, irow5915, rows5921]
  all_goals rfl

theorem atot5915 : totK PA10K2 A10K2.u5915 = [742419772272, 2941783066153, 3793410861571, 1688274597304, 222012075168, 6034215561, 0, 0, 0, 0] := by
  rw [show A10K2.u5915 = KTree.node A10K2.t5920 (nat_lit 100812101) (nat_lit 6926122644) (nat_lit 0) A10K2.t5921 from rfl, totK_node, tot5920, tot5921]
  decide +kernel

theorem arows5916 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5916 = true := by
  rw [show A10K2.u5916 = KTree.node A10K2.t5922 (nat_lit 100827413) (nat_lit 6796925496) (nat_lit 0) A10K2.t5923 from rfl, allE_node, rows5922, irow5916, rows5923]
  all_goals rfl

theorem atot5916 : totK PA10K2 A10K2.u5916 = [0, 1146264413782, 3844172462189, 3545192303062, 814153535802, 38342359577, 0, 0, 0, 0] := by
  rw [show A10K2.u5916 = KTree.node A10K2.t5922 (nat_lit 100827413) (nat_lit 6796925496) (nat_lit 0) A10K2.t5923 from rfl, totK_node, tot5922, tot5923]
  decide +kernel

theorem arows5918 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5918 = true := by
  rw [show A10K2.u5918 = KTree.node A10K2.t5924 (nat_lit 100843776) (nat_lit 14814158032) (nat_lit 0) A10K2.t5925 from rfl, allE_node, rows5924, irow5918, rows5925]
  all_goals rfl

theorem atot5918 : totK PA10K2 A10K2.u5918 = [0, 1053415267840, 3694155679157, 3734767775759, 1007789124085, 63417287647, 0, 0, 0, 0] := by
  rw [show A10K2.u5918 = KTree.node A10K2.t5924 (nat_lit 100843776) (nat_lit 14814158032) (nat_lit 0) A10K2.t5925 from rfl, totK_node, tot5924, tot5925]
  decide +kernel

theorem arows5919 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5919 = true := by
  rw [show A10K2.u5919 = KTree.node A10K2.t5926 (nat_lit 100849854) (nat_lit 11933677) (nat_lit 0) A10K2.t5927 from rfl, allE_node, rows5926, irow5919, rows5927]
  all_goals rfl

theorem atot5919 : totK PA10K2 A10K2.u5919 = [338679903066, 1256547057807, 2575757349575, 3251789792513, 1658017938999, 265773289542, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u5919 = KTree.node A10K2.t5926 (nat_lit 100849854) (nat_lit 11933677) (nat_lit 0) A10K2.t5927 from rfl, totK_node, tot5926, tot5927]
  decide +kernel

theorem arows5922 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5922 = true := by
  rw [show A10K2.u5922 = KTree.node A10K2.t5928 (nat_lit 100863959) (nat_lit 14217301965) (nat_lit 0) A10K2.t5929 from rfl, allE_node, rows5928, irow5922, rows5929]
  all_goals rfl

theorem atot5922 : totK PA10K2 A10K2.u5922 = [471804183793, 2319116175399, 3870121383721, 2518794293187, 522811957209, 25351274858, 0, 0, 0, 0] := by
  rw [show A10K2.u5922 = KTree.node A10K2.t5928 (nat_lit 100863959) (nat_lit 14217301965) (nat_lit 0) A10K2.t5929 from rfl, totK_node, tot5928, tot5929]
  decide +kernel

theorem arows5923 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5923 = true := by
  rw [show A10K2.u5923 = KTree.node A10K2.t5930 (nat_lit 100871615) (nat_lit 14297916367) (nat_lit 0) A10K2.t5931 from rfl, allE_node, rows5930, irow5923, rows5931]
  all_goals rfl

theorem atot5923 : totK PA10K2 A10K2.u5923 = [512353472697, 2658621262205, 4365767115840, 2430461699597, 391816519275, 25130312156, 0, 0, 0, 0] := by
  rw [show A10K2.u5923 = KTree.node A10K2.t5930 (nat_lit 100871615) (nat_lit 14297916367) (nat_lit 0) A10K2.t5931 from rfl, totK_node, tot5930, tot5931]
  decide +kernel

theorem arows5925 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5925 = true := by
  rw [show A10K2.u5925 = KTree.node A10K2.t5932 (nat_lit 100886238) (nat_lit 10313950122) (nat_lit 0) A10K2.t5933 from rfl, allE_node, rows5932, irow5925, rows5933]
  all_goals rfl

theorem atot5925 : totK PA10K2 A10K2.u5925 = [845700278790, 3331016985985, 4112185289550, 1617050830358, 149949364467, 0, 0, 0, 0, 0] := by
  rw [show A10K2.u5925 = KTree.node A10K2.t5932 (nat_lit 100886238) (nat_lit 10313950122) (nat_lit 0) A10K2.t5933 from rfl, totK_node, tot5932, tot5933]
  decide +kernel

theorem arows5926 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5926 = true := by
  rw [show A10K2.u5926 = KTree.node A10K2.t5934 (nat_lit 100892036) (nat_lit 6836740723) (nat_lit 0) A10K2.t5935 from rfl, allE_node, rows5934, irow5926, rows5935]
  all_goals rfl

theorem atot5926 : totK PA10K2 A10K2.u5926 = [0, 979653305130, 3677032222098, 4079058955739, 1244454778701, 83145843390, 0, 0, 0, 0] := by
  rw [show A10K2.u5926 = KTree.node A10K2.t5934 (nat_lit 100892036) (nat_lit 6836740723) (nat_lit 0) A10K2.t5935 from rfl, totK_node, tot5934, tot5935]
  decide +kernel

theorem arows5930 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5930 = true := by
  rw [show A10K2.u5930 = KTree.node A10K2.t5936 (nat_lit 100896649) (nat_lit 8367675134) (nat_lit 0) A10K2.t5937 from rfl, allE_node, rows5936, irow5930, rows5937]
  all_goals rfl

theorem atot5930 : totK PA10K2 A10K2.u5930 = [0, 499628035384, 2579831408364, 4175198370087, 2192635476718, 302294023714, 6904928264, 0, 0, 0] := by
  rw [show A10K2.u5930 = KTree.node A10K2.t5936 (nat_lit 100896649) (nat_lit 8367675134) (nat_lit 0) A10K2.t5937 from rfl, totK_node, tot5936, tot5937]
  decide +kernel

theorem arows5931 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5931 = true := by
  rw [show A10K2.u5931 = KTree.node A10K2.t5938 (nat_lit 100904524) (nat_lit 4769212833) (nat_lit 0) A10K2.t5939 from rfl, allE_node, rows5938, irow5931, rows5939]
  all_goals rfl

theorem atot5931 : totK PA10K2 A10K2.u5931 = [0, 595221967764, 2678419472774, 4222984836430, 2457087800005, 373300782330, 7047025452, 0, 0, 0] := by
  rw [show A10K2.u5931 = KTree.node A10K2.t5938 (nat_lit 100904524) (nat_lit 4769212833) (nat_lit 0) A10K2.t5939 from rfl, totK_node, tot5938, tot5939]
  decide +kernel

theorem arows5933 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5933 = true := by
  rw [show A10K2.u5933 = KTree.node A10K2.t5940 (nat_lit 100920374) (nat_lit 16595278098) (nat_lit 0) A10K2.t5941 from rfl, allE_node, rows5940, irow5933, rows5941]
  all_goals rfl

theorem atot5933 : totK PA10K2 A10K2.u5933 = [0, 750504392814, 3264979791605, 4209604225425, 1670554180799, 136774785454, 0, 0, 0, 0] := by
  rw [show A10K2.u5933 = KTree.node A10K2.t5940 (nat_lit 100920374) (nat_lit 16595278098) (nat_lit 0) A10K2.t5941 from rfl, totK_node, tot5940, tot5941]
  decide +kernel

theorem arows5934 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5934 = true := by
  rw [show A10K2.u5934 = KTree.node A10K2.t5942 (nat_lit 100924986) (nat_lit 11323210669) (nat_lit 0) A10K2.t5943 from rfl, allE_node, rows5942, irow5934, rows5943]
  all_goals rfl

theorem atot5934 : totK PA10K2 A10K2.u5934 = [0, 427178422353, 1939549692787, 3576992287396, 3037181301331, 879149173201, 61110126106, 0, 0, 0] := by
  rw [show A10K2.u5934 = KTree.node A10K2.t5942 (nat_lit 100924986) (nat_lit 11323210669) (nat_lit 0) A10K2.t5943 from rfl, totK_node, tot5942, tot5943]
  decide +kernel

theorem arows5937 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5937 = true := by
  rw [show A10K2.u5937 = KTree.node A10K2.t5944 (nat_lit 100929479) (nat_lit 14288936747) (nat_lit 0) A10K2.t5945 from rfl, allE_node, rows5944, irow5937, rows5945]
  all_goals rfl

theorem atot5937 : totK PA10K2 A10K2.u5937 = [0, 440177673483, 2352238787245, 3978400871259, 2277928197303, 429000939451, 25371180993, 0, 0, 0] := by
  rw [show A10K2.u5937 = KTree.node A10K2.t5944 (nat_lit 100929479) (nat_lit 14288936747) (nat_lit 0) A10K2.t5945 from rfl, totK_node, tot5944, tot5945]
  decide +kernel

theorem arows5938 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5938 = true := by
  rw [show A10K2.u5938 = KTree.node A10K2.t5946 (nat_lit 100942691) (nat_lit 5077399622) (nat_lit 0) A10K2.t5947 from rfl, allE_node, rows5946, irow5938, rows5947]
  all_goals rfl

theorem atot5938 : totK PA10K2 A10K2.u5938 = [0, 681396248112, 2878527864157, 3818164660593, 1692595515420, 220861237983, 5460492893, 0, 0, 0] := by
  rw [show A10K2.u5938 = KTree.node A10K2.t5946 (nat_lit 100942691) (nat_lit 5077399622) (nat_lit 0) A10K2.t5947 from rfl, totK_node, tot5946, tot5947]
  decide +kernel

theorem arows5940 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5940 = true := by
  rw [show A10K2.u5940 = KTree.node A10K2.t5948 (nat_lit 100950305) (nat_lit 9905063494) (nat_lit 0) A10K2.t5949 from rfl, allE_node, rows5948, irow5940, rows5949]
  all_goals rfl

theorem atot5940 : totK PA10K2 A10K2.u5940 = [0, 724276722652, 2900018749775, 3933292044931, 1802643522494, 211785329318, 5705019915, 0, 0, 0] := by
  rw [show A10K2.u5940 = KTree.node A10K2.t5948 (nat_lit 100950305) (nat_lit 9905063494) (nat_lit 0) A10K2.t5949 from rfl, totK_node, tot5948, tot5949]
  decide +kernel

theorem arows5941 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5941 = true := by
  rw [show A10K2.u5941 = KTree.node A10K2.t5950 (nat_lit 100955312) (nat_lit 10307510823) (nat_lit 0) A10K2.t5951 from rfl, allE_node, rows5950, irow5941, rows5951]
  all_goals rfl

theorem atot5941 : totK PA10K2 A10K2.u5941 = [0, 61859181966, 1548311637016, 4270047304186, 3390317424097, 729393880087, 35031173917, 0, 0, 0] := by
  rw [show A10K2.u5941 = KTree.node A10K2.t5950 (nat_lit 100955312) (nat_lit 10307510823) (nat_lit 0) A10K2.t5951 from rfl, totK_node, tot5950, tot5951]
  decide +kernel

theorem arows5947 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5947 = true := by
  rw [show A10K2.u5947 = KTree.node A10K2.t5952 (nat_lit 100961380) (nat_lit 11925582992) (nat_lit 0) A10K2.t5953 from rfl, allE_node, rows5952, irow5947, rows5953]
  all_goals rfl

theorem atot5947 : totK PA10K2 A10K2.u5947 = [0, 0, 645239498776, 2826751518814, 3879040335771, 1774459334800, 322633127833, 20060612110, 0, 0] := by
  rw [show A10K2.u5947 = KTree.node A10K2.t5952 (nat_lit 100961380) (nat_lit 11925582992) (nat_lit 0) A10K2.t5953 from rfl, totK_node, tot5952, tot5953]
  decide +kernel

theorem arows5948 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5948 = true := by
  rw [show A10K2.u5948 = KTree.node A10K2.t5954 (nat_lit 100974916) (nat_lit 12944906826) (nat_lit 0) A10K2.t5955 from rfl, allE_node, rows5954, irow5948, rows5955]
  all_goals rfl

theorem atot5948 : totK PA10K2 A10K2.u5948 = [0, 0, 674253939578, 2744373868643, 3613739464078, 1724073290280, 283980606755, 10545135740, 0, 0] := by
  rw [show A10K2.u5948 = KTree.node A10K2.t5954 (nat_lit 100974916) (nat_lit 12944906826) (nat_lit 0) A10K2.t5955 from rfl, totK_node, tot5954, tot5955]
  decide +kernel

theorem arows5950 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5950 = true := by
  rw [show A10K2.u5950 = KTree.node A10K2.t5956 (nat_lit 100981409) (nat_lit 7459055296) (nat_lit 0) A10K2.t5957 from rfl, allE_node, rows5956, irow5950, rows5957]
  all_goals rfl

theorem atot5950 : totK PA10K2 A10K2.u5950 = [0, 0, 663562021630, 2823253837679, 3955425333203, 1686042040517, 211677635039, 5528811039, 0, 0] := by
  rw [show A10K2.u5950 = KTree.node A10K2.t5956 (nat_lit 100981409) (nat_lit 7459055296) (nat_lit 0) A10K2.t5957 from rfl, totK_node, tot5956, tot5957]
  decide +kernel

theorem arows5951 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5951 = true := by
  rw [show A10K2.u5951 = KTree.node A10K2.t5958 (nat_lit 101057430) (nat_lit 13969515421) (nat_lit 0) A10K2.t5959 from rfl, allE_node, rows5958, irow5951, rows5959]
  all_goals rfl

theorem atot5951 : totK PA10K2 A10K2.u5951 = [0, 795232957208, 3018145039579, 3779353959873, 1848647177840, 396256936244, 29010686974, 0, 0, 0] := by
  rw [show A10K2.u5951 = KTree.node A10K2.t5958 (nat_lit 101057430) (nat_lit 13969515421) (nat_lit 0) A10K2.t5959 from rfl, totK_node, tot5958, tot5959]
  decide +kernel

theorem arows5954 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5954 = true := by
  rw [show A10K2.u5954 = KTree.node A10K2.t5960 (nat_lit 101063332) (nat_lit 13601698361) (nat_lit 0) A10K2.t5961 from rfl, allE_node, rows5960, irow5954, rows5961]
  all_goals rfl

theorem atot5954 : totK PA10K2 A10K2.u5954 = [0, 251705348851, 1860124686400, 3927155931369, 2792667374447, 583974769230, 30831673886, 0, 0, 0] := by
  rw [show A10K2.u5954 = KTree.node A10K2.t5960 (nat_lit 101063332) (nat_lit 13601698361) (nat_lit 0) A10K2.t5961 from rfl, totK_node, tot5960, tot5961]
  decide +kernel

theorem arows5955 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5955 = true := by
  rw [show A10K2.u5955 = KTree.node A10K2.t5962 (nat_lit 101074206) (nat_lit 5238655973) (nat_lit 0) A10K2.t5963 from rfl, allE_node, rows5962, irow5955, rows5963]
  all_goals rfl

theorem atot5955 : totK PA10K2 A10K2.u5955 = [0, 741721075374, 2972119599386, 3739000726295, 1638875595174, 220214271323, 6034215561, 0, 0, 0] := by
  rw [show A10K2.u5955 = KTree.node A10K2.t5962 (nat_lit 101074206) (nat_lit 5238655973) (nat_lit 0) A10K2.t5963 from rfl, totK_node, tot5962, tot5963]
  decide +kernel

theorem arows5957 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5957 = true := by
  rw [show A10K2.u5957 = KTree.node A10K2.t5964 (nat_lit 101089536) (nat_lit 15049380543) (nat_lit 0) A10K2.t5965 from rfl, allE_node, rows5964, irow5957, rows5965]
  all_goals rfl

theorem atot5957 : totK PA10K2 A10K2.u5957 = [0, 0, 1100237788635, 3876963124209, 3489763373437, 773138556309, 31987755669, 0, 0, 0] := by
  rw [show A10K2.u5957 = KTree.node A10K2.t5964 (nat_lit 101089536) (nat_lit 15049380543) (nat_lit 0) A10K2.t5965 from rfl, totK_node, tot5964, tot5965]
  decide +kernel

theorem arows5958 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5958 = true := by
  rw [show A10K2.u5958 = KTree.node A10K2.t5966 (nat_lit 101105921) (nat_lit 10329861105) (nat_lit 0) A10K2.t5967 from rfl, allE_node, rows5966, irow5958, rows5967]
  all_goals rfl

theorem atot5958 : totK PA10K2 A10K2.u5958 = [0, 0, 1120382763403, 3789189821953, 3616772962382, 868029733349, 43672754288, 0, 0, 0] := by
  rw [show A10K2.u5958 = KTree.node A10K2.t5966 (nat_lit 101105921) (nat_lit 10329861105) (nat_lit 0) A10K2.t5967 from rfl, totK_node, tot5966, tot5967]
  decide +kernel

theorem arows5962 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5962 = true := by
  rw [show A10K2.u5962 = KTree.node A10K2.t5968 (nat_lit 101112108) (nat_lit 13552313479) (nat_lit 0) A10K2.t5969 from rfl, allE_node, rows5968, irow5962, rows5969]
  all_goals rfl

theorem atot5962 : totK PA10K2 A10K2.u5962 = [0, 455829770507, 1543711200258, 2690103353816, 3055592115317, 1407790006757, 192289909650, 5676195732, 0, 0] := by
  rw [show A10K2.u5962 = KTree.node A10K2.t5968 (nat_lit 101112108) (nat_lit 13552313479) (nat_lit 0) A10K2.t5969 from rfl, totK_node, tot5968, tot5969]
  decide +kernel

theorem arows5963 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5963 = true := by
  rw [show A10K2.u5963 = KTree.node A10K2.t5970 (nat_lit 101126245) (nat_lit 6540504388) (nat_lit 0) A10K2.t5971 from rfl, allE_node, rows5970, irow5963, rows5971]
  all_goals rfl

theorem atot5963 : totK PA10K2 A10K2.u5963 = [0, 351481254165, 2283370512058, 4217357442298, 2462555229020, 436341273152, 25313348169, 0, 0, 0] := by
  rw [show A10K2.u5963 = KTree.node A10K2.t5970 (nat_lit 101126245) (nat_lit 6540504388) (nat_lit 0) A10K2.t5971 from rfl, totK_node, tot5970, tot5971]
  decide +kernel

theorem arows5965 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5965 = true := by
  rw [show A10K2.u5965 = KTree.node A10K2.t5972 (nat_lit 101134264) (nat_lit 13384385497) (nat_lit 0) A10K2.t5973 from rfl, allE_node, rows5972, irow5965, rows5973]
  all_goals rfl

theorem atot5965 : totK PA10K2 A10K2.u5965 = [0, 724612363178, 2925085683638, 4074508726956, 2243103862212, 361294446447, 7151180950, 0, 0, 0] := by
  rw [show A10K2.u5965 = KTree.node A10K2.t5972 (nat_lit 101134264) (nat_lit 13384385497) (nat_lit 0) A10K2.t5973 from rfl, totK_node, tot5972, tot5973]
  decide +kernel

theorem arows5966 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5966 = true := by
  rw [show A10K2.u5966 = KTree.node A10K2.t5974 (nat_lit 101149924) (nat_lit 3421993830) (nat_lit 0) A10K2.t5975 from rfl, allE_node, rows5974, irow5966, rows5975]
  all_goals rfl

theorem atot5966 : totK PA10K2 A10K2.u5966 = [0, 618318149094, 2868747941991, 4219243872522, 2080566220212, 294391099195, 6853348008, 0, 0, 0] := by
  rw [show A10K2.u5966 = KTree.node A10K2.t5974 (nat_lit 101149924) (nat_lit 3421993830) (nat_lit 0) A10K2.t5975 from rfl, totK_node, tot5974, tot5975]
  decide +kernel

theorem arows5969 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5969 = true := by
  rw [show A10K2.u5969 = KTree.node A10K2.t5976 (nat_lit 101154546) (nat_lit 14166633567) (nat_lit 0) A10K2.t5977 from rfl, allE_node, rows5976, irow5969, rows5977]
  all_goals rfl

theorem atot5969 : totK PA10K2 A10K2.u5969 = [526709715043, 1643666875020, 2096850002943, 2483548520384, 2342679236762, 759063450387, 55515214941, 0, 0, 0] := by
  rw [show A10K2.u5969 = KTree.node A10K2.t5976 (nat_lit 101154546) (nat_lit 14166633567) (nat_lit 0) A10K2.t5977 from rfl, totK_node, tot5976, tot5977]
  decide +kernel

theorem arows5970 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5970 = true := by
  rw [show A10K2.u5970 = KTree.node A10K2.t5978 (nat_lit 101716228) (nat_lit 12824621696) (nat_lit 0) A10K2.t5979 from rfl, allE_node, rows5978, irow5970, rows5979]
  all_goals rfl

theorem atot5970 : totK PA10K2 A10K2.u5970 = [312694146422, 2045532259443, 3942325915174, 2662915506120, 545823161246, 30831673886, 0, 0, 0, 0] := by
  rw [show A10K2.u5970 = KTree.node A10K2.t5978 (nat_lit 101716228) (nat_lit 12824621696) (nat_lit 0) A10K2.t5979 from rfl, totK_node, tot5978, tot5979]
  decide +kernel

theorem arows5972 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5972 = true := by
  rw [show A10K2.u5972 = KTree.node A10K2.t5980 (nat_lit 101729581) (nat_lit 6613700219) (nat_lit 0) A10K2.t5981 from rfl, allE_node, rows5980, irow5972, rows5981]
  all_goals rfl

theorem atot5972 : totK PA10K2 A10K2.u5972 = [749928254756, 3132379009116, 4020637354887, 1525502121990, 131625909965, 0, 0, 0, 0, 0] := by
  rw [show A10K2.u5972 = KTree.node A10K2.t5980 (nat_lit 101729581) (nat_lit 6613700219) (nat_lit 0) A10K2.t5981 from rfl, totK_node, tot5980, tot5981]
  decide +kernel

theorem arows5973 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5973 = true := by
  rw [show A10K2.u5973 = KTree.node A10K2.t5982 (nat_lit 101736768) (nat_lit 14899540939) (nat_lit 0) A10K2.t5983 from rfl, allE_node, rows5982, irow5973, rows5983]
  all_goals rfl

theorem atot5973 : totK PA10K2 A10K2.u5973 = [593149538699, 2713980446493, 4112193729725, 2116975065074, 287802438388, 6354482628, 0, 0, 0, 0] := by
  rw [show A10K2.u5973 = KTree.node A10K2.t5982 (nat_lit 101736768) (nat_lit 14899540939) (nat_lit 0) A10K2.t5983 from rfl, totK_node, tot5982, tot5983]
  decide +kernel

theorem arows5978 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5978 = true := by
  rw [show A10K2.u5978 = KTree.node A10K2.t5984 (nat_lit 101744241) (nat_lit 7625527066) (nat_lit 0) A10K2.t5985 from rfl, allE_node, rows5984, irow5978, rows5985]
  all_goals rfl

theorem atot5978 : totK PA10K2 A10K2.u5978 = [0, 1067516183116, 3751981990915, 3909885102072, 1167999746198, 81572176924, 0, 0, 0, 0] := by
  rw [show A10K2.u5978 = KTree.node A10K2.t5984 (nat_lit 101744241) (nat_lit 7625527066) (nat_lit 0) A10K2.t5985 from rfl, totK_node, tot5984, tot5985]
  decide +kernel

theorem arows5979 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5979 = true := by
  rw [show A10K2.u5979 = KTree.node A10K2.t5986 (nat_lit 101748842) (nat_lit 4174965044) (nat_lit 0) A10K2.t5987 from rfl, allE_node, rows5986, irow5979, rows5987]
  all_goals rfl

theorem atot5979 : totK PA10K2 A10K2.u5979 = [0, 360002622783, 2140713541335, 3875363294460, 2434908627987, 523065398562, 30650496230, 0, 0, 0] := by
  rw [show A10K2.u5979 = KTree.node A10K2.t5986 (nat_lit 101748842) (nat_lit 4174965044) (nat_lit 0) A10K2.t5987 from rfl, totK_node, tot5986, tot5987]
  decide +kernel

theorem arows5981 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5981 = true := by
  rw [show A10K2.u5981 = KTree.node A10K2.t5988 (nat_lit 101762400) (nat_lit 10846661124) (nat_lit 0) A10K2.t5989 from rfl, allE_node, rows5988, irow5981, rows5989]
  all_goals rfl

theorem atot5981 : totK PA10K2 A10K2.u5981 = [0, 748389098402, 3207942720974, 4073806263358, 1399994179771, 96772787717, 0, 0, 0, 0] := by
  rw [show A10K2.u5981 = KTree.node A10K2.t5988 (nat_lit 101762400) (nat_lit 10846661124) (nat_lit 0) A10K2.t5989 from rfl, totK_node, tot5988, tot5989]
  decide +kernel

theorem arows5982 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5982 = true := by
  rw [show A10K2.u5982 = KTree.node A10K2.t5990 (nat_lit 101769728) (nat_lit 15675239011) (nat_lit 0) A10K2.t5991 from rfl, allE_node, rows5990, irow5982, rows5991]
  all_goals rfl

theorem atot5982 : totK PA10K2 A10K2.u5982 = [152930188526, 944604090543, 2813252788748, 3822228707806, 1820553022652, 236737135223, 5546304973, 0, 0, 0] := by
  rw [show A10K2.u5982 = KTree.node A10K2.t5990 (nat_lit 101769728) (nat_lit 15675239011) (nat_lit 0) A10K2.t5991 from rfl, totK_node, tot5990, tot5991]
  decide +kernel

theorem arows5985 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5985 = true := by
  rw [show A10K2.u5985 = KTree.node A10K2.t5992 (nat_lit 101846020) (nat_lit 10625901368) (nat_lit 0) A10K2.t5993 from rfl, allE_node, rows5992, irow5985, rows5993]
  all_goals rfl

theorem atot5985 : totK PA10K2 A10K2.u5985 = [611245139011, 2724244379557, 3872883814686, 1993633264949, 394431186185, 25371180993, 0, 0, 0, 0] := by
  rw [show A10K2.u5985 = KTree.node A10K2.t5992 (nat_lit 101846020) (nat_lit 10625901368) (nat_lit 0) A10K2.t5993 from rfl, totK_node, tot5992, tot5993]
  decide +kernel

theorem arows5986 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5986 = true := by
  rw [show A10K2.u5986 = KTree.node A10K2.t5994 (nat_lit 101852636) (nat_lit 5560832097) (nat_lit 0) A10K2.t5995 from rfl, allE_node, rows5994, irow5986, rows5995]
  all_goals rfl

theorem atot5986 : totK PA10K2 A10K2.u5986 = [562867763590, 2724172740600, 4079532166336, 2016674955129, 273522132120, 5460492893, 0, 0, 0, 0] := by
  rw [show A10K2.u5986 = KTree.node A10K2.t5994 (nat_lit 101852636) (nat_lit 5560832097) (nat_lit 0) A10K2.t5995 from rfl, totK_node, tot5994, tot5995]
  decide +kernel

theorem arows5988 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5988 = true := by
  rw [show A10K2.u5988 = KTree.node A10K2.t5996 (nat_lit 101859429) (nat_lit 7000149661) (nat_lit 0) A10K2.t5997 from rfl, allE_node, rows5996, irow5988, rows5997]
  all_goals rfl

theorem atot5988 : totK PA10K2 A10K2.u5988 = [552899335879, 2248889972474, 3629398855706, 2479431458871, 553572771818, 31768748853, 0, 0, 0, 0] := by
  rw [show A10K2.u5988 = KTree.node A10K2.t5996 (nat_lit 101859429) (nat_lit 7000149661) (nat_lit 0) A10K2.t5997 from rfl, totK_node, tot5996, tot5997]
  decide +kernel

theorem arows5989 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5989 = true := by
  rw [show A10K2.u5989 = KTree.node A10K2.t5998 (nat_lit 101864722) (nat_lit 14993366649) (nat_lit 0) A10K2.t5999 from rfl, allE_node, rows5998, irow5989, rows5999]
  all_goals rfl

theorem atot5989 : totK PA10K2 A10K2.u5989 = [267608287982, 2184596791688, 4267456846059, 2397983309898, 316153253513, 6354482628, 0, 0, 0, 0] := by
  rw [show A10K2.u5989 = KTree.node A10K2.t5998 (nat_lit 101864722) (nat_lit 14993366649) (nat_lit 0) A10K2.t5999 from rfl, totK_node, tot5998, tot5999]
  decide +kernel

end QECKChecks.A10K2
