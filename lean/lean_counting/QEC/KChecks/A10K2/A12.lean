import QEC.Count.ChunksK3
import QEC.KChecks.A10K2.A11

namespace QECKChecks.A10K2

open QEC QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem arows525 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u525 = true := by
  rw [show A10K2.u525 = KTree.node A10K2.u517 (nat_lit 9341489) (nat_lit 9734270331) (nat_lit 0) A10K2.u524 from rfl, allE_node, arows517, irow525, arows524]
  all_goals rfl

theorem atot525 : totK PA10K2 A10K2.u525 = [1257633742337, 7003731943471, 18468972194164, 26583959271225, 18060769983871, 4275481787972, 339924805981, 6239673734, 0, 0] := by
  rw [show A10K2.u525 = KTree.node A10K2.u517 (nat_lit 9341489) (nat_lit 9734270331) (nat_lit 0) A10K2.u524 from rfl, totK_node, atot517, atot524]
  decide +kernel

theorem arows540 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u540 = true := by
  rw [show A10K2.u540 = KTree.node A10K2.u532 (nat_lit 9488570) (nat_lit 12721037767) (nat_lit 0) A10K2.u539 from rfl, allE_node, arows532, irow540, arows539]
  all_goals rfl

theorem atot540 : totK PA10K2 A10K2.u540 = [2491811631599, 14092809328416, 28167842600120, 23617883331638, 7858170249643, 969698190008, 36196801203, 0, 0, 0] := by
  rw [show A10K2.u540 = KTree.node A10K2.u532 (nat_lit 9488570) (nat_lit 12721037767) (nat_lit 0) A10K2.u539 from rfl, totK_node, atot532, atot539]
  decide +kernel

theorem arows556 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u556 = true := by
  rw [show A10K2.u556 = KTree.node A10K2.u548 (nat_lit 9571142) (nat_lit 8331486008) (nat_lit 0) A10K2.u555 from rfl, allE_node, arows548, irow556, arows555]
  all_goals rfl

theorem atot556 : totK PA10K2 A10K2.u556 = [2453432600795, 13846494101229, 27657332690505, 23207624317822, 7901811775284, 982975417126, 37204059898, 0, 0, 0] := by
  rw [show A10K2.u556 = KTree.node A10K2.u548 (nat_lit 9571142) (nat_lit 8331486008) (nat_lit 0) A10K2.u555 from rfl, totK_node, atot548, atot555]
  decide +kernel

theorem arows571 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u571 = true := by
  rw [show A10K2.u571 = KTree.node A10K2.u563 (nat_lit 9715748) (nat_lit 13324647755) (nat_lit 0) A10K2.u570 from rfl, allE_node, arows563, irow571, arows570]
  all_goals rfl

theorem atot571 : totK PA10K2 A10K2.u571 = [0, 5225602113569, 22559174509296, 31402631219989, 15010426848658, 2276088052126, 81833253981, 0, 0, 0] := by
  rw [show A10K2.u571 = KTree.node A10K2.u563 (nat_lit 9715748) (nat_lit 13324647755) (nat_lit 0) A10K2.u570 from rfl, totK_node, atot563, atot570]
  decide +kernel

theorem arows588 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u588 = true := by
  rw [show A10K2.u588 = KTree.node A10K2.u580 (nat_lit 9845078) (nat_lit 9111017001) (nat_lit 0) A10K2.u587 from rfl, allE_node, arows580, irow588, arows587]
  all_goals rfl

theorem atot588 : totK PA10K2 A10K2.u588 = [0, 2856022969965, 16256661544018, 30664446010789, 20621770694987, 4286546303506, 252088397880, 0, 0, 0] := by
  rw [show A10K2.u588 = KTree.node A10K2.u580 (nat_lit 9845078) (nat_lit 9111017001) (nat_lit 0) A10K2.u587 from rfl, totK_node, atot580, atot587]
  decide +kernel

theorem arows603 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u603 = true := by
  rw [show A10K2.u603 = KTree.node A10K2.u595 (nat_lit 10514993) (nat_lit 9935575717) (nat_lit 0) A10K2.u602 from rfl, allE_node, arows595, irow603, arows602]
  all_goals rfl

theorem atot603 : totK PA10K2 A10K2.u603 = [0, 2597608154335, 13688127922989, 27182355379767, 24148036751187, 8580548137559, 1146329850361, 42551283831, 0, 0] := by
  rw [show A10K2.u603 = KTree.node A10K2.u595 (nat_lit 10514993) (nat_lit 9935575717) (nat_lit 0) A10K2.u602 from rfl, totK_node, atot595, atot602]
  decide +kernel

theorem arows619 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u619 = true := by
  rw [show A10K2.u619 = KTree.node A10K2.u611 (nat_lit 10650452) (nat_lit 11949799862) (nat_lit 0) A10K2.u618 from rfl, allE_node, arows611, irow619, arows618]
  all_goals rfl

theorem atot619 : totK PA10K2 A10K2.u619 = [0, 2906175344308, 15799865312241, 29684322320461, 21862850738254, 5586017225041, 486190437991, 6354482628, 0, 0] := by
  rw [show A10K2.u619 = KTree.node A10K2.u611 (nat_lit 10650452) (nat_lit 11949799862) (nat_lit 0) A10K2.u618 from rfl, totK_node, atot611, atot618]
  decide +kernel

theorem arows634 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u634 = true := by
  rw [show A10K2.u634 = KTree.node A10K2.u626 (nat_lit 11086624) (nat_lit 11033158024) (nat_lit 0) A10K2.u633 from rfl, allE_node, arows626, irow634, arows633]
  all_goals rfl

theorem atot634 : totK PA10K2 A10K2.u634 = [0, 2693615829208, 15195990721936, 30098856196293, 23955014297422, 6796058103092, 561483601149, 6904928264, 0, 0] := by
  rw [show A10K2.u634 = KTree.node A10K2.u626 (nat_lit 11086624) (nat_lit 11033158024) (nat_lit 0) A10K2.u633 from rfl, totK_node, atot626, atot633]
  decide +kernel

theorem arows652 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u652 = true := by
  rw [show A10K2.u652 = KTree.node A10K2.u644 (nat_lit 11150629) (nat_lit 7319544913) (nat_lit 0) A10K2.u651 from rfl, allE_node, arows644, irow652, arows651]
  all_goals rfl

theorem atot652 : totK PA10K2 A10K2.u652 = [0, 2143507266498, 12858003105759, 27517903533525, 24634956306661, 8346238539376, 999733992597, 37204059898, 0, 0] := by
  rw [show A10K2.u652 = KTree.node A10K2.u644 (nat_lit 11150629) (nat_lit 7319544913) (nat_lit 0) A10K2.u651 from rfl, totK_node, atot644, atot651]
  decide +kernel

theorem arows667 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u667 = true := by
  rw [show A10K2.u667 = KTree.node A10K2.u659 (nat_lit 11556972) (nat_lit 11680964347) (nat_lit 0) A10K2.u666 from rfl, allE_node, arows659, irow667, arows666]
  all_goals rfl

theorem atot667 : totK PA10K2 A10K2.u667 = [0, 2091277548036, 12388280323380, 27030428035671, 25028293368804, 8592707637999, 1091666037745, 42121665971, 0, 0] := by
  rw [show A10K2.u667 = KTree.node A10K2.u659 (nat_lit 11556972) (nat_lit 11680964347) (nat_lit 0) A10K2.u666 from rfl, totK_node, atot659, atot666]
  decide +kernel

theorem arows683 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u683 = true := by
  rw [show A10K2.u683 = KTree.node A10K2.u675 (nat_lit 11643424) (nat_lit 11072636368) (nat_lit 0) A10K2.u682 from rfl, allE_node, arows675, irow683, arows682]
  all_goals rfl

theorem atot683 : totK PA10K2 A10K2.u683 = [0, 2836989722907, 14747655001477, 28026485481101, 22822516826580, 7170741671982, 838466147287, 36768997705, 0, 0] := by
  rw [show A10K2.u683 = KTree.node A10K2.u675 (nat_lit 11643424) (nat_lit 11072636368) (nat_lit 0) A10K2.u682 from rfl, totK_node, atot675, atot682]
  decide +kernel

theorem arows698 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u698 = true := by
  rw [show A10K2.u698 = KTree.node A10K2.u690 (nat_lit 11710142) (nat_lit 11842463174) (nat_lit 0) A10K2.u697 from rfl, allE_node, arows690, irow698, arows697]
  all_goals rfl

theorem atot698 : totK PA10K2 A10K2.u698 = [0, 1265119596279, 10176481004958, 26581475283358, 26905745237331, 9182516339807, 1074314772613, 36743231635, 0, 0] := by
  rw [show A10K2.u698 = KTree.node A10K2.u690 (nat_lit 11710142) (nat_lit 11842463174) (nat_lit 0) A10K2.u697 from rfl, totK_node, atot690, atot697]
  decide +kernel

theorem arows715 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u715 = true := by
  rw [show A10K2.u715 = KTree.node A10K2.u707 (nat_lit 11929822) (nat_lit 7436075031) (nat_lit 0) A10K2.u714 from rfl, allE_node, arows707, irow715, arows714]
  all_goals rfl

theorem atot715 : totK PA10K2 A10K2.u715 = [0, 0, 4583248723129, 20895515098787, 31256631528816, 15753443507234, 2648742424501, 135998035210, 0, 0] := by
  rw [show A10K2.u715 = KTree.node A10K2.u707 (nat_lit 11929822) (nat_lit 7436075031) (nat_lit 0) A10K2.u714 from rfl, totK_node, atot707, atot714]
  decide +kernel

theorem arows730 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u730 = true := by
  rw [show A10K2.u730 = KTree.node A10K2.u722 (nat_lit 12599926) (nat_lit 14773165199) (nat_lit 0) A10K2.u729 from rfl, allE_node, arows722, irow730, arows729]
  all_goals rfl

theorem atot730 : totK PA10K2 A10K2.u730 = [2300403117589, 11557928869029, 20813178613408, 17721465242472, 12154104866302, 8588343586755, 2955974567580, 353769333798, 6354482628, 0] := by
  rw [show A10K2.u730 = KTree.node A10K2.u722 (nat_lit 12599926) (nat_lit 14773165199) (nat_lit 0) A10K2.u729 from rfl, totK_node, atot722, atot729]
  decide +kernel

theorem arows746 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u746 = true := by
  rw [show A10K2.u746 = KTree.node A10K2.u738 (nat_lit 12732984) (nat_lit 13026764199) (nat_lit 0) A10K2.u745 from rfl, allE_node, arows738, irow746, arows745]
  all_goals rfl

theorem atot746 : totK PA10K2 A10K2.u746 = [2336205603258, 13748465418156, 28620847632692, 24424359776958, 7546364758989, 731091626773, 11900787601, 0, 0, 0] := by
  rw [show A10K2.u746 = KTree.node A10K2.u738 (nat_lit 12732984) (nat_lit 13026764199) (nat_lit 0) A10K2.u745 from rfl, totK_node, atot738, atot745]
  decide +kernel

theorem arows761 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u761 = true := by
  rw [show A10K2.u761 = KTree.node A10K2.u753 (nat_lit 12819506) (nat_lit 11155233023) (nat_lit 0) A10K2.u760 from rfl, allE_node, arows753, irow761, arows760]
  all_goals rfl

theorem atot761 : totK PA10K2 A10K2.u761 = [1420687879820, 9786779616469, 24848274423849, 27854812301814, 13079689089979, 2143457625669, 95132842637, 0, 0, 0] := by
  rw [show A10K2.u761 = KTree.node A10K2.u753 (nat_lit 12819506) (nat_lit 11155233023) (nat_lit 0) A10K2.u760 from rfl, totK_node, atot753, atot760]
  decide +kernel

theorem arows780 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u780 = true := by
  rw [show A10K2.u780 = KTree.node A10K2.u772 (nat_lit 12882439) (nat_lit 12458630533) (nat_lit 0) A10K2.u779 from rfl, allE_node, arows772, irow780, arows779]
  all_goals rfl

theorem atot780 : totK PA10K2 A10K2.u780 = [0, 2629267405888, 14448385022890, 28564656210115, 23253449706380, 7387048881000, 929630835390, 36134558889, 0, 0] := by
  rw [show A10K2.u780 = KTree.node A10K2.u772 (nat_lit 12882439) (nat_lit 12458630533) (nat_lit 0) A10K2.u779 from rfl, totK_node, atot772, atot779]
  decide +kernel

theorem arows795 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u795 = true := by
  rw [show A10K2.u795 = KTree.node A10K2.u787 (nat_lit 13047885) (nat_lit 5553316117) (nat_lit 0) A10K2.u794 from rfl, allE_node, arows787, irow795, arows794]
  all_goals rfl

theorem atot795 : totK PA10K2 A10K2.u795 = [847358390021, 5992508245556, 18394948080760, 28204454882589, 19424792197113, 4764745166732, 362666505761, 5676195732, 0, 0] := by
  rw [show A10K2.u795 = KTree.node A10K2.u787 (nat_lit 13047885) (nat_lit 5553316117) (nat_lit 0) A10K2.u794 from rfl, totK_node, atot787, atot794]
  decide +kernel

theorem arows811 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u811 = true := by
  rw [show A10K2.u811 = KTree.node A10K2.u803 (nat_lit 13219104) (nat_lit 8351447588) (nat_lit 0) A10K2.u810 from rfl, allE_node, arows803, irow811, arows810]
  all_goals rfl

theorem atot811 : totK PA10K2 A10K2.u811 = [2698145531354, 14235996178496, 27977186396036, 24277296212454, 8595409762467, 1048311936322, 37204059898, 0, 0, 0] := by
  rw [show A10K2.u811 = KTree.node A10K2.u803 (nat_lit 13219104) (nat_lit 8351447588) (nat_lit 0) A10K2.u810 from rfl, totK_node, atot803, atot810]
  decide +kernel

theorem arows826 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u826 = true := by
  rw [show A10K2.u826 = KTree.node A10K2.u818 (nat_lit 13347109) (nat_lit 7443314834) (nat_lit 0) A10K2.u825 from rfl, allE_node, arows818, irow826, arows825]
  all_goals rfl

theorem atot826 : totK PA10K2 A10K2.u826 = [912224543933, 8444804451649, 24465065722736, 29154118096091, 14148292063775, 2293134381088, 100796613114, 0, 0, 0] := by
  rw [show A10K2.u826 = KTree.node A10K2.u818 (nat_lit 13347109) (nat_lit 7443314834) (nat_lit 0) A10K2.u825 from rfl, totK_node, atot818, atot825]
  decide +kernel

theorem arows843 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u843 = true := by
  rw [show A10K2.u843 = KTree.node A10K2.u835 (nat_lit 13482656) (nat_lit 6467774366) (nat_lit 0) A10K2.u842 from rfl, allE_node, arows835, irow843, arows842]
  all_goals rfl

theorem atot843 : totK PA10K2 A10K2.u843 = [0, 2741464143490, 14954196242558, 28914180109234, 23411883978503, 7629249243794, 945819041108, 36704093874, 0, 0] := by
  rw [show A10K2.u843 = KTree.node A10K2.u835 (nat_lit 13482656) (nat_lit 6467774366) (nat_lit 0) A10K2.u842 from rfl, totK_node, atot835, atot842]
  decide +kernel

theorem arows858 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u858 = true := by
  rw [show A10K2.u858 = KTree.node A10K2.u850 (nat_lit 14176310) (nat_lit 15070140919) (nat_lit 0) A10K2.u857 from rfl, allE_node, arows850, irow858, arows857]
  all_goals rfl

theorem atot858 : totK PA10K2 A10K2.u858 = [2127308439256, 12064227984455, 25773928807836, 25313930937723, 11285699145276, 1973285023839, 98657373207, 0, 0, 0] := by
  rw [show A10K2.u858 = KTree.node A10K2.u850 (nat_lit 14176310) (nat_lit 15070140919) (nat_lit 0) A10K2.u857 from rfl, totK_node, atot850, atot857]
  decide +kernel

theorem arows874 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u874 = true := by
  rw [show A10K2.u874 = KTree.node A10K2.u866 (nat_lit 14251233) (nat_lit 2631780396) (nat_lit 0) A10K2.u873 from rfl, allE_node, arows866, irow874, arows873]
  all_goals rfl

theorem atot874 : totK PA10K2 A10K2.u874 = [2642420914979, 14273478960606, 28337463376600, 24695260766932, 8654505746972, 1047391068884, 36629191582, 0, 0, 0] := by
  rw [show A10K2.u874 = KTree.node A10K2.u866 (nat_lit 14251233) (nat_lit 2631780396) (nat_lit 0) A10K2.u873 from rfl, totK_node, atot866, atot873]
  decide +kernel

theorem arows889 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u889 = true := by
  rw [show A10K2.u889 = KTree.node A10K2.u881 (nat_lit 14385932) (nat_lit 11105070655) (nat_lit 0) A10K2.u888 from rfl, allE_node, arows881, irow889, arows888]
  all_goals rfl

theorem atot889 : totK PA10K2 A10K2.u889 = [1622710366237, 10734192865668, 25877506561509, 27081692176923, 11650291088814, 1601098376433, 37751669437, 0, 0, 0] := by
  rw [show A10K2.u889 = KTree.node A10K2.u881 (nat_lit 14385932) (nat_lit 11105070655) (nat_lit 0) A10K2.u888 from rfl, totK_node, atot881, atot888]
  decide +kernel

theorem arows907 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u907 = true := by
  rw [show A10K2.u907 = KTree.node A10K2.u899 (nat_lit 14450628) (nat_lit 5160861025) (nat_lit 0) A10K2.u906 from rfl, allE_node, arows899, irow907, arows906]
  all_goals rfl

theorem atot907 : totK PA10K2 A10K2.u907 = [0, 2905944438674, 15606512584554, 29772192893506, 23222855736202, 6578806696365, 576079392788, 7007974415, 0, 0] := by
  rw [show A10K2.u907 = KTree.node A10K2.u899 (nat_lit 14450628) (nat_lit 5160861025) (nat_lit 0) A10K2.u906 from rfl, totK_node, atot899, atot906]
  decide +kernel

theorem arows922 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u922 = true := by
  rw [show A10K2.u922 = KTree.node A10K2.u914 (nat_lit 14542740) (nat_lit 8559971102) (nat_lit 0) A10K2.u921 from rfl, allE_node, arows914, irow922, arows921]
  all_goals rfl

theorem atot922 : totK PA10K2 A10K2.u922 = [0, 3479510292143, 17339118314413, 30371325611790, 21873530149926, 5885040412930, 491192302753, 7151180950, 0, 0] := by
  rw [show A10K2.u922 = KTree.node A10K2.u914 (nat_lit 14542740) (nat_lit 8559971102) (nat_lit 0) A10K2.u921 from rfl, totK_node, atot914, atot921]
  decide +kernel

theorem arows938 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u938 = true := by
  rw [show A10K2.u938 = KTree.node A10K2.u930 (nat_lit 14675512) (nat_lit 14596423998) (nat_lit 0) A10K2.u937 from rfl, allE_node, arows930, irow938, arows937]
  all_goals rfl

theorem atot938 : totK PA10K2 A10K2.u938 = [0, 1942436274614, 11549428912083, 25951185586397, 25945761699929, 10988403270949, 1656960971349, 73776485728, 0, 0] := by
  rw [show A10K2.u938 = KTree.node A10K2.u930 (nat_lit 14675512) (nat_lit 14596423998) (nat_lit 0) A10K2.u937 from rfl, totK_node, atot930, atot937]
  decide +kernel

theorem arows953 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u953 = true := by
  rw [show A10K2.u953 = KTree.node A10K2.u945 (nat_lit 14737911) (nat_lit 14886314268) (nat_lit 0) A10K2.u952 from rfl, allE_node, arows945, irow953, arows952]
  all_goals rfl

theorem atot953 : totK PA10K2 A10K2.u953 = [0, 1892822707356, 12543025090770, 28175450387859, 25438750728343, 8543182441002, 1018329804996, 36196801203, 0, 0] := by
  rw [show A10K2.u953 = KTree.node A10K2.u945 (nat_lit 14737911) (nat_lit 14886314268) (nat_lit 0) A10K2.u952 from rfl, totK_node, atot945, atot952]
  decide +kernel

theorem arows970 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u970 = true := by
  rw [show A10K2.u970 = KTree.node A10K2.u962 (nat_lit 14902195) (nat_lit 8011808225) (nat_lit 0) A10K2.u969 from rfl, allE_node, arows962, irow970, arows969]
  all_goals rfl

theorem atot970 : totK PA10K2 A10K2.u970 = [0, 2222037618697, 12756426693878, 27515842034411, 25861806978038, 9391644886934, 1009562536124, 19647705476, 0, 0] := by
  rw [show A10K2.u970 = KTree.node A10K2.u962 (nat_lit 14902195) (nat_lit 8011808225) (nat_lit 0) A10K2.u969 from rfl, totK_node, atot962, atot969]
  decide +kernel

theorem arows985 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u985 = true := by
  rw [show A10K2.u985 = KTree.node A10K2.u977 (nat_lit 14964949) (nat_lit 6365199804) (nat_lit 0) A10K2.u984 from rfl, allE_node, arows977, irow985, arows984]
  all_goals rfl

theorem atot985 : totK PA10K2 A10K2.u985 = [0, 0, 2875697845281, 15941061517460, 30215710939420, 22228478109492, 5709430697141, 497705224788, 7237400819, 0] := by
  rw [show A10K2.u985 = KTree.node A10K2.u977 (nat_lit 14964949) (nat_lit 6365199804) (nat_lit 0) A10K2.u984 from rfl, totK_node, atot977, atot984]
  decide +kernel

theorem arows1001 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1001 = true := by
  rw [show A10K2.u1001 = KTree.node A10K2.u993 (nat_lit 15146167) (nat_lit 14879290484) (nat_lit 0) A10K2.u1000 from rfl, allE_node, arows993, irow1001, arows1000]
  all_goals rfl

theorem atot1001 : totK PA10K2 A10K2.u1001 = [0, 847358390021, 7252994519604, 22288513163036, 29702656726744, 15486321199831, 2645958795941, 122527677467, 0, 0] := by
  rw [show A10K2.u1001 = KTree.node A10K2.u993 (nat_lit 15146167) (nat_lit 14879290484) (nat_lit 0) A10K2.u1000 from rfl, totK_node, atot993, atot1000]
  decide +kernel

theorem arows1016 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1016 = true := by
  rw [show A10K2.u1016 = KTree.node A10K2.u1008 (nat_lit 15316741) (nat_lit 6285252457) (nat_lit 0) A10K2.u1015 from rfl, allE_node, arows1008, irow1016, arows1015]
  all_goals rfl

theorem atot1016 : totK PA10K2 A10K2.u1016 = [0, 2743423024714, 14672833696729, 28488397336331, 23753069538618, 8125283233066, 994107954252, 36968589557, 0, 0] := by
  rw [show A10K2.u1016 = KTree.node A10K2.u1008 (nat_lit 15316741) (nat_lit 6285252457) (nat_lit 0) A10K2.u1015 from rfl, totK_node, atot1008, atot1015]
  decide +kernel

theorem arows1037 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1037 = true := by
  rw [show A10K2.u1037 = KTree.node A10K2.u1029 (nat_lit 15445384) (nat_lit 12763704532) (nat_lit 0) A10K2.u1036 from rfl, allE_node, arows1029, irow1037, arows1036]
  all_goals rfl

theorem atot1037 : totK PA10K2 A10K2.u1037 = [0, 866947050573, 7927579624675, 23811007583056, 29500463724764, 14622472218650, 2352421569076, 106333121441, 0, 0] := by
  rw [show A10K2.u1037 = KTree.node A10K2.u1029 (nat_lit 15445384) (nat_lit 12763704532) (nat_lit 0) A10K2.u1036 from rfl, totK_node, atot1029, atot1036]
  decide +kernel

theorem arows1052 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1052 = true := by
  rw [show A10K2.u1052 = KTree.node A10K2.u1044 (nat_lit 15582867) (nat_lit 10953714944) (nat_lit 0) A10K2.u1051 from rfl, allE_node, arows1044, irow1052, arows1051]
  all_goals rfl

theorem atot1052 : totK PA10K2 A10K2.u1052 = [0, 0, 3420442031856, 17241984985152, 30567240801034, 21743895408232, 5484772479186, 458693572530, 7380853412, 0] := by
  rw [show A10K2.u1052 = KTree.node A10K2.u1044 (nat_lit 15582867) (nat_lit 10953714944) (nat_lit 0) A10K2.u1051 from rfl, totK_node, atot1044, atot1051]
  decide +kernel

theorem arows1068 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1068 = true := by
  rw [show A10K2.u1068 = KTree.node A10K2.u1060 (nat_lit 16281019) (nat_lit 6855533660) (nat_lit 0) A10K2.u1067 from rfl, allE_node, arows1060, irow1068, arows1067]
  all_goals rfl

theorem atot1068 : totK PA10K2 A10K2.u1068 = [0, 2204373509922, 12294748885777, 26257557794117, 25429210476058, 10780900629322, 1704343408539, 74859284461, 0, 0] := by
  rw [show A10K2.u1068 = KTree.node A10K2.u1060 (nat_lit 16281019) (nat_lit 6855533660) (nat_lit 0) A10K2.u1067 from rfl, totK_node, atot1060, atot1067]
  decide +kernel

theorem arows1083 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1083 = true := by
  rw [show A10K2.u1083 = KTree.node A10K2.u1075 (nat_lit 16362608) (nat_lit 12900754573) (nat_lit 0) A10K2.u1082 from rfl, allE_node, arows1075, irow1083, arows1082]
  all_goals rfl

theorem atot1083 : totK PA10K2 A10K2.u1083 = [0, 3143685415562, 15982238467228, 29178254418908, 22854417744082, 7199675868564, 719225400569, 12696458652, 0, 0] := by
  rw [show A10K2.u1083 = KTree.node A10K2.u1075 (nat_lit 16362608) (nat_lit 12900754573) (nat_lit 0) A10K2.u1082 from rfl, totK_node, atot1075, atot1082]
  decide +kernel

theorem arows1100 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1100 = true := by
  rw [show A10K2.u1100 = KTree.node A10K2.u1092 (nat_lit 16491761) (nat_lit 4836326203) (nat_lit 0) A10K2.u1099 from rfl, allE_node, arows1092, irow1100, arows1099]
  all_goals rfl

theorem atot1100 : totK PA10K2 A10K2.u1100 = [0, 1029302401414, 8906606296162, 24903503711488, 28640773832408, 13139142736934, 2011555918397, 87539204642, 0, 0] := by
  rw [show A10K2.u1100 = KTree.node A10K2.u1092 (nat_lit 16491761) (nat_lit 4836326203) (nat_lit 0) A10K2.u1099 from rfl, totK_node, atot1092, atot1099]
  decide +kernel

theorem arows1115 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1115 = true := by
  rw [show A10K2.u1115 = KTree.node A10K2.u1107 (nat_lit 16564551) (nat_lit 5853222694) (nat_lit 0) A10K2.u1114 from rfl, allE_node, arows1107, irow1115, arows1114]
  all_goals rfl

theorem atot1115 : totK PA10K2 A10K2.u1115 = [0, 0, 3176933896267, 16790202578343, 30973233102197, 22408518432755, 5422804770287, 393297750636, 6725424603, 0] := by
  rw [show A10K2.u1115 = KTree.node A10K2.u1107 (nat_lit 16564551) (nat_lit 5853222694) (nat_lit 0) A10K2.u1114 from rfl, totK_node, atot1107, atot1114]
  decide +kernel

theorem arows1131 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1131 = true := by
  rw [show A10K2.u1131 = KTree.node A10K2.u1123 (nat_lit 16719317) (nat_lit 1681352385) (nat_lit 0) A10K2.u1130 from rfl, allE_node, arows1123, irow1131, arows1130]
  all_goals rfl

theorem atot1131 : totK PA10K2 A10K2.u1131 = [0, 0, 2379134725954, 14108769127739, 29463193132157, 25138538737339, 7177359439198, 552679782315, 6860445330, 0] := by
  rw [show A10K2.u1131 = KTree.node A10K2.u1123 (nat_lit 16719317) (nat_lit 1681352385) (nat_lit 0) A10K2.u1130 from rfl, totK_node, atot1123, atot1130]
  decide +kernel

theorem arows1146 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1146 = true := by
  rw [show A10K2.u1146 = KTree.node A10K2.u1138 (nat_lit 16780919) (nat_lit 14459905030) (nat_lit 0) A10K2.u1145 from rfl, allE_node, arows1138, irow1146, arows1145]
  all_goals rfl

theorem atot1146 : totK PA10K2 A10K2.u1146 = [0, 2380035396479, 11494761764007, 20354537037826, 19357829716472, 15084637763377, 7687191774795, 1456237671250, 73776485728, 0] := by
  rw [show A10K2.u1146 = KTree.node A10K2.u1138 (nat_lit 16780919) (nat_lit 14459905030) (nat_lit 0) A10K2.u1145 from rfl, totK_node, atot1138, atot1145]
  decide +kernel

theorem arows1164 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1164 = true := by
  rw [show A10K2.u1164 = KTree.node A10K2.u1156 (nat_lit 16912457) (nat_lit 9594707706) (nat_lit 0) A10K2.u1163 from rfl, allE_node, arows1156, irow1164, arows1163]
  all_goals rfl

theorem atot1164 : totK PA10K2 A10K2.u1164 = [0, 2000559346920, 12464773746508, 27412647680753, 24747558865288, 8195199597452, 953752902494, 36196801203, 0, 0] := by
  rw [show A10K2.u1164 = KTree.node A10K2.u1156 (nat_lit 16912457) (nat_lit 9594707706) (nat_lit 0) A10K2.u1163 from rfl, totK_node, atot1156, atot1163]
  decide +kernel

theorem arows1179 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1179 = true := by
  rw [show A10K2.u1179 = KTree.node A10K2.u1171 (nat_lit 17000087) (nat_lit 13435479642) (nat_lit 0) A10K2.u1178 from rfl, allE_node, arows1171, irow1179, arows1178]
  all_goals rfl

theorem atot1179 : totK PA10K2 A10K2.u1179 = [0, 2128375855690, 12630188446966, 27660781892840, 26106588597348, 9261802053687, 930370960052, 13259410892, 0, 0] := by
  rw [show A10K2.u1179 = KTree.node A10K2.u1171 (nat_lit 17000087) (nat_lit 13435479642) (nat_lit 0) A10K2.u1178 from rfl, totK_node, atot1171, atot1178]
  decide +kernel

theorem arows1195 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1195 = true := by
  rw [show A10K2.u1195 = KTree.node A10K2.u1187 (nat_lit 17064321) (nat_lit 10320576489) (nat_lit 0) A10K2.u1194 from rfl, allE_node, arows1187, irow1195, arows1194]
  all_goals rfl

theorem atot1195 : totK PA10K2 A10K2.u1195 = [0, 0, 2541383653090, 14269379772206, 28384070395498, 23139745403749, 7201144282510, 828723369615, 30605747850, 0] := by
  rw [show A10K2.u1195 = KTree.node A10K2.u1187 (nat_lit 17064321) (nat_lit 10320576489) (nat_lit 0) A10K2.u1194 from rfl, totK_node, atot1187, atot1194]
  decide +kernel

theorem arows1210 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1210 = true := by
  rw [show A10K2.u1210 = KTree.node A10K2.u1202 (nat_lit 17193058) (nat_lit 9022449742) (nat_lit 0) A10K2.u1209 from rfl, allE_node, arows1202, irow1210, arows1209]
  all_goals rfl

theorem atot1210 : totK PA10K2 A10K2.u1210 = [0, 0, 2998872829978, 16201372962178, 30001460685966, 21012269498352, 5008437665165, 473730044632, 11205006771, 0] := by
  rw [show A10K2.u1210 = KTree.node A10K2.u1202 (nat_lit 17193058) (nat_lit 9022449742) (nat_lit 0) A10K2.u1209 from rfl, totK_node, atot1202, atot1209]
  decide +kernel

theorem arows1227 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1227 = true := by
  rw [show A10K2.u1227 = KTree.node A10K2.u1219 (nat_lit 17842517) (nat_lit 6864452057) (nat_lit 0) A10K2.u1226 from rfl, allE_node, arows1219, irow1227, arows1226]
  all_goals rfl

theorem atot1227 : totK PA10K2 A10K2.u1227 = [0, 2191473725670, 12349677989638, 25964563038348, 24904246559881, 10827764139019, 1803842143824, 78921248964, 0, 0] := by
  rw [show A10K2.u1227 = KTree.node A10K2.u1219 (nat_lit 17842517) (nat_lit 6864452057) (nat_lit 0) A10K2.u1226 from rfl, totK_node, atot1219, atot1226]
  decide +kernel

theorem arows1242 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1242 = true := by
  rw [show A10K2.u1242 = KTree.node A10K2.u1234 (nat_lit 17933553) (nat_lit 2058534364) (nat_lit 0) A10K2.u1241 from rfl, allE_node, arows1234, irow1242, arows1241]
  all_goals rfl

theorem atot1242 : totK PA10K2 A10K2.u1242 = [0, 2653116388797, 14457602981542, 28394643473379, 23106529262529, 6920777151990, 639322284973, 11667478262, 0, 0] := by
  rw [show A10K2.u1242 = KTree.node A10K2.u1234 (nat_lit 17933553) (nat_lit 2058534364) (nat_lit 0) A10K2.u1241 from rfl, totK_node, atot1234, atot1241]
  decide +kernel

theorem arows1258 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1258 = true := by
  rw [show A10K2.u1258 = KTree.node A10K2.u1250 (nat_lit 18011364) (nat_lit 13288066281) (nat_lit 0) A10K2.u1257 from rfl, allE_node, arows1250, irow1258, arows1257]
  all_goals rfl

theorem atot1258 : totK PA10K2 A10K2.u1258 = [0, 821967029087, 8426419168924, 25063732445939, 28429185902803, 11453330067945, 1496061444437, 50380680131, 0, 0] := by
  rw [show A10K2.u1258 = KTree.node A10K2.u1250 (nat_lit 18011364) (nat_lit 13288066281) (nat_lit 0) A10K2.u1257 from rfl, totK_node, atot1250, atot1257]
  decide +kernel

theorem arows1273 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1273 = true := by
  rw [show A10K2.u1273 = KTree.node A10K2.u1265 (nat_lit 18228978) (nat_lit 14867522649) (nat_lit 0) A10K2.u1272 from rfl, allE_node, arows1265, irow1273, arows1272]
  all_goals rfl

theorem atot1273 : totK PA10K2 A10K2.u1273 = [0, 0, 3469846824901, 18479097534502, 31865157572589, 18151305220405, 2966844844532, 122643151078, 0, 0] := by
  rw [show A10K2.u1273 = KTree.node A10K2.u1265 (nat_lit 18228978) (nat_lit 14867522649) (nat_lit 0) A10K2.u1272 from rfl, totK_node, atot1265, atot1272]
  decide +kernel

theorem arows1292 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1292 = true := by
  rw [show A10K2.u1292 = KTree.node A10K2.u1284 (nat_lit 18379200) (nat_lit 15203328423) (nat_lit 0) A10K2.u1291 from rfl, allE_node, arows1284, irow1292, arows1291]
  all_goals rfl

theorem atot1292 : totK PA10K2 A10K2.u1292 = [0, 2403607604811, 12969855883539, 25964357866735, 23597046572092, 10114307348499, 2306175732867, 231578808238, 6354482628, 0] := by
  rw [show A10K2.u1292 = KTree.node A10K2.u1284 (nat_lit 18379200) (nat_lit 15203328423) (nat_lit 0) A10K2.u1291 from rfl, totK_node, atot1284, atot1291]
  decide +kernel

theorem arows1307 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1307 = true := by
  rw [show A10K2.u1307 = KTree.node A10K2.u1299 (nat_lit 18476179) (nat_lit 10761484445) (nat_lit 0) A10K2.u1306 from rfl, allE_node, arows1299, irow1307, arows1306]
  all_goals rfl

theorem atot1307 : totK PA10K2 A10K2.u1307 = [0, 3482269234406, 17537983251818, 30996683254822, 22317689898482, 5975937244113, 502347066845, 8047840951, 0, 0] := by
  rw [show A10K2.u1307 = KTree.node A10K2.u1299 (nat_lit 18476179) (nat_lit 10761484445) (nat_lit 0) A10K2.u1306 from rfl, totK_node, atot1299, atot1306]
  decide +kernel

theorem arows1323 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1323 = true := by
  rw [show A10K2.u1323 = KTree.node A10K2.u1315 (nat_lit 18608594) (nat_lit 13655768253) (nat_lit 0) A10K2.u1322 from rfl, allE_node, arows1315, irow1323, arows1322]
  all_goals rfl

theorem atot1323 : totK PA10K2 A10K2.u1323 = [0, 0, 5056030565405, 22254846012320, 32098363497280, 16453703058242, 2616790731361, 111547539915, 0, 0] := by
  rw [show A10K2.u1323 = KTree.node A10K2.u1315 (nat_lit 18608594) (nat_lit 13655768253) (nat_lit 0) A10K2.u1322 from rfl, totK_node, atot1315, atot1322]
  decide +kernel

theorem arows1338 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1338 = true := by
  rw [show A10K2.u1338 = KTree.node A10K2.u1330 (nat_lit 18689943) (nat_lit 14522178997) (nat_lit 0) A10K2.u1337 from rfl, allE_node, arows1330, irow1338, arows1337]
  all_goals rfl

theorem atot1338 : totK PA10K2 A10K2.u1338 = [0, 0, 2796364104103, 15414558974009, 30416272908032, 24202483994802, 6591486195026, 525018890538, 7007974415, 0] := by
  rw [show A10K2.u1338 = KTree.node A10K2.u1330 (nat_lit 18689943) (nat_lit 14522178997) (nat_lit 0) A10K2.u1337 from rfl, totK_node, atot1330, atot1337]
  decide +kernel

theorem arows1355 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1355 = true := by
  rw [show A10K2.u1355 = KTree.node A10K2.u1347 (nat_lit 18866464) (nat_lit 13007362358) (nat_lit 0) A10K2.u1354 from rfl, allE_node, arows1347, irow1355, arows1354]
  all_goals rfl

theorem atot1355 : totK PA10K2 A10K2.u1355 = [0, 0, 2462603361087, 14136305695397, 28482331400523, 24048983311963, 8384207063543, 1091241634064, 41880972333, 0] := by
  rw [show A10K2.u1355 = KTree.node A10K2.u1347 (nat_lit 18866464) (nat_lit 13007362358) (nat_lit 0) A10K2.u1354 from rfl, totK_node, atot1347, atot1354]
  decide +kernel

theorem arows1370 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1370 = true := by
  rw [show A10K2.u1370 = KTree.node A10K2.u1362 (nat_lit 18926404) (nat_lit 12863214254) (nat_lit 0) A10K2.u1369 from rfl, allE_node, arows1362, irow1370, arows1369]
  all_goals rfl

theorem atot1370 : totK PA10K2 A10K2.u1370 = [0, 0, 2575873835572, 13838024254455, 27607785043148, 23604751086406, 7738567654357, 954231378474, 36196801203, 0] := by
  rw [show A10K2.u1370 = KTree.node A10K2.u1362 (nat_lit 18926404) (nat_lit 12863214254) (nat_lit 0) A10K2.u1369 from rfl, totK_node, atot1362, atot1369]
  decide +kernel

theorem arows1386 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1386 = true := by
  rw [show A10K2.u1386 = KTree.node A10K2.u1378 (nat_lit 19075071) (nat_lit 13966711711) (nat_lit 0) A10K2.u1385 from rfl, allE_node, arows1378, irow1386, arows1385]
  all_goals rfl

theorem atot1386 : totK PA10K2 A10K2.u1386 = [0, 0, 2305947832964, 13961973200021, 29344819636400, 24274598667660, 6882785725077, 651699983196, 12881350074, 0] := by
  rw [show A10K2.u1386 = KTree.node A10K2.u1378 (nat_lit 19075071) (nat_lit 13966711711) (nat_lit 0) A10K2.u1385 from rfl, totK_node, atot1378, atot1385]
  decide +kernel

theorem arows1401 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1401 = true := by
  rw [show A10K2.u1401 = KTree.node A10K2.u1393 (nat_lit 19155131) (nat_lit 1583319284) (nat_lit 0) A10K2.u1400 from rfl, allE_node, arows1393, irow1401, arows1400]
  all_goals rfl

theorem atot1401 : totK PA10K2 A10K2.u1401 = [0, 0, 0, 3669008121608, 17732438336981, 29485316350219, 19725103577860, 5588375615637, 711988826368, 30605747850] := by
  rw [show A10K2.u1401 = KTree.node A10K2.u1393 (nat_lit 19155131) (nat_lit 1583319284) (nat_lit 0) A10K2.u1400 from rfl, totK_node, atot1393, atot1400]
  decide +kernel

theorem arows1419 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1419 = true := by
  rw [show A10K2.u1419 = KTree.node A10K2.u1411 (nat_lit 19286022) (nat_lit 11312591296) (nat_lit 0) A10K2.u1418 from rfl, allE_node, arows1411, irow1419, arows1418]
  all_goals rfl

theorem atot1419 : totK PA10K2 A10K2.u1419 = [0, 0, 0, 2799408645344, 15370398530945, 29035377681824, 21022836627029, 5609355124565, 541171770140, 11205006771] := by
  rw [show A10K2.u1419 = KTree.node A10K2.u1411 (nat_lit 19286022) (nat_lit 11312591296) (nat_lit 0) A10K2.u1418 from rfl, totK_node, atot1411, atot1418]
  decide +kernel

theorem arows1434 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1434 = true := by
  rw [show A10K2.u1434 = KTree.node A10K2.u1426 (nat_lit 19940616) (nat_lit 12960116328) (nat_lit 0) A10K2.u1433 from rfl, allE_node, arows1426, irow1434, arows1433]
  all_goals rfl

theorem atot1434 : totK PA10K2 A10K2.u1434 = [0, 0, 2181200105082, 12696172926195, 26879237650643, 24582047233439, 9743870467146, 1565787480695, 81095584216, 0] := by
  rw [show A10K2.u1434 = KTree.node A10K2.u1426 (nat_lit 19940616) (nat_lit 12960116328) (nat_lit 0) A10K2.u1433 from rfl, totK_node, atot1426, atot1433]
  decide +kernel

theorem arows1450 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1450 = true := by
  rw [show A10K2.u1450 = KTree.node A10K2.u1442 (nat_lit 20037907) (nat_lit 10284623048) (nat_lit 0) A10K2.u1449 from rfl, allE_node, arows1442, irow1450, arows1449]
  all_goals rfl

theorem atot1450 : totK PA10K2 A10K2.u1450 = [0, 0, 3159223026771, 16149683225678, 29256268111941, 21190798974185, 5571314156547, 467652609249, 11667478262, 0] := by
  rw [show A10K2.u1450 = KTree.node A10K2.u1442 (nat_lit 20037907) (nat_lit 10284623048) (nat_lit 0) A10K2.u1449 from rfl, totK_node, atot1442, atot1449]
  decide +kernel

theorem arows1465 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1465 = true := by
  rw [show A10K2.u1465 = KTree.node A10K2.u1457 (nat_lit 20187501) (nat_lit 6396598253) (nat_lit 0) A10K2.u1464 from rfl, allE_node, arows1457, irow1465, arows1464]
  all_goals rfl

theorem atot1465 : totK PA10K2 A10K2.u1465 = [0, 0, 308781236982, 7218501502159, 25427350915082, 29745044437570, 11451592618423, 1477976707944, 50380680131, 0] := by
  rw [show A10K2.u1465 = KTree.node A10K2.u1457 (nat_lit 20187501) (nat_lit 6396598253) (nat_lit 0) A10K2.u1464 from rfl, totK_node, atot1457, atot1464]
  decide +kernel

theorem arows1482 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1482 = true := by
  rw [show A10K2.u1482 = KTree.node A10K2.u1474 (nat_lit 20335268) (nat_lit 13693685982) (nat_lit 0) A10K2.u1481 from rfl, allE_node, arows1474, irow1482, arows1481]
  all_goals rfl

theorem atot1482 : totK PA10K2 A10K2.u1482 = [0, 0, 842261825863, 6045197264258, 19047214658716, 28226444966871, 16488516457593, 3573535840447, 310181042276, 5976421810] := by
  rw [show A10K2.u1482 = KTree.node A10K2.u1474 (nat_lit 20335268) (nat_lit 13693685982) (nat_lit 0) A10K2.u1481 from rfl, totK_node, atot1474, atot1481]
  decide +kernel

theorem arows1497 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1497 = true := by
  rw [show A10K2.u1497 = KTree.node A10K2.u1489 (nat_lit 20484717) (nat_lit 5114767867) (nat_lit 0) A10K2.u1496 from rfl, allE_node, arows1489, irow1497, arows1496]
  all_goals rfl

theorem atot1497 : totK PA10K2 A10K2.u1497 = [0, 0, 3056080985897, 15979125275741, 30029231919733, 23093882423440, 6541865012162, 666171511512, 25239774317, 0] := by
  rw [show A10K2.u1497 = KTree.node A10K2.u1489 (nat_lit 20484717) (nat_lit 5114767867) (nat_lit 0) A10K2.u1496 from rfl, totK_node, atot1489, atot1496]
  decide +kernel

theorem arows1513 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1513 = true := by
  rw [show A10K2.u1513 = KTree.node A10K2.u1505 (nat_lit 20677022) (nat_lit 14858508501) (nat_lit 0) A10K2.u1512 from rfl, allE_node, arows1505, irow1513, arows1512]
  all_goals rfl

theorem atot1513 : totK PA10K2 A10K2.u1513 = [0, 857716201818, 5375534748292, 15877940401700, 26554288530438, 22353126752191, 8000095349490, 1076169755701, 42512946920, 0] := by
  rw [show A10K2.u1513 = KTree.node A10K2.u1505 (nat_lit 20677022) (nat_lit 14858508501) (nat_lit 0) A10K2.u1512 from rfl, totK_node, atot1505, atot1512]
  decide +kernel

theorem arows1528 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1528 = true := by
  rw [show A10K2.u1528 = KTree.node A10K2.u1520 (nat_lit 25202569) (nat_lit 8367675134) (nat_lit 0) A10K2.u1527 from rfl, allE_node, arows1520, irow1528, arows1527]
  all_goals rfl

theorem atot1528 : totK PA10K2 A10K2.u1528 = [0, 2222110472546, 13107889019592, 27958632438909, 24888170988736, 8398857633077, 990536584764, 36196801203, 0, 0] := by
  rw [show A10K2.u1528 = KTree.node A10K2.u1520 (nat_lit 25202569) (nat_lit 8367675134) (nat_lit 0) A10K2.u1527 from rfl, totK_node, atot1520, atot1527]
  decide +kernel

theorem arows1548 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1548 = true := by
  rw [show A10K2.u1548 = KTree.node A10K2.u1540 (nat_lit 25346837) (nat_lit 6979538597) (nat_lit 0) A10K2.u1547 from rfl, allE_node, arows1540, irow1548, arows1547]
  all_goals rfl

theorem atot1548 : totK PA10K2 A10K2.u1548 = [0, 2933762722828, 15844431830640, 29945792555048, 22337828310662, 5622927237487, 468975068398, 6354482628, 0, 0] := by
  rw [show A10K2.u1548 = KTree.node A10K2.u1540 (nat_lit 25346837) (nat_lit 6979538597) (nat_lit 0) A10K2.u1547 from rfl, totK_node, atot1540, atot1547]
  decide +kernel

theorem arows1563 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1563 = true := by
  rw [show A10K2.u1563 = KTree.node A10K2.u1555 (nat_lit 25433023) (nat_lit 9955663627) (nat_lit 0) A10K2.u1562 from rfl, allE_node, arows1555, irow1563, arows1562]
  all_goals rfl

theorem atot1563 : totK PA10K2 A10K2.u1563 = [0, 0, 3893577649081, 18973972459460, 31418482198413, 19548157062564, 4262859595503, 398814033011, 20060612110, 0] := by
  rw [show A10K2.u1563 = KTree.node A10K2.u1555 (nat_lit 25433023) (nat_lit 9955663627) (nat_lit 0) A10K2.u1562 from rfl, totK_node, atot1555, atot1562]
  decide +kernel

theorem arows1579 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1579 = true := by
  rw [show A10K2.u1579 = KTree.node A10K2.u1571 (nat_lit 25569502) (nat_lit 10636022587) (nat_lit 0) A10K2.u1578 from rfl, allE_node, arows1571, irow1579, arows1578]
  all_goals rfl

theorem atot1579 : totK PA10K2 A10K2.u1579 = [0, 0, 2113777521167, 13306063604819, 28664680085168, 23588017605349, 6886066195955, 708510771541, 16073946779, 0] := by
  rw [show A10K2.u1579 = KTree.node A10K2.u1571 (nat_lit 25569502) (nat_lit 10636022587) (nat_lit 0) A10K2.u1578 from rfl, totK_node, atot1571, atot1578]
  decide +kernel

theorem arows1594 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1594 = true := by
  rw [show A10K2.u1594 = KTree.node A10K2.u1586 (nat_lit 25767884) (nat_lit 11933677) (nat_lit 0) A10K2.u1593 from rfl, allE_node, arows1586, irow1594, arows1593]
  all_goals rfl

theorem atot1594 : totK PA10K2 A10K2.u1594 = [0, 2185661584285, 12615700036224, 26439249665104, 24475254108203, 10532571431430, 2265663993432, 222016331383, 5676195732, 0] := by
  rw [show A10K2.u1594 = KTree.node A10K2.u1586 (nat_lit 25767884) (nat_lit 11933677) (nat_lit 0) A10K2.u1593 from rfl, totK_node, atot1586, atot1593]
  decide +kernel

theorem arows1611 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1611 = true := by
  rw [show A10K2.u1611 = KTree.node A10K2.u1603 (nat_lit 25831532) (nat_lit 11724389142) (nat_lit 0) A10K2.u1610 from rfl, allE_node, arows1603, irow1611, arows1610]
  all_goals rfl

theorem atot1611 : totK PA10K2 A10K2.u1611 = [0, 2148948818715, 12868441479817, 27450019718208, 24562279638256, 8465008630518, 1034652738775, 37204059898, 0, 0] := by
  rw [show A10K2.u1611 = KTree.node A10K2.u1603 (nat_lit 25831532) (nat_lit 11724389142) (nat_lit 0) A10K2.u1610 from rfl, totK_node, atot1603, atot1610]
  decide +kernel

theorem arows1626 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1626 = true := by
  rw [show A10K2.u1626 = KTree.node A10K2.u1618 (nat_lit 26043674) (nat_lit 14731252833) (nat_lit 0) A10K2.u1625 from rfl, allE_node, arows1618, irow1626, arows1625]
  all_goals rfl

theorem atot1626 : totK PA10K2 A10K2.u1626 = [0, 0, 4907679684626, 21874665142683, 31860727764154, 15740494063315, 2317796287447, 88554889312, 0, 0] := by
  rw [show A10K2.u1626 = KTree.node A10K2.u1618 (nat_lit 26043674) (nat_lit 14731252833) (nat_lit 0) A10K2.u1625 from rfl, totK_node, atot1618, atot1625]
  decide +kernel

theorem arows1642 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1642 = true := by
  rw [show A10K2.u1642 = KTree.node A10K2.u1634 (nat_lit 26218569) (nat_lit 9594707706) (nat_lit 0) A10K2.u1641 from rfl, allE_node, arows1634, irow1642, arows1641]
  all_goals rfl

theorem atot1642 : totK PA10K2 A10K2.u1642 = [0, 2093964635397, 10527198864561, 21632068209664, 23972943588331, 14289170938789, 3439453456701, 315882843200, 6239673734, 0] := by
  rw [show A10K2.u1642 = KTree.node A10K2.u1634 (nat_lit 26218569) (nat_lit 9594707706) (nat_lit 0) A10K2.u1641 from rfl, totK_node, atot1634, atot1641]
  decide +kernel

theorem arows1657 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1657 = true := by
  rw [show A10K2.u1657 = KTree.node A10K2.u1649 (nat_lit 26298026) (nat_lit 12807045655) (nat_lit 0) A10K2.u1656 from rfl, allE_node, arows1649, irow1657, arows1656]
  all_goals rfl

theorem atot1657 : totK PA10K2 A10K2.u1657 = [0, 1812581868266, 11241080461623, 26038508208447, 26165497932772, 9959784898465, 1239939977860, 47219075702, 0, 0] := by
  rw [show A10K2.u1657 = KTree.node A10K2.u1649 (nat_lit 26298026) (nat_lit 12807045655) (nat_lit 0) A10K2.u1656 from rfl, totK_node, atot1649, atot1656]
  decide +kernel

theorem arows1675 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1675 = true := by
  rw [show A10K2.u1675 = KTree.node A10K2.u1667 (nat_lit 26364781) (nat_lit 6356241174) (nat_lit 0) A10K2.u1674 from rfl, allE_node, arows1667, irow1675, arows1674]
  all_goals rfl

theorem atot1675 : totK PA10K2 A10K2.u1675 = [0, 2296331471068, 13871465974658, 28657311606952, 23427480997193, 6676476184023, 656624452347, 12475655917, 0, 0] := by
  rw [show A10K2.u1675 = KTree.node A10K2.u1667 (nat_lit 26364781) (nat_lit 6356241174) (nat_lit 0) A10K2.u1674 from rfl, totK_node, atot1667, atot1674]
  decide +kernel

theorem arows1690 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1690 = true := by
  rw [show A10K2.u1690 = KTree.node A10K2.u1682 (nat_lit 26555777) (nat_lit 11933677) (nat_lit 0) A10K2.u1689 from rfl, allE_node, arows1682, irow1690, arows1689]
  all_goals rfl

theorem atot1690 : totK PA10K2 A10K2.u1690 = [0, 0, 4371549456299, 20602540650670, 31889280005544, 16914691032413, 2619763905177, 111908137527, 0, 0] := by
  rw [show A10K2.u1690 = KTree.node A10K2.u1682 (nat_lit 26555777) (nat_lit 11933677) (nat_lit 0) A10K2.u1689 from rfl, totK_node, atot1682, atot1689]
  decide +kernel

theorem arows1706 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1706 = true := by
  rw [show A10K2.u1706 = KTree.node A10K2.u1698 (nat_lit 26658024) (nat_lit 6435602749) (nat_lit 0) A10K2.u1705 from rfl, allE_node, arows1698, irow1706, arows1705]
  all_goals rfl

theorem atot1706 : totK PA10K2 A10K2.u1706 = [0, 0, 3035040200260, 16185616864087, 29661434087250, 20419241702204, 4968232631453, 453152165063, 6354482628, 0] := by
  rw [show A10K2.u1706 = KTree.node A10K2.u1698 (nat_lit 26658024) (nat_lit 6435602749) (nat_lit 0) A10K2.u1705 from rfl, totK_node, atot1698, atot1705]
  decide +kernel

theorem arows1721 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1721 = true := by
  rw [show A10K2.u1721 = KTree.node A10K2.u1713 (nat_lit 27320647) (nat_lit 6166852643) (nat_lit 0) A10K2.u1720 from rfl, allE_node, arows1713, irow1721, arows1720]
  all_goals rfl

theorem atot1721 : totK PA10K2 A10K2.u1721 = [0, 0, 2500926709266, 14234885015117, 28422339597382, 23538899932680, 7491821436430, 939243146578, 36196801203, 0] := by
  rw [show A10K2.u1721 = KTree.node A10K2.u1713 (nat_lit 27320647) (nat_lit 6166852643) (nat_lit 0) A10K2.u1720 from rfl, totK_node, atot1713, atot1720]
  decide +kernel

theorem arows1738 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1738 = true := by
  rw [show A10K2.u1738 = KTree.node A10K2.u1730 (nat_lit 27466005) (nat_lit 6862298905) (nat_lit 0) A10K2.u1737 from rfl, allE_node, arows1730, irow1738, arows1737]
  all_goals rfl

theorem atot1738 : totK PA10K2 A10K2.u1738 = [0, 0, 2020241700918, 12881758809960, 29095064248097, 25957140261375, 7768449048851, 733774417769, 13259410892, 0] := by
  rw [show A10K2.u1738 = KTree.node A10K2.u1730 (nat_lit 27466005) (nat_lit 6862298905) (nat_lit 0) A10K2.u1737 from rfl, totK_node, atot1730, atot1737]
  decide +kernel

theorem arows1753 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1753 = true := by
  rw [show A10K2.u1753 = KTree.node A10K2.u1745 (nat_lit 27920936) (nat_lit 12578888093) (nat_lit 0) A10K2.u1752 from rfl, allE_node, arows1745, irow1753, arows1752]
  all_goals rfl

theorem atot1753 : totK PA10K2 A10K2.u1753 = [0, 0, 3912814809189, 19394377109486, 31897926257829, 18665225480733, 3092912913567, 116946631867, 0, 0] := by
  rw [show A10K2.u1753 = KTree.node A10K2.u1745 (nat_lit 27920936) (nat_lit 12578888093) (nat_lit 0) A10K2.u1752 from rfl, totK_node, atot1745, atot1752]
  decide +kernel

theorem arows1769 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1769 = true := by
  rw [show A10K2.u1769 = KTree.node A10K2.u1761 (nat_lit 28330146) (nat_lit 13527284891) (nat_lit 0) A10K2.u1768 from rfl, allE_node, arows1761, irow1769, arows1768]
  all_goals rfl

theorem atot1769 : totK PA10K2 A10K2.u1769 = [0, 0, 2088213763383, 12729820560984, 27869527971483, 24790553879285, 7688310466041, 893052487753, 36575360998, 0] := by
  rw [show A10K2.u1769 = KTree.node A10K2.u1761 (nat_lit 28330146) (nat_lit 13527284891) (nat_lit 0) A10K2.u1768 from rfl, totK_node, atot1761, atot1768]
  decide +kernel

theorem arows1784 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1784 = true := by
  rw [show A10K2.u1784 = KTree.node A10K2.u1776 (nat_lit 28419938) (nat_lit 12921064822) (nat_lit 0) A10K2.u1783 from rfl, allE_node, arows1776, irow1784, arows1783]
  all_goals rfl

theorem atot1784 : totK PA10K2 A10K2.u1784 = [0, 0, 3251376319593, 16675967630659, 29689429478777, 21146673155705, 5402209186487, 527153398859, 11667478262, 0] := by
  rw [show A10K2.u1784 = KTree.node A10K2.u1776 (nat_lit 28419938) (nat_lit 12921064822) (nat_lit 0) A10K2.u1783 from rfl, totK_node, atot1776, atot1783]
  decide +kernel

theorem arows1803 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1803 = true := by
  rw [show A10K2.u1803 = KTree.node A10K2.u1795 (nat_lit 28494491) (nat_lit 9653417816) (nat_lit 0) A10K2.u1802 from rfl, allE_node, arows1795, irow1803, arows1802]
  all_goals rfl

theorem atot1803 : totK PA10K2 A10K2.u1803 = [0, 0, 845557281498, 8989646737042, 26345578561324, 28161599694073, 9951104711913, 1216957372326, 43097714263, 0] := by
  rw [show A10K2.u1803 = KTree.node A10K2.u1795 (nat_lit 28494491) (nat_lit 9653417816) (nat_lit 0) A10K2.u1802 from rfl, totK_node, atot1795, atot1802]
  decide +kernel

theorem arows1818 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1818 = true := by
  rw [show A10K2.u1818 = KTree.node A10K2.u1810 (nat_lit 28719175) (nat_lit 4660135217) (nat_lit 0) A10K2.u1817 from rfl, allE_node, arows1810, irow1818, arows1817]
  all_goals rfl

theorem atot1818 : totK PA10K2 A10K2.u1818 = [0, 157526836586, 329480614415, 3960086501755, 18639974162099, 30204951485287, 17321493734816, 3926882155506, 312307117555, 6354482628] := by
  rw [show A10K2.u1818 = KTree.node A10K2.u1810 (nat_lit 28719175) (nat_lit 4660135217) (nat_lit 0) A10K2.u1817 from rfl, totK_node, atot1810, atot1817]
  decide +kernel

theorem arows1834 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1834 = true := by
  rw [show A10K2.u1834 = KTree.node A10K2.u1826 (nat_lit 29392319) (nat_lit 14319036847) (nat_lit 0) A10K2.u1833 from rfl, allE_node, arows1826, irow1834, arows1833]
  all_goals rfl

theorem atot1834 : totK PA10K2 A10K2.u1834 = [0, 2649329046225, 14259404202857, 27965136261464, 23733572034377, 8051300911150, 989397257013, 36196801203, 0, 0] := by
  rw [show A10K2.u1834 = KTree.node A10K2.u1826 (nat_lit 29392319) (nat_lit 14319036847) (nat_lit 0) A10K2.u1833 from rfl, totK_node, atot1826, atot1833]
  decide +kernel

theorem arows1849 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1849 = true := by
  rw [show A10K2.u1849 = KTree.node A10K2.u1841 (nat_lit 29546652) (nat_lit 11901295526) (nat_lit 0) A10K2.u1848 from rfl, allE_node, arows1841, irow1849, arows1848]
  all_goals rfl

theorem atot1849 : totK PA10K2 A10K2.u1849 = [0, 3238958246903, 17075364465310, 30823309033399, 21494485686057, 5016654429237, 360255829333, 6354482628, 0, 0] := by
  rw [show A10K2.u1849 = KTree.node A10K2.u1841 (nat_lit 29546652) (nat_lit 11901295526) (nat_lit 0) A10K2.u1848 from rfl, totK_node, atot1841, atot1848]
  decide +kernel

theorem arows1866 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1866 = true := by
  rw [show A10K2.u1866 = KTree.node A10K2.u1858 (nat_lit 29619877) (nat_lit 1772082894) (nat_lit 0) A10K2.u1865 from rfl, allE_node, arows1858, irow1866, arows1865]
  all_goals rfl

theorem atot1866 : totK PA10K2 A10K2.u1866 = [0, 0, 4846947996464, 21751618228785, 32225714526325, 16857685789989, 2666846984343, 111598773623, 0, 0] := by
  rw [show A10K2.u1866 = KTree.node A10K2.u1858 (nat_lit 29619877) (nat_lit 1772082894) (nat_lit 0) A10K2.u1865 from rfl, totK_node, atot1858, atot1865]
  decide +kernel

theorem arows1881 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1881 = true := by
  rw [show A10K2.u1881 = KTree.node A10K2.u1873 (nat_lit 29754218) (nat_lit 5361535461) (nat_lit 0) A10K2.u1880 from rfl, allE_node, arows1873, irow1881, arows1880]
  all_goals rfl

theorem atot1881 : totK PA10K2 A10K2.u1881 = [0, 0, 2589639054361, 14562638555301, 28677158992168, 23048126547909, 7376408713880, 939588473651, 36134558889, 0] := by
  rw [show A10K2.u1881 = KTree.node A10K2.u1873 (nat_lit 29754218) (nat_lit 5361535461) (nat_lit 0) A10K2.u1880 from rfl, totK_node, atot1873, atot1880]
  decide +kernel

theorem arows1897 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1897 = true := by
  rw [show A10K2.u1897 = KTree.node A10K2.u1889 (nat_lit 29965780) (nat_lit 8038786286) (nat_lit 0) A10K2.u1896 from rfl, allE_node, arows1889, irow1897, arows1896]
  all_goals rfl

theorem atot1897 : totK PA10K2 A10K2.u1897 = [0, 2211226772095, 12315452279191, 25806288517251, 25129910419236, 11377118327068, 2007571545895, 100602630508, 0, 0] := by
  rw [show A10K2.u1897 = KTree.node A10K2.u1889 (nat_lit 29965780) (nat_lit 8038786286) (nat_lit 0) A10K2.u1896 from rfl, totK_node, atot1889, atot1896]
  decide +kernel

theorem arows1912 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1912 = true := by
  rw [show A10K2.u1912 = KTree.node A10K2.u1904 (nat_lit 30095520) (nat_lit 3966561664) (nat_lit 0) A10K2.u1911 from rfl, allE_node, arows1904, irow1912, arows1911]
  all_goals rfl

theorem atot1912 : totK PA10K2 A10K2.u1912 = [0, 2246501693213, 13233153766501, 28419416078169, 25951146564405, 8957426844228, 856669330291, 13026101553, 0, 0] := by
  rw [show A10K2.u1912 = KTree.node A10K2.u1904 (nat_lit 30095520) (nat_lit 3966561664) (nat_lit 0) A10K2.u1911 from rfl, totK_node, atot1904, atot1911]
  decide +kernel

theorem arows1930 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1930 = true := by
  rw [show A10K2.u1930 = KTree.node A10K2.u1922 (nat_lit 30230689) (nat_lit 8088243184) (nat_lit 0) A10K2.u1929 from rfl, allE_node, arows1922, irow1930, arows1929]
  all_goals rfl

theorem atot1930 : totK PA10K2 A10K2.u1930 = [0, 0, 3075507852395, 16537123469107, 30654276762041, 22275502242139, 5703246100071, 486095540365, 8047840951, 0] := by
  rw [show A10K2.u1930 = KTree.node A10K2.u1922 (nat_lit 30230689) (nat_lit 8088243184) (nat_lit 0) A10K2.u1929 from rfl, totK_node, atot1922, atot1929]
  decide +kernel

theorem arows1945 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1945 = true := by
  rw [show A10K2.u1945 = KTree.node A10K2.u1937 (nat_lit 30372450) (nat_lit 11933677) (nat_lit 0) A10K2.u1944 from rfl, allE_node, arows1937, irow1945, arows1944]
  all_goals rfl

theorem atot1945 : totK PA10K2 A10K2.u1945 = [0, 2127308439256, 11608827089640, 24463432233562, 25382521148078, 13229567951242, 2585454743016, 127797284249, 0, 0] := by
  rw [show A10K2.u1945 = KTree.node A10K2.u1937 (nat_lit 30372450) (nat_lit 11933677) (nat_lit 0) A10K2.u1944 from rfl, totK_node, atot1937, atot1944]
  decide +kernel

theorem arows1961 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1961 = true := by
  rw [show A10K2.u1961 = KTree.node A10K2.u1953 (nat_lit 31008997) (nat_lit 7119318088) (nat_lit 0) A10K2.u1960 from rfl, allE_node, arows1953, irow1961, arows1960]
  all_goals rfl

theorem atot1961 : totK PA10K2 A10K2.u1961 = [0, 1876293614846, 12199770600307, 28174742720520, 26835236699202, 9127984570537, 989187152846, 30650496230, 0, 0] := by
  rw [show A10K2.u1961 = KTree.node A10K2.u1953 (nat_lit 31008997) (nat_lit 7119318088) (nat_lit 0) A10K2.u1960 from rfl, totK_node, atot1953, atot1960]
  decide +kernel

theorem arows1976 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1976 = true := by
  rw [show A10K2.u1976 = KTree.node A10K2.u1968 (nat_lit 31143194) (nat_lit 14745446160) (nat_lit 0) A10K2.u1975 from rfl, allE_node, arows1968, irow1976, arows1975]
  all_goals rfl

theorem atot1976 : totK PA10K2 A10K2.u1976 = [0, 2388837666370, 13433835225526, 27803943546622, 25002600414629, 8953993210440, 1010573667927, 20481146374, 0, 0] := by
  rw [show A10K2.u1976 = KTree.node A10K2.u1968 (nat_lit 31143194) (nat_lit 14745446160) (nat_lit 0) A10K2.u1975 from rfl, totK_node, atot1968, atot1975]
  decide +kernel

theorem arows1993 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1993 = true := by
  rw [show A10K2.u1993 = KTree.node A10K2.u1985 (nat_lit 31202380) (nat_lit 8940810305) (nat_lit 0) A10K2.u1992 from rfl, allE_node, arows1985, irow1993, arows1992]
  all_goals rfl

theorem atot1993 : totK PA10K2 A10K2.u1993 = [0, 0, 3325648453483, 17077968139167, 30493506954880, 21684203018980, 5646329346182, 489592634675, 7007974415, 0] := by
  rw [show A10K2.u1993 = KTree.node A10K2.u1985 (nat_lit 31202380) (nat_lit 8940810305) (nat_lit 0) A10K2.u1992 from rfl, totK_node, atot1985, atot1992]
  decide +kernel

theorem arows2008 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2008 = true := by
  rw [show A10K2.u2008 = KTree.node A10K2.u2000 (nat_lit 31290761) (nat_lit 7165888537) (nat_lit 0) A10K2.u2007 from rfl, allE_node, arows2000, irow2008, arows2007]
  all_goals rfl

theorem atot2008 : totK PA10K2 A10K2.u2008 = [0, 0, 2667910901263, 15214338497539, 30367582975727, 24422386132887, 6688246522143, 498592456958, 7151180950, 0] := by
  rw [show A10K2.u2008 = KTree.node A10K2.u2000 (nat_lit 31290761) (nat_lit 7165888537) (nat_lit 0) A10K2.u2007 from rfl, totK_node, atot2000, atot2007]
  decide +kernel

theorem arows2024 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2024 = true := by
  rw [show A10K2.u2024 = KTree.node A10K2.u2016 (nat_lit 31429132) (nat_lit 9952412231) (nat_lit 0) A10K2.u2023 from rfl, allE_node, arows2016, irow2024, arows2023]
  all_goals rfl

theorem atot2024 : totK PA10K2 A10K2.u2024 = [876250713213, 3080719290227, 4638042710902, 10711033202986, 23114240194681, 24147113484130, 10525736519092, 1632372015925, 73776485728, 0] := by
  rw [show A10K2.u2024 = KTree.node A10K2.u2016 (nat_lit 31429132) (nat_lit 9952412231) (nat_lit 0) A10K2.u2023 from rfl, totK_node, atot2016, atot2023]
  decide +kernel

theorem arows2039 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2039 = true := by
  rw [show A10K2.u2039 = KTree.node A10K2.u2031 (nat_lit 38381674) (nat_lit 5641286180) (nat_lit 0) A10K2.u2038 from rfl, allE_node, arows2031, irow2039, arows2038]
  all_goals rfl

theorem atot2039 : totK PA10K2 A10K2.u2039 = [1932579139760, 12345251702385, 27475119099432, 25162075696977, 8905563639327, 1062339829472, 37204059898, 0, 0, 0] := by
  rw [show A10K2.u2039 = KTree.node A10K2.u2031 (nat_lit 38381674) (nat_lit 5641286180) (nat_lit 0) A10K2.u2038 from rfl, totK_node, atot2031, atot2038]
  decide +kernel

theorem arows2061 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2061 = true := by
  rw [show A10K2.u2061 = KTree.node A10K2.u2053 (nat_lit 38448300) (nat_lit 11430406129) (nat_lit 0) A10K2.u2060 from rfl, allE_node, arows2053, irow2061, arows2060]
  all_goals rfl

theorem atot2061 : totK PA10K2 A10K2.u2061 = [3095636918978, 16096808302086, 29680957675466, 21983076935243, 5622698529738, 477127598093, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u2061 = KTree.node A10K2.u2053 (nat_lit 38448300) (nat_lit 11430406129) (nat_lit 0) A10K2.u2060 from rfl, totK_node, atot2053, atot2060]
  decide +kernel

theorem arows2076 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2076 = true := by
  rw [show A10K2.u2076 = KTree.node A10K2.u2068 (nat_lit 38528446) (nat_lit 16292101936) (nat_lit 0) A10K2.u2075 from rfl, allE_node, arows2068, irow2076, arows2075]
  all_goals rfl

theorem atot2076 : totK PA10K2 A10K2.u2076 = [613328696870, 6910555890912, 23081299936417, 30364065644368, 15233982872157, 2462357039034, 106830828675, 0, 0, 0] := by
  rw [show A10K2.u2076 = KTree.node A10K2.u2068 (nat_lit 38528446) (nat_lit 16292101936) (nat_lit 0) A10K2.u2075 from rfl, totK_node, atot2068, atot2075]
  decide +kernel

theorem arows2092 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2092 = true := by
  rw [show A10K2.u2092 = KTree.node A10K2.u2084 (nat_lit 38655134) (nat_lit 13921104357) (nat_lit 0) A10K2.u2091 from rfl, allE_node, arows2084, irow2092, arows2091]
  all_goals rfl

theorem atot2092 : totK PA10K2 A10K2.u2092 = [0, 2786994674695, 14284862599884, 27600297390067, 23336723551219, 7744072940296, 955555283053, 36704093874, 0, 0] := by
  rw [show A10K2.u2092 = KTree.node A10K2.u2084 (nat_lit 38655134) (nat_lit 13921104357) (nat_lit 0) A10K2.u2091 from rfl, totK_node, atot2084, atot2091]
  decide +kernel

theorem arows2107 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2107 = true := by
  rw [show A10K2.u2107 = KTree.node A10K2.u2099 (nat_lit 38741253) (nat_lit 6074938325) (nat_lit 0) A10K2.u2106 from rfl, allE_node, arows2099, irow2107, arows2106]
  all_goals rfl

theorem atot2107 : totK PA10K2 A10K2.u2107 = [560981842138, 4559040238730, 16427288074173, 28636220546466, 21356974792686, 5333707230213, 403371066377, 6239673734, 0, 0] := by
  rw [show A10K2.u2107 = KTree.node A10K2.u2099 (nat_lit 38741253) (nat_lit 6074938325) (nat_lit 0) A10K2.u2106 from rfl, totK_node, atot2099, atot2106]
  decide +kernel

theorem arows2124 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2124 = true := by
  rw [show A10K2.u2124 = KTree.node A10K2.u2116 (nat_lit 38872914) (nat_lit 14828695722) (nat_lit 0) A10K2.u2123 from rfl, allE_node, arows2116, irow2124, arows2123]
  all_goals rfl

theorem atot2124 : totK PA10K2 A10K2.u2124 = [2935627200832, 15414166414662, 28687282470372, 21983059619003, 6750093242939, 855610393987, 36196801203, 0, 0, 0] := by
  rw [show A10K2.u2124 = KTree.node A10K2.u2116 (nat_lit 38872914) (nat_lit 14828695722) (nat_lit 0) A10K2.u2123 from rfl, totK_node, atot2116, atot2123]
  decide +kernel

theorem arows2139 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2139 = true := by
  rw [show A10K2.u2139 = KTree.node A10K2.u2131 (nat_lit 38933255) (nat_lit 9221651913) (nat_lit 0) A10K2.u2138 from rfl, allE_node, arows2131, irow2139, arows2138]
  all_goals rfl

theorem atot2139 : totK PA10K2 A10K2.u2139 = [2174123190330, 12826329896463, 27090671326591, 24283049700872, 8622876623182, 1038898813349, 37204059898, 0, 0, 0] := by
  rw [show A10K2.u2139 = KTree.node A10K2.u2131 (nat_lit 38933255) (nat_lit 9221651913) (nat_lit 0) A10K2.u2138 from rfl, totK_node, atot2131, atot2138]
  decide +kernel

theorem arows2155 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2155 = true := by
  rw [show A10K2.u2155 = KTree.node A10K2.u2147 (nat_lit 39081992) (nat_lit 14111335316) (nat_lit 0) A10K2.u2154 from rfl, allE_node, arows2147, irow2155, arows2154]
  all_goals rfl

theorem atot2155 : totK PA10K2 A10K2.u2155 = [0, 4780406966652, 21571746695611, 31571873796757, 15833787119558, 2432380666837, 88297130952, 0, 0, 0] := by
  rw [show A10K2.u2155 = KTree.node A10K2.u2147 (nat_lit 39081992) (nat_lit 14111335316) (nat_lit 0) A10K2.u2154 from rfl, totK_node, atot2147, atot2154]
  decide +kernel

theorem arows2170 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2170 = true := by
  rw [show A10K2.u2170 = KTree.node A10K2.u2162 (nat_lit 39213411) (nat_lit 9194853334) (nat_lit 0) A10K2.u2169 from rfl, allE_node, arows2162, irow2170, arows2169]
  all_goals rfl

theorem atot2170 : totK PA10K2 A10K2.u2170 = [953763886815, 6024387698014, 17868167501064, 27133821107122, 18495084180030, 4680300365842, 446040892095, 6354482628, 0, 0] := by
  rw [show A10K2.u2170 = KTree.node A10K2.u2162 (nat_lit 39213411) (nat_lit 9194853334) (nat_lit 0) A10K2.u2169 from rfl, totK_node, atot2162, atot2169]
  decide +kernel

theorem arows2188 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2188 = true := by
  rw [show A10K2.u2188 = KTree.node A10K2.u2180 (nat_lit 39400662) (nat_lit 14738388334) (nat_lit 0) A10K2.u2187 from rfl, allE_node, arows2180, irow2188, arows2187]
  all_goals rfl

theorem atot2188 : totK PA10K2 A10K2.u2188 = [2651214091375, 15209503022134, 30192445258456, 24192057767203, 6952517160947, 679419005862, 25239774317, 0, 0, 0] := by
  rw [show A10K2.u2188 = KTree.node A10K2.u2180 (nat_lit 39400662) (nat_lit 14738388334) (nat_lit 0) A10K2.u2187 from rfl, totK_node, atot2180, atot2187]
  decide +kernel

theorem arows2203 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2203 = true := by
  rw [show A10K2.u2203 = KTree.node A10K2.u2195 (nat_lit 39528663) (nat_lit 11681737993) (nat_lit 0) A10K2.u2202 from rfl, allE_node, arows2195, irow2203, arows2202]
  all_goals rfl

theorem atot2203 : totK PA10K2 A10K2.u2203 = [2284714674300, 12838431718964, 26982346594531, 25469140848169, 10015187683416, 1334192409090, 44108988162, 0, 0, 0] := by
  rw [show A10K2.u2203 = KTree.node A10K2.u2195 (nat_lit 39528663) (nat_lit 11681737993) (nat_lit 0) A10K2.u2202 from rfl, totK_node, atot2195, atot2202]
  decide +kernel

theorem arows2219 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2219 = true := by
  rw [show A10K2.u2219 = KTree.node A10K2.u2211 (nat_lit 39591390) (nat_lit 14811449216) (nat_lit 0) A10K2.u2218 from rfl, allE_node, arows2211, irow2219, arows2218]
  all_goals rfl

theorem atot2219 : totK PA10K2 A10K2.u2219 = [0, 3624697239447, 17736532040592, 30416565078368, 21775869770990, 5961523216545, 530991723887, 7007974415, 0, 0] := by
  rw [show A10K2.u2219 = KTree.node A10K2.u2211 (nat_lit 39591390) (nat_lit 14811449216) (nat_lit 0) A10K2.u2218 from rfl, totK_node, atot2211, atot2218]
  decide +kernel

theorem arows2234 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2234 = true := by
  rw [show A10K2.u2234 = KTree.node A10K2.u2226 (nat_lit 39693138) (nat_lit 13798124545) (nat_lit 0) A10K2.u2233 from rfl, allE_node, arows2226, irow2234, arows2233]
  all_goals rfl

theorem atot2234 : totK PA10K2 A10K2.u2234 = [0, 2851163083637, 15921594049335, 30446448042211, 23081108062648, 6301119253575, 522761192934, 7151180950, 0, 0] := by
  rw [show A10K2.u2234 = KTree.node A10K2.u2226 (nat_lit 39693138) (nat_lit 13798124545) (nat_lit 0) A10K2.u2233 from rfl, totK_node, atot2226, atot2233]
  decide +kernel

theorem arows2251 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2251 = true := by
  rw [show A10K2.u2251 = KTree.node A10K2.u2243 (nat_lit 39824968) (nat_lit 12201256997) (nat_lit 0) A10K2.u2250 from rfl, allE_node, arows2243, irow2251, arows2250]
  all_goals rfl

theorem atot2251 : totK PA10K2 A10K2.u2251 = [0, 1894157213777, 11428641032711, 26066005867939, 26456242753150, 11111234439269, 1664140764778, 73776485728, 0, 0] := by
  rw [show A10K2.u2251 = KTree.node A10K2.u2243 (nat_lit 39824968) (nat_lit 12201256997) (nat_lit 0) A10K2.u2250 from rfl, totK_node, atot2243, atot2250]
  decide +kernel

theorem arows2266 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2266 = true := by
  rw [show A10K2.u2266 = KTree.node A10K2.u2258 (nat_lit 40483043) (nat_lit 10379010550) (nat_lit 0) A10K2.u2265 from rfl, allE_node, arows2258, irow2266, arows2265]
  all_goals rfl

theorem atot2266 : totK PA10K2 A10K2.u2266 = [0, 2586685855837, 14211509864760, 27841118640428, 23311043150091, 8005313460563, 982655605174, 37204059898, 0, 0] := by
  rw [show A10K2.u2266 = KTree.node A10K2.u2258 (nat_lit 40483043) (nat_lit 10379010550) (nat_lit 0) A10K2.u2265 from rfl, totK_node, atot2258, atot2265]
  decide +kernel

theorem arows2282 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2282 = true := by
  rw [show A10K2.u2282 = KTree.node A10K2.u2274 (nat_lit 40555698) (nat_lit 14807146858) (nat_lit 0) A10K2.u2281 from rfl, allE_node, arows2274, irow2282, arows2281]
  all_goals rfl

theorem atot2282 : totK PA10K2 A10K2.u2282 = [0, 2903302422428, 15734382882278, 30083692758142, 22583274109196, 5459664797324, 387293423643, 6354482628, 0, 0] := by
  rw [show A10K2.u2282 = KTree.node A10K2.u2274 (nat_lit 40555698) (nat_lit 14807146858) (nat_lit 0) A10K2.u2281 from rfl, totK_node, atot2274, atot2281]
  decide +kernel

theorem arows2297 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2297 = true := by
  rw [show A10K2.u2297 = KTree.node A10K2.u2289 (nat_lit 40632306) (nat_lit 13452139763) (nat_lit 0) A10K2.u2296 from rfl, allE_node, arows2289, irow2297, arows2296]
  all_goals rfl

theorem atot2297 : totK PA10K2 A10K2.u2297 = [0, 0, 4814523071830, 21849050672355, 32318569850582, 16767891793421, 2566498646317, 93148485416, 0, 0] := by
  rw [show A10K2.u2297 = KTree.node A10K2.u2289 (nat_lit 40632306) (nat_lit 13452139763) (nat_lit 0) A10K2.u2296 from rfl, totK_node, atot2289, atot2296]
  decide +kernel

theorem arows2316 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2316 = true := by
  rw [show A10K2.u2316 = KTree.node A10K2.u2308 (nat_lit 40767786) (nat_lit 9050087185) (nat_lit 0) A10K2.u2315 from rfl, allE_node, arows2308, irow2316, arows2315]
  all_goals rfl

theorem atot2316 : totK PA10K2 A10K2.u2316 = [0, 0, 1994586508952, 12782794476436, 27800328249702, 23765736548624, 7676370307743, 970637717157, 36704093874, 0] := by
  rw [show A10K2.u2316 = KTree.node A10K2.u2308 (nat_lit 40767786) (nat_lit 9050087185) (nat_lit 0) A10K2.u2315 from rfl, totK_node, atot2308, atot2315]
  decide +kernel

theorem arows2331 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2331 = true := by
  rw [show A10K2.u2331 = KTree.node A10K2.u2323 (nat_lit 40857594) (nat_lit 12700502014) (nat_lit 0) A10K2.u2330 from rfl, allE_node, arows2323, irow2331, arows2330]
  all_goals rfl

theorem atot2331 : totK PA10K2 A10K2.u2331 = [0, 1299799213788, 9179139870493, 22916086501511, 25914665933107, 14250225387513, 3379336097856, 299353888095, 5982052406, 0] := by
  rw [show A10K2.u2331 = KTree.node A10K2.u2323 (nat_lit 40857594) (nat_lit 12700502014) (nat_lit 0) A10K2.u2330 from rfl, totK_node, atot2323, atot2330]
  decide +kernel

theorem arows2347 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2347 = true := by
  rw [show A10K2.u2347 = KTree.node A10K2.u2339 (nat_lit 40988058) (nat_lit 14554951347) (nat_lit 0) A10K2.u2346 from rfl, allE_node, arows2339, irow2347, arows2346]
  all_goals rfl

theorem atot2347 : totK PA10K2 A10K2.u2347 = [0, 2196809829182, 12664103420509, 26967145373702, 24888393223602, 9013549157548, 1147888643786, 42750364871, 0, 0] := by
  rw [show A10K2.u2347 = KTree.node A10K2.u2339 (nat_lit 40988058) (nat_lit 14554951347) (nat_lit 0) A10K2.u2346 from rfl, totK_node, atot2339, atot2346]
  decide +kernel

theorem arows2362 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2362 = true := by
  rw [show A10K2.u2362 = KTree.node A10K2.u2354 (nat_lit 41048326) (nat_lit 8287825324) (nat_lit 0) A10K2.u2361 from rfl, allE_node, arows2354, irow2362, arows2361]
  all_goals rfl

theorem atot2362 : totK PA10K2 A10K2.u2362 = [0, 2174123190330, 13037151984058, 27813948463629, 24222436357466, 7428356539943, 729966593405, 11801668502, 0, 0] := by
  rw [show A10K2.u2362 = KTree.node A10K2.u2354 (nat_lit 41048326) (nat_lit 8287825324) (nat_lit 0) A10K2.u2361 from rfl, totK_node, atot2354, atot2361]
  decide +kernel

theorem arows2379 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2379 = true := by
  rw [show A10K2.u2379 = KTree.node A10K2.u2371 (nat_lit 41248187) (nat_lit 7035925206) (nat_lit 0) A10K2.u2378 from rfl, allE_node, arows2371, irow2379, arows2378]
  all_goals rfl

theorem atot2379 : totK PA10K2 A10K2.u2379 = [0, 0, 4863371925687, 21774035945261, 31735165768528, 15399431836207, 2208199251845, 87588219036, 0, 0] := by
  rw [show A10K2.u2379 = KTree.node A10K2.u2371 (nat_lit 41248187) (nat_lit 7035925206) (nat_lit 0) A10K2.u2378 from rfl, totK_node, atot2371, atot2378]
  decide +kernel

theorem arows2394 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2394 = true := by
  rw [show A10K2.u2394 = KTree.node A10K2.u2386 (nat_lit 41423792) (nat_lit 14652486819) (nat_lit 0) A10K2.u2393 from rfl, allE_node, arows2386, irow2394, arows2393]
  all_goals rfl

theorem atot2394 : totK PA10K2 A10K2.u2394 = [0, 1934017180087, 9751812733069, 21170881938174, 25730770225834, 15289043250774, 3542262661102, 309426632483, 6354482628, 0] := by
  rw [show A10K2.u2394 = KTree.node A10K2.u2386 (nat_lit 41423792) (nat_lit 14652486819) (nat_lit 0) A10K2.u2393 from rfl, totK_node, atot2386, atot2393]
  decide +kernel

theorem arows2410 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2410 = true := by
  rw [show A10K2.u2410 = KTree.node A10K2.u2402 (nat_lit 41527464) (nat_lit 7370723861) (nat_lit 0) A10K2.u2409 from rfl, allE_node, arows2402, irow2410, arows2409]
  all_goals rfl

theorem atot2410 : totK PA10K2 A10K2.u2410 = [0, 2292165169570, 13571571075969, 28453406132296, 24729439859677, 8429189717024, 1019043094907, 36968589557, 0, 0] := by
  rw [show A10K2.u2410 = KTree.node A10K2.u2402 (nat_lit 41527464) (nat_lit 7370723861) (nat_lit 0) A10K2.u2409 from rfl, totK_node, atot2402, atot2409]
  decide +kernel

theorem arows2425 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2425 = true := by
  rw [show A10K2.u2425 = KTree.node A10K2.u2417 (nat_lit 41652726) (nat_lit 16395554551) (nat_lit 0) A10K2.u2424 from rfl, allE_node, arows2417, irow2425, arows2424]
  all_goals rfl

theorem atot2425 : totK PA10K2 A10K2.u2425 = [796021182214, 4268907216151, 12464203106943, 23868574580511, 24707052028693, 11174301540976, 1739629497956, 74789331576, 0, 0] := by
  rw [show A10K2.u2425 = KTree.node A10K2.u2417 (nat_lit 41652726) (nat_lit 16395554551) (nat_lit 0) A10K2.u2424 from rfl, totK_node, atot2417, atot2424]
  decide +kernel

theorem arows2443 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2443 = true := by
  rw [show A10K2.u2443 = KTree.node A10K2.u2435 (nat_lit 41979122) (nat_lit 10763397228) (nat_lit 0) A10K2.u2442 from rfl, allE_node, arows2435, irow2443, arows2442]
  all_goals rfl

theorem atot2443 : totK PA10K2 A10K2.u2443 = [2151350857276, 13063546941038, 27989633958631, 24679887540372, 8314123909018, 1000696730695, 36196801203, 0, 0, 0] := by
  rw [show A10K2.u2443 = KTree.node A10K2.u2435 (nat_lit 41979122) (nat_lit 10763397228) (nat_lit 0) A10K2.u2442 from rfl, totK_node, atot2435, atot2442]
  decide +kernel

theorem arows2458 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2458 = true := by
  rw [show A10K2.u2458 = KTree.node A10K2.u2450 (nat_lit 42123604) (nat_lit 13026333276) (nat_lit 0) A10K2.u2457 from rfl, allE_node, arows2450, irow2458, arows2457]
  all_goals rfl

theorem atot2458 : totK PA10K2 A10K2.u2458 = [1380631111097, 10308809965805, 26121710541363, 26904840574932, 10041375461065, 1203932244069, 37186156514, 0, 0, 0] := by
  rw [show A10K2.u2458 = KTree.node A10K2.u2450 (nat_lit 42123604) (nat_lit 13026333276) (nat_lit 0) A10K2.u2457 from rfl, totK_node, atot2450, atot2457]
  decide +kernel

theorem arows2474 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2474 = true := by
  rw [show A10K2.u2474 = KTree.node A10K2.u2466 (nat_lit 42262913) (nat_lit 10320576489) (nat_lit 0) A10K2.u2473 from rfl, allE_node, arows2466, irow2474, arows2473]
  all_goals rfl

theorem atot2474 : totK PA10K2 A10K2.u2474 = [0, 2739527338127, 14672443261841, 28195780592339, 22757172158324, 7277692136859, 924904139880, 36134558889, 0, 0] := by
  rw [show A10K2.u2474 = KTree.node A10K2.u2466 (nat_lit 42262913) (nat_lit 10320576489) (nat_lit 0) A10K2.u2473 from rfl, totK_node, atot2466, atot2473]
  decide +kernel

theorem arows2489 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2489 = true := by
  rw [show A10K2.u2489 = KTree.node A10K2.u2481 (nat_lit 42547973) (nat_lit 6907801568) (nat_lit 0) A10K2.u2488 from rfl, allE_node, arows2481, irow2489, arows2488]
  all_goals rfl

theorem atot2489 : totK PA10K2 A10K2.u2489 = [2298266100845, 11563958143065, 22584093427013, 23292901730311, 13769585459206, 3477952612646, 299638718703, 5676195732, 0, 0] := by
  rw [show A10K2.u2489 = KTree.node A10K2.u2481 (nat_lit 42547973) (nat_lit 6907801568) (nat_lit 0) A10K2.u2488 from rfl, totK_node, atot2481, atot2488]
  decide +kernel

theorem arows2506 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2506 = true := by
  rw [show A10K2.u2506 = KTree.node A10K2.u2498 (nat_lit 42610066) (nat_lit 15259374986) (nat_lit 0) A10K2.u2505 from rfl, allE_node, arows2498, irow2506, arows2505]
  all_goals rfl

theorem atot2506 : totK PA10K2 A10K2.u2506 = [2116282535288, 13056074753577, 28108603221276, 24529544365458, 7744647964480, 728002499569, 11638555097, 0, 0, 0] := by
  rw [show A10K2.u2506 = KTree.node A10K2.u2498 (nat_lit 42610066) (nat_lit 15259374986) (nat_lit 0) A10K2.u2505 from rfl, totK_node, atot2498, atot2505]
  decide +kernel

theorem arows2521 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2521 = true := by
  rw [show A10K2.u2521 = KTree.node A10K2.u2513 (nat_lit 42706304) (nat_lit 10450346447) (nat_lit 0) A10K2.u2520 from rfl, allE_node, arows2513, irow2521, arows2520]
  all_goals rfl

theorem atot2521 : totK PA10K2 A10K2.u2521 = [1609698614687, 10291658886470, 25227547008260, 27794609402557, 12754394289640, 2140836927081, 100246167478, 0, 0, 0] := by
  rw [show A10K2.u2521 = KTree.node A10K2.u2513 (nat_lit 42706304) (nat_lit 10450346447) (nat_lit 0) A10K2.u2520 from rfl, totK_node, atot2513, atot2520]
  decide +kernel

theorem arows2537 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2537 = true := by
  rw [show A10K2.u2537 = KTree.node A10K2.u2529 (nat_lit 42841821) (nat_lit 5441397718) (nat_lit 0) A10K2.u2536 from rfl, allE_node, arows2529, irow2537, arows2536]
  all_goals rfl

theorem atot2537 : totK PA10K2 A10K2.u2537 = [0, 2742697567505, 14690167461927, 28302571525017, 22975857511646, 7442564707586, 929820749761, 36704093874, 0, 0] := by
  rw [show A10K2.u2537 = KTree.node A10K2.u2529 (nat_lit 42841821) (nat_lit 5441397718) (nat_lit 0) A10K2.u2536 from rfl, totK_node, atot2529, atot2536]
  decide +kernel

theorem arows2552 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2552 = true := by
  rw [show A10K2.u2552 = KTree.node A10K2.u2544 (nat_lit 42912413) (nat_lit 5879602105) (nat_lit 0) A10K2.u2551 from rfl, allE_node, arows2544, irow2552, arows2551]
  all_goals rfl

theorem atot2552 : totK PA10K2 A10K2.u2552 = [444521281299, 3852732037996, 15459584641243, 28976719704845, 22531037333189, 5660459088381, 428131840815, 6239673734, 0, 0] := by
  rw [show A10K2.u2552 = KTree.node A10K2.u2544 (nat_lit 42912413) (nat_lit 5879602105) (nat_lit 0) A10K2.u2551 from rfl, totK_node, atot2544, atot2551]
  decide +kernel

theorem arows2572 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2572 = true := by
  rw [show A10K2.u2572 = KTree.node A10K2.u2564 (nat_lit 43030600) (nat_lit 13743670115) (nat_lit 0) A10K2.u2571 from rfl, allE_node, arows2564, irow2572, arows2571]
  all_goals rfl

theorem atot2572 : totK PA10K2 A10K2.u2572 = [2949135731706, 15074760324527, 27899351215829, 22360154140925, 7274522240200, 907620755298, 36196801203, 0, 0, 0] := by
  rw [show A10K2.u2572 = KTree.node A10K2.u2564 (nat_lit 43030600) (nat_lit 13743670115) (nat_lit 0) A10K2.u2571 from rfl, totK_node, atot2564, atot2571]
  decide +kernel

theorem arows2587 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2587 = true := by
  rw [show A10K2.u2587 = KTree.node A10K2.u2579 (nat_lit 43110753) (nat_lit 8876377978) (nat_lit 0) A10K2.u2586 from rfl, allE_node, arows2579, irow2587, arows2586]
  all_goals rfl

theorem atot2587 : totK PA10K2 A10K2.u2587 = [2231167093449, 13203154776364, 27778999674271, 24261707552487, 8480914808870, 1043844883300, 37204059898, 0, 0, 0] := by
  rw [show A10K2.u2587 = KTree.node A10K2.u2579 (nat_lit 43110753) (nat_lit 8876377978) (nat_lit 0) A10K2.u2586 from rfl, totK_node, atot2579, atot2586]
  decide +kernel

theorem arows2603 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2603 = true := by
  rw [show A10K2.u2603 = KTree.node A10K2.u2595 (nat_lit 43253811) (nat_lit 4034786930) (nat_lit 0) A10K2.u2602 from rfl, allE_node, arows2595, irow2603, arows2602]
  all_goals rfl

theorem atot2603 : totK PA10K2 A10K2.u2603 = [568096137437, 7865239189167, 25086116725000, 29049329544335, 11837007406889, 1597776394836, 50380680131, 0, 0, 0] := by
  rw [show A10K2.u2603 = KTree.node A10K2.u2595 (nat_lit 43253811) (nat_lit 4034786930) (nat_lit 0) A10K2.u2602 from rfl, totK_node, atot2595, atot2602]
  decide +kernel

theorem arows2618 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2618 = true := by
  rw [show A10K2.u2618 = KTree.node A10K2.u2610 (nat_lit 43391010) (nat_lit 8448699946) (nat_lit 0) A10K2.u2617 from rfl, allE_node, arows2610, irow2618, arows2617]
  all_goals rfl

theorem atot2618 : totK PA10K2 A10K2.u2618 = [0, 3573850966553, 18463156107946, 31537755593927, 18830226332652, 3302891294433, 163220199286, 0, 0, 0] := by
  rw [show A10K2.u2618 = KTree.node A10K2.u2610 (nat_lit 43391010) (nat_lit 8448699946) (nat_lit 0) A10K2.u2617 from rfl, totK_node, atot2610, atot2617]
  decide +kernel

theorem arows2635 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2635 = true := by
  rw [show A10K2.u2635 = KTree.node A10K2.u2627 (nat_lit 44059283) (nat_lit 10411323981) (nat_lit 0) A10K2.u2634 from rfl, allE_node, arows2627, irow2635, arows2634]
  all_goals rfl

theorem atot2635 : totK PA10K2 A10K2.u2635 = [0, 2178457473183, 12978785931398, 27730363463818, 24300505980291, 8005703772205, 1017772788910, 37004978858, 0, 0] := by
  rw [show A10K2.u2635 = KTree.node A10K2.u2627 (nat_lit 44059283) (nat_lit 10411323981) (nat_lit 0) A10K2.u2634 from rfl, totK_node, atot2627, atot2634]
  decide +kernel

theorem arows2650 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2650 = true := by
  rw [show A10K2.u2650 = KTree.node A10K2.u2642 (nat_lit 44189142) (nat_lit 9132676779) (nat_lit 0) A10K2.u2649 from rfl, allE_node, arows2642, irow2650, arows2649]
  all_goals rfl

theorem atot2650 : totK PA10K2 A10K2.u2650 = [0, 2624305014753, 14108527533466, 28107608023322, 23593377343585, 7129357434865, 704257403875, 11900787601, 0, 0] := by
  rw [show A10K2.u2650 = KTree.node A10K2.u2642 (nat_lit 44189142) (nat_lit 9132676779) (nat_lit 0) A10K2.u2649 from rfl, totK_node, atot2642, atot2649]
  decide +kernel

theorem arows2666 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2666 = true := by
  rw [show A10K2.u2666 = KTree.node A10K2.u2658 (nat_lit 44672471) (nat_lit 14127503837) (nat_lit 0) A10K2.u2665 from rfl, allE_node, arows2658, irow2666, arows2665]
  all_goals rfl

theorem atot2666 : totK PA10K2 A10K2.u2666 = [0, 2332763962641, 13635263270305, 27993751450097, 24301725381178, 8268597195589, 993502866590, 37204059898, 0, 0] := by
  rw [show A10K2.u2666 = KTree.node A10K2.u2658 (nat_lit 44672471) (nat_lit 14127503837) (nat_lit 0) A10K2.u2665 from rfl, totK_node, atot2658, atot2665]
  decide +kernel

theorem arows2681 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2681 = true := by
  rw [show A10K2.u2681 = KTree.node A10K2.u2673 (nat_lit 44738561) (nat_lit 9983667354) (nat_lit 0) A10K2.u2680 from rfl, allE_node, arows2673, irow2681, arows2680]
  all_goals rfl

theorem atot2681 : totK PA10K2 A10K2.u2681 = [0, 3209429055636, 16450052979749, 29850786644825, 21787019397507, 5491584046102, 467349572028, 6354482628, 0, 0] := by
  rw [show A10K2.u2681 = KTree.node A10K2.u2673 (nat_lit 44738561) (nat_lit 9983667354) (nat_lit 0) A10K2.u2680 from rfl, totK_node, atot2673, atot2680]
  decide +kernel

theorem arows2699 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2699 = true := by
  rw [show A10K2.u2699 = KTree.node A10K2.u2691 (nat_lit 45094921) (nat_lit 9782390168) (nat_lit 0) A10K2.u2698 from rfl, allE_node, arows2691, irow2699, arows2698]
  all_goals rfl

theorem atot2699 : totK PA10K2 A10K2.u2699 = [0, 1806013987253, 12094019612864, 27971025255790, 26099664174912, 8886967853548, 1007201405828, 37267903822, 0, 0] := by
  rw [show A10K2.u2699 = KTree.node A10K2.u2691 (nat_lit 45094921) (nat_lit 9782390168) (nat_lit 0) A10K2.u2698 from rfl, totK_node, atot2691, atot2698]
  decide +kernel

theorem arows2714 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2714 = true := by
  rw [show A10K2.u2714 = KTree.node A10K2.u2706 (nat_lit 45180402) (nat_lit 14258420018) (nat_lit 0) A10K2.u2713 from rfl, allE_node, arows2706, irow2714, arows2713]
  all_goals rfl

theorem atot2714 : totK PA10K2 A10K2.u2714 = [0, 2259642262525, 12762184410862, 27312856610161, 25151994081651, 8575288581037, 1027231530388, 42315302678, 0, 0] := by
  rw [show A10K2.u2714 = KTree.node A10K2.u2706 (nat_lit 45180402) (nat_lit 14258420018) (nat_lit 0) A10K2.u2713 from rfl, totK_node, atot2706, atot2713]
  decide +kernel

theorem arows2730 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2730 = true := by
  rw [show A10K2.u2730 = KTree.node A10K2.u2722 (nat_lit 45242722) (nat_lit 12517783050) (nat_lit 0) A10K2.u2729 from rfl, allE_node, arows2722, irow2730, arows2729]
  all_goals rfl

theorem atot2730 : totK PA10K2 A10K2.u2730 = [0, 2129015206400, 13292701684281, 28309200133610, 23815399395920, 6941325968647, 778744836934, 31296045761, 0, 0] := by
  rw [show A10K2.u2730 = KTree.node A10K2.u2722 (nat_lit 45242722) (nat_lit 12517783050) (nat_lit 0) A10K2.u2729 from rfl, totK_node, atot2722, atot2729]
  decide +kernel

theorem arows2745 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2745 = true := by
  rw [show A10K2.u2745 = KTree.node A10K2.u2737 (nat_lit 45435398) (nat_lit 7952075887) (nat_lit 0) A10K2.u2744 from rfl, allE_node, arows2737, irow2745, arows2744]
  all_goals rfl

theorem atot2745 : totK PA10K2 A10K2.u2745 = [0, 0, 4832622510845, 21622331134754, 31347534999517, 15147932865033, 2374694773087, 110251991019, 0, 0] := by
  rw [show A10K2.u2745 = KTree.node A10K2.u2737 (nat_lit 45435398) (nat_lit 7952075887) (nat_lit 0) A10K2.u2744 from rfl, totK_node, atot2737, atot2744]
  decide +kernel

theorem arows2762 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2762 = true := by
  rw [show A10K2.u2762 = KTree.node A10K2.u2754 (nat_lit 46138221) (nat_lit 5410436237) (nat_lit 0) A10K2.u2761 from rfl, allE_node, arows2754, irow2762, arows2761]
  all_goals rfl

theorem atot2762 : totK PA10K2 A10K2.u2762 = [2205856923078, 10582187235983, 17622395083353, 15418382249550, 15108994026105, 11415658992124, 3525851668675, 384962563863, 6354482628, 0] := by
  rw [show A10K2.u2762 = KTree.node A10K2.u2754 (nat_lit 46138221) (nat_lit 5410436237) (nat_lit 0) A10K2.u2761 from rfl, totK_node, atot2754, atot2761]
  decide +kernel

theorem arows2777 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2777 = true := by
  rw [show A10K2.u2777 = KTree.node A10K2.u2769 (nat_lit 46338451) (nat_lit 5910231096) (nat_lit 0) A10K2.u2776 from rfl, allE_node, arows2769, irow2777, arows2776]
  all_goals rfl

theorem atot2777 : totK PA10K2 A10K2.u2777 = [2245249553523, 13152295657793, 28111464572130, 25512911267199, 8799112976365, 1034517132136, 36196801203, 0, 0, 0] := by
  rw [show A10K2.u2777 = KTree.node A10K2.u2769 (nat_lit 46338451) (nat_lit 5910231096) (nat_lit 0) A10K2.u2776 from rfl, totK_node, atot2769, atot2776]
  decide +kernel

theorem arows2793 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2793 = true := by
  rw [show A10K2.u2793 = KTree.node A10K2.u2785 (nat_lit 46402737) (nat_lit 6872407935) (nat_lit 0) A10K2.u2792 from rfl, allE_node, arows2785, irow2793, arows2792]
  all_goals rfl

theorem atot2793 : totK PA10K2 A10K2.u2793 = [0, 3665329433608, 18747127781399, 32188622753254, 20148534670876, 3789163036129, 177852359017, 0, 0, 0] := by
  rw [show A10K2.u2793 = KTree.node A10K2.u2785 (nat_lit 46402737) (nat_lit 6872407935) (nat_lit 0) A10K2.u2792 from rfl, totK_node, atot2785, atot2792]
  decide +kernel

theorem arows2808 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2808 = true := by
  rw [show A10K2.u2808 = KTree.node A10K2.u2800 (nat_lit 46606014) (nat_lit 15268314887) (nat_lit 0) A10K2.u2807 from rfl, allE_node, arows2800, irow2808, arows2807]
  all_goals rfl

theorem atot2808 : totK PA10K2 A10K2.u2808 = [861896674927, 5995875675437, 17463722068407, 26376036855280, 20083442119806, 6733040278565, 899871324471, 36134558889, 0, 0] := by
  rw [show A10K2.u2808 = KTree.node A10K2.u2800 (nat_lit 46606014) (nat_lit 15268314887) (nat_lit 0) A10K2.u2807 from rfl, totK_node, atot2800, atot2807]
  decide +kernel

theorem arows2827 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2827 = true := by
  rw [show A10K2.u2827 = KTree.node A10K2.u2819 (nat_lit 46774125) (nat_lit 5234365043) (nat_lit 0) A10K2.u2826 from rfl, allE_node, arows2819, irow2827, arows2826]
  all_goals rfl

theorem atot2827 : totK PA10K2 A10K2.u2827 = [2523184633352, 13839878672149, 27944735398804, 24459022059283, 8577208558408, 1034531659286, 37204059898, 0, 0, 0] := by
  rw [show A10K2.u2827 = KTree.node A10K2.u2819 (nat_lit 46774125) (nat_lit 5234365043) (nat_lit 0) A10K2.u2826 from rfl, totK_node, atot2819, atot2826]
  decide +kernel

theorem arows2842 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2842 = true := by
  rw [show A10K2.u2842 = KTree.node A10K2.u2834 (nat_lit 46865854) (nat_lit 16420244646) (nat_lit 0) A10K2.u2841 from rfl, allE_node, arows2834, irow2842, arows2841]
  all_goals rfl

theorem atot2842 : totK PA10K2 A10K2.u2842 = [2682443249882, 15062681228710, 29596929111152, 23587875139384, 6880450471335, 635846350833, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u2842 = KTree.node A10K2.u2834 (nat_lit 46865854) (nat_lit 16420244646) (nat_lit 0) A10K2.u2841 from rfl, totK_node, atot2834, atot2841]
  decide +kernel

theorem arows2858 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2858 = true := by
  rw [show A10K2.u2858 = KTree.node A10K2.u2850 (nat_lit 47001144) (nat_lit 12152398256) (nat_lit 0) A10K2.u2857 from rfl, allE_node, arows2850, irow2858, arows2857]
  all_goals rfl

theorem atot2858 : totK PA10K2 A10K2.u2858 = [0, 3969520341378, 19351668809166, 31900859142255, 19581275975047, 3747382765741, 180612111745, 0, 0, 0] := by
  rw [show A10K2.u2858 = KTree.node A10K2.u2850 (nat_lit 47001144) (nat_lit 12152398256) (nat_lit 0) A10K2.u2857 from rfl, totK_node, atot2850, atot2857]
  decide +kernel

theorem arows2873 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2873 = true := by
  rw [show A10K2.u2873 = KTree.node A10K2.u2865 (nat_lit 47069736) (nat_lit 9957624774) (nat_lit 0) A10K2.u2872 from rfl, allE_node, arows2865, irow2873, arows2872]
  all_goals rfl

theorem atot2873 : totK PA10K2 A10K2.u2873 = [0, 2094727372423, 12433287768916, 27003887504626, 25229626911086, 9084836774722, 1167500284533, 42943767608, 0, 0] := by
  rw [show A10K2.u2873 = KTree.node A10K2.u2865 (nat_lit 47069736) (nat_lit 9957624774) (nat_lit 0) A10K2.u2872 from rfl, totK_node, atot2865, atot2872]
  decide +kernel

theorem arows2890 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2890 = true := by
  rw [show A10K2.u2890 = KTree.node A10K2.u2882 (nat_lit 47712621) (nat_lit 6396598253) (nat_lit 0) A10K2.u2889 from rfl, allE_node, arows2882, irow2890, arows2889]
  all_goals rfl

theorem atot2890 : totK PA10K2 A10K2.u2890 = [1870719184046, 11163502766219, 25360987323988, 26495390916277, 12315943050005, 2153089751820, 100675502142, 0, 0, 0] := by
  rw [show A10K2.u2890 = KTree.node A10K2.u2882 (nat_lit 47712621) (nat_lit 6396598253) (nat_lit 0) A10K2.u2889 from rfl, totK_node, atot2882, atot2889]
  decide +kernel

theorem arows2905 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2905 = true := by
  rw [show A10K2.u2905 = KTree.node A10K2.u2897 (nat_lit 47799072) (nat_lit 11143483996) (nat_lit 0) A10K2.u2904 from rfl, allE_node, arows2897, irow2905, arows2904]
  all_goals rfl

theorem atot2905 : totK PA10K2 A10K2.u2905 = [2133734795744, 12431908685917, 26706142632901, 25572860481008, 10252858749014, 1525953395468, 67854556128, 0, 0, 0] := by
  rw [show A10K2.u2905 = KTree.node A10K2.u2897 (nat_lit 47799072) (nat_lit 11143483996) (nat_lit 0) A10K2.u2904 from rfl, totK_node, atot2897, atot2904]
  decide +kernel

theorem arows2921 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2921 = true := by
  rw [show A10K2.u2921 = KTree.node A10K2.u2913 (nat_lit 47932912) (nat_lit 12998789637) (nat_lit 0) A10K2.u2920 from rfl, allE_node, arows2913, irow2921, arows2920]
  all_goals rfl

theorem atot2921 : totK PA10K2 A10K2.u2921 = [2389005205952, 13540979739778, 28138174340270, 25045323143989, 8718287473096, 919912485082, 13951953716, 0, 0, 0] := by
  rw [show A10K2.u2921 = KTree.node A10K2.u2913 (nat_lit 47932912) (nat_lit 12998789637) (nat_lit 0) A10K2.u2920 from rfl, totK_node, atot2913, atot2920]
  decide +kernel

theorem arows2936 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2936 = true := by
  rw [show A10K2.u2936 = KTree.node A10K2.u2928 (nat_lit 47998902) (nat_lit 16799536538) (nat_lit 0) A10K2.u2935 from rfl, allE_node, arows2928, irow2936, arows2935]
  all_goals rfl

theorem atot2936 : totK PA10K2 A10K2.u2936 = [0, 3122325397676, 16267920823242, 29989646252878, 22791987713365, 6390919872405, 556742732595, 7007974415, 0, 0] := by
  rw [show A10K2.u2936 = KTree.node A10K2.u2928 (nat_lit 47998902) (nat_lit 16799536538) (nat_lit 0) A10K2.u2935 from rfl, totK_node, atot2928, atot2935]
  decide +kernel

theorem arows2954 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2954 = true := by
  rw [show A10K2.u2954 = KTree.node A10K2.u2946 (nat_lit 48082035) (nat_lit 6200441575) (nat_lit 0) A10K2.u2953 from rfl, allE_node, arows2946, irow2954, arows2953]
  all_goals rfl

theorem atot2954 : totK PA10K2 A10K2.u2954 = [0, 3101173874047, 16288043986803, 30115325545936, 22752821298773, 6290715831305, 522761192934, 7151180950, 0, 0] := by
  rw [show A10K2.u2954 = KTree.node A10K2.u2946 (nat_lit 48082035) (nat_lit 6200441575) (nat_lit 0) A10K2.u2953 from rfl, totK_node, atot2946, atot2953]
  decide +kernel

theorem arows2969 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2969 = true := by
  rw [show A10K2.u2969 = KTree.node A10K2.u2961 (nat_lit 48212259) (nat_lit 10160992118) (nat_lit 0) A10K2.u2968 from rfl, allE_node, arows2961, irow2969, arows2968]
  all_goals rfl

theorem atot2969 : totK PA10K2 A10K2.u2969 = [0, 1736062256800, 11109125283939, 26068082711858, 26655630826071, 11217351968133, 1663203689811, 73776485728, 0, 0] := by
  rw [show A10K2.u2969 = KTree.node A10K2.u2961 (nat_lit 48212259) (nat_lit 10160992118) (nat_lit 0) A10K2.u2968 from rfl, totK_node, atot2961, atot2968]
  decide +kernel

theorem arows2985 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2985 = true := by
  rw [show A10K2.u2985 = KTree.node A10K2.u2977 (nat_lit 48274177) (nat_lit 10111568244) (nat_lit 0) A10K2.u2984 from rfl, allE_node, arows2977, irow2985, arows2984]
  all_goals rfl

theorem atot2985 : totK PA10K2 A10K2.u2985 = [0, 2739649106732, 14665601061710, 28516109875212, 23660034611329, 7871224439718, 974655694483, 36196801203, 0, 0] := by
  rw [show A10K2.u2985 = KTree.node A10K2.u2977 (nat_lit 48274177) (nat_lit 10111568244) (nat_lit 0) A10K2.u2984 from rfl, totK_node, atot2977, atot2984]
  decide +kernel

theorem arows3000 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3000 = true := by
  rw [show A10K2.u3000 = KTree.node A10K2.u2992 (nat_lit 48476037) (nat_lit 1566849094) (nat_lit 0) A10K2.u2999 from rfl, allE_node, arows2992, irow3000, arows2999]
  all_goals rfl

theorem atot3000 : totK PA10K2 A10K2.u3000 = [0, 866737529530, 7910216141893, 23711809391856, 29476136805506, 14619331142975, 2361440042239, 105613083658, 0, 0] := by
  rw [show A10K2.u3000 = KTree.node A10K2.u2992 (nat_lit 48476037) (nat_lit 1566849094) (nat_lit 0) A10K2.u2999 from rfl, totK_node, atot2992, atot2999]
  decide +kernel

theorem arows3017 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3017 = true := by
  rw [show A10K2.u3017 = KTree.node A10K2.u3009 (nat_lit 48548620) (nat_lit 11924970024) (nat_lit 0) A10K2.u3016 from rfl, allE_node, arows3009, irow3017, arows3016]
  all_goals rfl

theorem atot3017 : totK PA10K2 A10K2.u3017 = [0, 0, 3314189817224, 17230046807503, 30786290290723, 21495108124218, 5272010859874, 454107563793, 7237400819, 0] := by
  rw [show A10K2.u3017 = KTree.node A10K2.u3009 (nat_lit 48548620) (nat_lit 11924970024) (nat_lit 0) A10K2.u3016 from rfl, totK_node, atot3009, atot3016]
  decide +kernel

theorem arows3032 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3032 = true := by
  rw [show A10K2.u3032 = KTree.node A10K2.u3024 (nat_lit 48852150) (nat_lit 16606316129) (nat_lit 0) A10K2.u3031 from rfl, allE_node, arows3024, irow3032, arows3031]
  all_goals rfl

theorem atot3032 : totK PA10K2 A10K2.u3032 = [0, 2305653685916, 12733223871607, 26097491149503, 24392177903335, 10585197003221, 1878736142330, 99337152506, 0, 0] := by
  rw [show A10K2.u3032 = KTree.node A10K2.u3024 (nat_lit 48852150) (nat_lit 16606316129) (nat_lit 0) A10K2.u3031 from rfl, totK_node, atot3024, atot3031]
  decide +kernel

theorem arows3048 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3048 = true := by
  rw [show A10K2.u3048 = KTree.node A10K2.u3040 (nat_lit 48939073) (nat_lit 10388325720) (nat_lit 0) A10K2.u3047 from rfl, allE_node, arows3040, irow3048, arows3047]
  all_goals rfl

theorem atot3048 : totK PA10K2 A10K2.u3048 = [0, 3389485948133, 16836226829007, 29923777382110, 21862735801015, 5650829224791, 443129673143, 6354482628, 0, 0] := by
  rw [show A10K2.u3048 = KTree.node A10K2.u3040 (nat_lit 48939073) (nat_lit 10388325720) (nat_lit 0) A10K2.u3047 from rfl, totK_node, atot3040, atot3047]
  decide +kernel

theorem arows3063 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3063 = true := by
  rw [show A10K2.u3063 = KTree.node A10K2.u3055 (nat_lit 49014043) (nat_lit 9986927230) (nat_lit 0) A10K2.u3062 from rfl, allE_node, arows3055, irow3063, arows3062]
  all_goals rfl

theorem atot3063 : totK PA10K2 A10K2.u3063 = [0, 359360087617, 6279432269851, 22692245653810, 30691853513044, 15881446363818, 2575243447486, 112315173847, 0, 0] := by
  rw [show A10K2.u3063 = KTree.node A10K2.u3055 (nat_lit 49014043) (nat_lit 9986927230) (nat_lit 0) A10K2.u3062 from rfl, totK_node, atot3055, atot3062]
  decide +kernel

theorem arows3084 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3084 = true := by
  rw [show A10K2.u3084 = KTree.node A10K2.u3076 (nat_lit 49147549) (nat_lit 4701889235) (nat_lit 0) A10K2.u3083 from rfl, allE_node, arows3076, irow3084, arows3083]
  all_goals rfl

theorem atot3084 : totK PA10K2 A10K2.u3084 = [0, 0, 3672198089267, 18040110198300, 30662648000374, 20558773109209, 5125837290376, 446373589919, 7380853412, 0] := by
  rw [show A10K2.u3084 = KTree.node A10K2.u3076 (nat_lit 49147549) (nat_lit 4701889235) (nat_lit 0) A10K2.u3083 from rfl, totK_node, atot3076, atot3083]
  decide +kernel

theorem arows3099 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3099 = true := by
  rw [show A10K2.u3099 = KTree.node A10K2.u3091 (nat_lit 49828108) (nat_lit 11990601799) (nat_lit 0) A10K2.u3098 from rfl, allE_node, arows3091, irow3099, arows3098]
  all_goals rfl

theorem atot3099 : totK PA10K2 A10K2.u3099 = [0, 1870719184046, 11232243250497, 25339717713368, 26297429564939, 12221438129521, 2069033250988, 87551697294, 0, 0] := by
  rw [show A10K2.u3099 = KTree.node A10K2.u3091 (nat_lit 49828108) (nat_lit 11990601799) (nat_lit 0) A10K2.u3098 from rfl, totK_node, atot3091, atot3098]
  decide +kernel

theorem arows3115 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3115 = true := by
  rw [show A10K2.u3115 = KTree.node A10K2.u3107 (nat_lit 49905050) (nat_lit 14487834767) (nat_lit 0) A10K2.u3114 from rfl, allE_node, arows3107, irow3115, arows3114]
  all_goals rfl

theorem atot3115 : totK PA10K2 A10K2.u3115 = [0, 2859684104075, 15022636859574, 28724759425858, 23802949029356, 7818586905101, 770773184045, 12696458652, 0, 0] := by
  rw [show A10K2.u3115 = KTree.node A10K2.u3107 (nat_lit 49905050) (nat_lit 14487834767) (nat_lit 0) A10K2.u3114 from rfl, totK_node, atot3107, atot3114]
  decide +kernel

theorem arows3130 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3130 = true := by
  rw [show A10K2.u3130 = KTree.node A10K2.u3122 (nat_lit 50037518) (nat_lit 10254947295) (nat_lit 0) A10K2.u3129 from rfl, allE_node, arows3122, irow3130, arows3129]
  all_goals rfl

theorem atot3130 : totK PA10K2 A10K2.u3130 = [0, 1663055897621, 10813807092406, 25915150971203, 27043241714761, 11581734511799, 1525369854747, 37751669437, 0, 0] := by
  rw [show A10K2.u3130 = KTree.node A10K2.u3122 (nat_lit 50037518) (nat_lit 10254947295) (nat_lit 0) A10K2.u3129 from rfl, totK_node, atot3122, atot3129]
  decide +kernel

theorem arows3147 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3147 = true := by
  rw [show A10K2.u3147 = KTree.node A10K2.u3139 (nat_lit 50105440) (nat_lit 13857200976) (nat_lit 0) A10K2.u3146 from rfl, allE_node, arows3139, irow3147, arows3146]
  all_goals rfl

theorem atot3147 : totK PA10K2 A10K2.u3147 = [0, 0, 3383362457903, 17126584013208, 30414581808467, 22046133315925, 5628094104960, 436805433957, 6725424603, 0] := by
  rw [show A10K2.u3147 = KTree.node A10K2.u3139 (nat_lit 50105440) (nat_lit 13857200976) (nat_lit 0) A10K2.u3146 from rfl, totK_node, atot3139, atot3146]
  decide +kernel

theorem arows3162 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3162 = true := by
  rw [show A10K2.u3162 = KTree.node A10K2.u3154 (nat_lit 50266976) (nat_lit 12641673887) (nat_lit 0) A10K2.u3161 from rfl, allE_node, arows3154, irow3162, arows3161]
  all_goals rfl

theorem atot3162 : totK PA10K2 A10K2.u3162 = [0, 0, 2991420278188, 16283989510790, 30650369375229, 22973140087390, 5735915378292, 422948397847, 6860445330, 0] := by
  rw [show A10K2.u3162 = KTree.node A10K2.u3154 (nat_lit 50266976) (nat_lit 12641673887) (nat_lit 0) A10K2.u3161 from rfl, totK_node, atot3154, atot3161]
  decide +kernel

theorem arows3178 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3178 = true := by
  rw [show A10K2.u3178 = KTree.node A10K2.u3170 (nat_lit 50330835) (nat_lit 10248088735) (nat_lit 0) A10K2.u3177 from rfl, allE_node, arows3170, irow3178, arows3177]
  all_goals rfl

theorem atot3178 : totK PA10K2 A10K2.u3178 = [0, 2384474177162, 10498227139435, 17331271136456, 18418548995767, 18180657222874, 9337402407864, 1602520676930, 73776485728, 0] := by
  rw [show A10K2.u3178 = KTree.node A10K2.u3170 (nat_lit 50330835) (nat_lit 10248088735) (nat_lit 0) A10K2.u3177 from rfl, totK_node, atot3170, atot3177]
  decide +kernel

theorem arows3193 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3193 = true := by
  rw [show A10K2.u3193 = KTree.node A10K2.u3185 (nat_lit 55176349) (nat_lit 5257101777) (nat_lit 0) A10K2.u3192 from rfl, allE_node, arows3185, irow3193, arows3192]
  all_goals rfl

theorem atot3193 : totK PA10K2 A10K2.u3193 = [0, 2002693624572, 12389418726550, 27185741757465, 24984408118195, 8783803634999, 1032793763987, 37204059898, 0, 0] := by
  rw [show A10K2.u3193 = KTree.node A10K2.u3185 (nat_lit 55176349) (nat_lit 5257101777) (nat_lit 0) A10K2.u3192 from rfl, totK_node, atot3185, atot3192]
  decide +kernel

theorem arows3211 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3211 = true := by
  rw [show A10K2.u3211 = KTree.node A10K2.u3203 (nat_lit 55259012) (nat_lit 4120559007) (nat_lit 0) A10K2.u3210 from rfl, allE_node, arows3203, irow3211, arows3210]
  all_goals rfl

theorem atot3211 : totK PA10K2 A10K2.u3211 = [0, 2130627667087, 13117856877992, 28919676685022, 25959949383063, 7954508087751, 643774866750, 6354482628, 0, 0] := by
  rw [show A10K2.u3211 = KTree.node A10K2.u3203 (nat_lit 55259012) (nat_lit 4120559007) (nat_lit 0) A10K2.u3210 from rfl, totK_node, atot3203, atot3210]
  decide +kernel

theorem arows3226 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3226 = true := by
  rw [show A10K2.u3226 = KTree.node A10K2.u3218 (nat_lit 55395549) (nat_lit 5699812192) (nat_lit 0) A10K2.u3225 from rfl, allE_node, arows3218, irow3226, arows3225]
  all_goals rfl

theorem atot3226 : totK PA10K2 A10K2.u3226 = [0, 0, 3216553817196, 16645897214383, 29895646914917, 21439296167666, 5923450744133, 698251844780, 31018567651, 0] := by
  rw [show A10K2.u3226 = KTree.node A10K2.u3218 (nat_lit 55395549) (nat_lit 5699812192) (nat_lit 0) A10K2.u3225 from rfl, totK_node, atot3218, atot3225]
  decide +kernel

theorem arows3242 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3242 = true := by
  rw [show A10K2.u3242 = KTree.node A10K2.u3234 (nat_lit 55458604) (nat_lit 13345843118) (nat_lit 0) A10K2.u3241 from rfl, allE_node, arows3234, irow3242, arows3241]
  all_goals rfl

theorem atot3242 : totK PA10K2 A10K2.u3242 = [0, 0, 2190077877386, 13214967069220, 28143334554098, 23957192554186, 6869965106989, 646326321433, 11925199957, 0] := by
  rw [show A10K2.u3242 = KTree.node A10K2.u3234 (nat_lit 55458604) (nat_lit 13345843118) (nat_lit 0) A10K2.u3241 from rfl, totK_node, atot3234, atot3241]
  decide +kernel

theorem arows3257 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3257 = true := by
  rw [show A10K2.u3257 = KTree.node A10K2.u3249 (nat_lit 55575053) (nat_lit 5624688965) (nat_lit 0) A10K2.u3256 from rfl, allE_node, arows3249, irow3257, arows3256]
  all_goals rfl

theorem atot3257 : totK PA10K2 A10K2.u3257 = [0, 1616645945202, 10269824459927, 24683846786307, 26738503936479, 12455502483083, 2074379843969, 85303692204, 0, 0] := by
  rw [show A10K2.u3257 = KTree.node A10K2.u3249 (nat_lit 55575053) (nat_lit 5624688965) (nat_lit 0) A10K2.u3256 from rfl, totK_node, atot3249, atot3256]
  decide +kernel

theorem arows3274 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3274 = true := by
  rw [show A10K2.u3274 = KTree.node A10K2.u3266 (nat_lit 55682725) (nat_lit 6930083950) (nat_lit 0) A10K2.u3273 from rfl, allE_node, arows3266, irow3274, arows3273]
  all_goals rfl

theorem atot3274 : totK PA10K2 A10K2.u3274 = [0, 2462762608142, 13738160719881, 27602326481587, 23854877333281, 8438864563654, 1030673108655, 37204059898, 0, 0] := by
  rw [show A10K2.u3274 = KTree.node A10K2.u3266 (nat_lit 55682725) (nat_lit 6930083950) (nat_lit 0) A10K2.u3273 from rfl, totK_node, atot3266, atot3273]
  decide +kernel

theorem arows3289 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3289 = true := by
  rw [show A10K2.u3289 = KTree.node A10K2.u3281 (nat_lit 55748370) (nat_lit 15163172844) (nat_lit 0) A10K2.u3288 from rfl, allE_node, arows3281, irow3289, arows3288]
  all_goals rfl

theorem atot3289 : totK PA10K2 A10K2.u3289 = [0, 1591323679956, 11181882845964, 27108401738811, 26186348764195, 8573377651293, 848961984406, 11801668502, 0, 0] := by
  rw [show A10K2.u3289 = KTree.node A10K2.u3281 (nat_lit 55748370) (nat_lit 15163172844) (nat_lit 0) A10K2.u3288 from rfl, totK_node, atot3281, atot3288]
  decide +kernel

theorem arows3305 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3305 = true := by
  rw [show A10K2.u3305 = KTree.node A10K2.u3297 (nat_lit 55967859) (nat_lit 13652359) (nat_lit 8) A10K2.u3304 from rfl, allE_node, arows3297, irow3305, arows3304]
  all_goals rfl

theorem atot3305 : totK PA10K2 A10K2.u3305 = [0, 0, 4368323519491, 20582914036931, 31840227656741, 16756768566131, 2574985432087, 99328694161, 0, 0] := by
  rw [show A10K2.u3305 = KTree.node A10K2.u3297 (nat_lit 55967859) (nat_lit 13652359) (nat_lit 8) A10K2.u3304 from rfl, totK_node, atot3297, atot3304]
  decide +kernel

theorem arows3320 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3320 = true := by
  rw [show A10K2.u3320 = KTree.node A10K2.u3312 (nat_lit 56127483) (nat_lit 6009720723) (nat_lit 0) A10K2.u3319 from rfl, allE_node, arows3312, irow3320, arows3319]
  all_goals rfl

theorem atot3320 : totK PA10K2 A10K2.u3320 = [0, 2233135491413, 11699666425081, 23771438070939, 24419298482323, 13184540623726, 3159658654866, 295553588414, 6354482628, 0] := by
  rw [show A10K2.u3320 = KTree.node A10K2.u3312 (nat_lit 56127483) (nat_lit 6009720723) (nat_lit 0) A10K2.u3319 from rfl, totK_node, atot3312, atot3319]
  decide +kernel

theorem arows3339 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3339 = true := by
  rw [show A10K2.u3339 = KTree.node A10K2.u3331 (nat_lit 56212224) (nat_lit 7960183284) (nat_lit 0) A10K2.u3338 from rfl, allE_node, arows3331, irow3339, arows3338]
  all_goals rfl

theorem atot3339 : totK PA10K2 A10K2.u3339 = [0, 2782753928909, 14842448174597, 28579264148866, 23663179058550, 8042382473799, 994098037389, 37204059898, 0, 0] := by
  rw [show A10K2.u3339 = KTree.node A10K2.u3331 (nat_lit 56212224) (nat_lit 7960183284) (nat_lit 0) A10K2.u3338 from rfl, totK_node, atot3331, atot3338]
  decide +kernel

theorem arows3354 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3354 = true := by
  rw [show A10K2.u3354 = KTree.node A10K2.u3346 (nat_lit 56340147) (nat_lit 10143942411) (nat_lit 0) A10K2.u3353 from rfl, allE_node, arows3346, irow3354, arows3353]
  all_goals rfl

theorem atot3354 : totK PA10K2 A10K2.u3354 = [0, 873803232168, 8229087559056, 24725830665871, 29964169409596, 13930807495514, 2105671167408, 82965252042, 0, 0] := by
  rw [show A10K2.u3354 = KTree.node A10K2.u3346 (nat_lit 56340147) (nat_lit 10143942411) (nat_lit 0) A10K2.u3353 from rfl, totK_node, atot3346, atot3353]
  decide +kernel

theorem arows3370 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3370 = true := by
  rw [show A10K2.u3370 = KTree.node A10K2.u3362 (nat_lit 56445189) (nat_lit 7040787894) (nat_lit 0) A10K2.u3369 from rfl, allE_node, arows3362, irow3370, arows3369]
  all_goals rfl

theorem atot3370 : totK PA10K2 A10K2.u3370 = [0, 0, 2218744156994, 14286539406357, 30470752194672, 24976389024389, 6913524332462, 562672166844, 7151180950, 0] := by
  rw [show A10K2.u3370 = KTree.node A10K2.u3362 (nat_lit 56445189) (nat_lit 7040787894) (nat_lit 0) A10K2.u3369 from rfl, totK_node, atot3362, atot3369]
  decide +kernel

theorem arows3385 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3385 = true := by
  rw [show A10K2.u3385 = KTree.node A10K2.u3377 (nat_lit 56585954) (nat_lit 12874899280) (nat_lit 0) A10K2.u3384 from rfl, allE_node, arows3377, irow3385, arows3384]
  all_goals rfl

theorem atot3385 : totK PA10K2 A10K2.u3385 = [0, 0, 2283220196760, 13547092208617, 29222121315274, 26122170915942, 8348527584076, 665594754934, 6439430839, 0] := by
  rw [show A10K2.u3385 = KTree.node A10K2.u3377 (nat_lit 56585954) (nat_lit 12874899280) (nat_lit 0) A10K2.u3384 from rfl, totK_node, atot3377, atot3384]
  decide +kernel

theorem arows3402 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3402 = true := by
  rw [show A10K2.u3402 = KTree.node A10K2.u3394 (nat_lit 57240986) (nat_lit 14554951347) (nat_lit 0) A10K2.u3401 from rfl, allE_node, arows3394, irow3402, arows3401]
  all_goals rfl

theorem atot3402 : totK PA10K2 A10K2.u3402 = [0, 0, 2372275091717, 13072407531152, 26429067763204, 23766851100389, 9592058808771, 1624388568203, 79079279468, 0] := by
  rw [show A10K2.u3402 = KTree.node A10K2.u3394 (nat_lit 57240986) (nat_lit 14554951347) (nat_lit 0) A10K2.u3401 from rfl, totK_node, atot3394, atot3401]
  decide +kernel

theorem arows3417 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3417 = true := by
  rw [show A10K2.u3417 = KTree.node A10K2.u3409 (nat_lit 57301789) (nat_lit 6284307410) (nat_lit 0) A10K2.u3416 from rfl, allE_node, arows3409, irow3417, arows3416]
  all_goals rfl

theorem atot3417 : totK PA10K2 A10K2.u3417 = [0, 0, 3289402961007, 16682470815492, 29730294583167, 21119697317173, 5128288056512, 407849765716, 6354482628, 0] := by
  rw [show A10K2.u3417 = KTree.node A10K2.u3409 (nat_lit 57301789) (nat_lit 6284307410) (nat_lit 0) A10K2.u3416 from rfl, totK_node, atot3409, atot3416]
  decide +kernel

theorem arows3433 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3433 = true := by
  rw [show A10K2.u3433 = KTree.node A10K2.u3425 (nat_lit 57402259) (nat_lit 9488116297) (nat_lit 0) A10K2.u3432 from rfl, allE_node, arows3425, irow3433, arows3432]
  all_goals rfl

theorem atot3433 : totK PA10K2 A10K2.u3433 = [0, 0, 834905328705, 8178139436747, 24886419814808, 29644364732632, 13114573793650, 1839219343754, 74564457688, 0] := by
  rw [show A10K2.u3433 = KTree.node A10K2.u3425 (nat_lit 57402259) (nat_lit 9488116297) (nat_lit 0) A10K2.u3432 from rfl, totK_node, atot3425, atot3432]
  decide +kernel

theorem arows3448 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3448 = true := by
  rw [show A10K2.u3448 = KTree.node A10K2.u3440 (nat_lit 57530730) (nat_lit 9773326432) (nat_lit 0) A10K2.u3447 from rfl, allE_node, arows3440, irow3448, arows3447]
  all_goals rfl

theorem atot3448 : totK PA10K2 A10K2.u3448 = [0, 0, 0, 2772033203376, 14874878044911, 28024569116892, 21925465523689, 7184938530068, 933575998874, 36704093874] := by
  rw [show A10K2.u3448 = KTree.node A10K2.u3440 (nat_lit 57530730) (nat_lit 9773326432) (nat_lit 0) A10K2.u3447 from rfl, totK_node, atot3440, atot3447]
  decide +kernel

theorem arows3466 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3466 = true := by
  rw [show A10K2.u3466 = KTree.node A10K2.u3458 (nat_lit 57621650) (nat_lit 15732242332) (nat_lit 0) A10K2.u3465 from rfl, allE_node, arows3458, irow3466, arows3465]
  all_goals rfl

theorem atot3466 : totK PA10K2 A10K2.u3466 = [0, 0, 1297955991958, 8518885265128, 21244583211932, 25890114100890, 15965016130949, 3823302058161, 333966901681, 5982052406] := by
  rw [show A10K2.u3466 = KTree.node A10K2.u3458 (nat_lit 57621650) (nat_lit 15732242332) (nat_lit 0) A10K2.u3465 from rfl, totK_node, atot3458, atot3465]
  decide +kernel

theorem arows3481 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3481 = true := by
  rw [show A10K2.u3481 = KTree.node A10K2.u3473 (nat_lit 57759931) (nat_lit 6831934262) (nat_lit 0) A10K2.u3480 from rfl, allE_node, arows3473, irow3481, arows3480]
  all_goals rfl

theorem atot3481 : totK PA10K2 A10K2.u3481 = [0, 0, 2188079250831, 12638741090192, 27273423780207, 24999040145599, 8368240205633, 962114796539, 36629191582, 0] := by
  rw [show A10K2.u3481 = KTree.node A10K2.u3473 (nat_lit 57759931) (nat_lit 6831934262) (nat_lit 0) A10K2.u3480 from rfl, totK_node, atot3473, atot3480]
  decide +kernel

theorem arows3497 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3497 = true := by
  rw [show A10K2.u3497 = KTree.node A10K2.u3489 (nat_lit 57822053) (nat_lit 7253494417) (nat_lit 0) A10K2.u3496 from rfl, allE_node, arows3489, irow3497, arows3496]
  all_goals rfl

theorem atot3497 : totK PA10K2 A10K2.u3497 = [0, 0, 2171906535597, 13680824098493, 29146788587580, 23735075398270, 6298729920360, 574253927116, 12475655917, 0] := by
  rw [show A10K2.u3497 = KTree.node A10K2.u3489 (nat_lit 57822053) (nat_lit 7253494417) (nat_lit 0) A10K2.u3496 from rfl, totK_node, atot3489, atot3496]
  decide +kernel

theorem arows3512 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3512 = true := by
  rw [show A10K2.u3512 = KTree.node A10K2.u3504 (nat_lit 58025762) (nat_lit 13632985490) (nat_lit 0) A10K2.u3511 from rfl, allE_node, arows3504, irow3512, arows3511]
  all_goals rfl

theorem atot3512 : totK PA10K2 A10K2.u3512 = [0, 0, 0, 4776559560139, 21935451385239, 32030960049304, 15057511891024, 2114057242547, 87588219036, 0] := by
  rw [show A10K2.u3512 = KTree.node A10K2.u3504 (nat_lit 58025762) (nat_lit 13632985490) (nat_lit 0) A10K2.u3511 from rfl, totK_node, atot3504, atot3511]
  decide +kernel

theorem arows3529 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3529 = true := by
  rw [show A10K2.u3529 = KTree.node A10K2.u3521 (nat_lit 58224638) (nat_lit 15844512021) (nat_lit 0) A10K2.u3528 from rfl, allE_node, arows3521, irow3529, arows3528]
  all_goals rfl

theorem atot3529 : totK PA10K2 A10K2.u3529 = [0, 0, 3600442167987, 15257993952272, 24023022491979, 20516925146401, 11308331020740, 2844792843700, 271960934478, 6354482628] := by
  rw [show A10K2.u3529 = KTree.node A10K2.u3521 (nat_lit 58224638) (nat_lit 15844512021) (nat_lit 0) A10K2.u3528 from rfl, totK_node, atot3521, atot3528]
  decide +kernel

theorem arows3544 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3544 = true := by
  rw [show A10K2.u3544 = KTree.node A10K2.u3536 (nat_lit 58395752) (nat_lit 12055462186) (nat_lit 0) A10K2.u3543 from rfl, allE_node, arows3536, irow3544, arows3543]
  all_goals rfl

theorem atot3544 : totK PA10K2 A10K2.u3544 = [0, 0, 2283767739473, 14165460766739, 29876006716670, 24892617222732, 7646441076913, 843185374616, 31082886609, 0] := by
  rw [show A10K2.u3544 = KTree.node A10K2.u3536 (nat_lit 58395752) (nat_lit 12055462186) (nat_lit 0) A10K2.u3543 from rfl, totK_node, atot3536, atot3543]
  decide +kernel

theorem arows3560 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3560 = true := by
  rw [show A10K2.u3560 = KTree.node A10K2.u3552 (nat_lit 58724640) (nat_lit 13525227562) (nat_lit 0) A10K2.u3559 from rfl, allE_node, arows3552, irow3560, arows3559]
  all_goals rfl

theorem atot3560 : totK PA10K2 A10K2.u3560 = [0, 2180308054505, 10968171653482, 20920102086553, 21296909740992, 15323145691970, 6779518338271, 1110782404136, 48968269916, 0] := by
  rw [show A10K2.u3560 = KTree.node A10K2.u3552 (nat_lit 58724640) (nat_lit 13525227562) (nat_lit 0) A10K2.u3559 from rfl, totK_node, atot3552, atot3559]
  decide +kernel

theorem arows3575 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3575 = true := by
  rw [show A10K2.u3575 = KTree.node A10K2.u3567 (nat_lit 58861348) (nat_lit 13734798012) (nat_lit 0) A10K2.u3574 from rfl, allE_node, arows3567, irow3575, arows3574]
  all_goals rfl

theorem atot3575 : totK PA10K2 A10K2.u3575 = [0, 2147695096082, 13129837965261, 28023406210392, 24392406944530, 7862740497218, 955590853488, 36196801203, 0, 0] := by
  rw [show A10K2.u3575 = KTree.node A10K2.u3567 (nat_lit 58861348) (nat_lit 13734798012) (nat_lit 0) A10K2.u3574 from rfl, totK_node, atot3567, atot3574]
  decide +kernel

theorem arows3595 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3595 = true := by
  rw [show A10K2.u3595 = KTree.node A10K2.u3587 (nat_lit 59010160) (nat_lit 14746494604) (nat_lit 0) A10K2.u3594 from rfl, allE_node, arows3587, irow3595, arows3594]
  all_goals rfl

theorem atot3595 : totK PA10K2 A10K2.u3595 = [0, 0, 4624747243853, 21601961832317, 32202101798549, 15683178558133, 2268616820206, 86610413884, 0, 0] := by
  rw [show A10K2.u3595 = KTree.node A10K2.u3587 (nat_lit 59010160) (nat_lit 14746494604) (nat_lit 0) A10K2.u3594 from rfl, totK_node, atot3587, atot3594]
  decide +kernel

theorem arows3610 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3610 = true := by
  rw [show A10K2.u3610 = KTree.node A10K2.u3602 (nat_lit 59324768) (nat_lit 10741708474) (nat_lit 0) A10K2.u3609 from rfl, allE_node, arows3602, irow3610, arows3609]
  all_goals rfl

theorem atot3610 : totK PA10K2 A10K2.u3610 = [0, 2298266100845, 11563958143065, 22835321734487, 23656897577854, 13270766275193, 3165371826435, 287609045340, 5676195732, 0] := by
  rw [show A10K2.u3610 = KTree.node A10K2.u3602 (nat_lit 59324768) (nat_lit 10741708474) (nat_lit 0) A10K2.u3609 from rfl, totK_node, atot3602, atot3609]
  decide +kernel

theorem arows3626 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3626 = true := by
  rw [show A10K2.u3626 = KTree.node A10K2.u3618 (nat_lit 59387044) (nat_lit 12704109333) (nat_lit 0) A10K2.u3625 from rfl, allE_node, arows3618, irow3626, arows3625]
  all_goals rfl

theorem atot3626 : totK PA10K2 A10K2.u3626 = [0, 2116282535288, 13056074753577, 28008310712853, 24449320594724, 7835259008131, 807933429709, 16872920140, 0, 0] := by
  rw [show A10K2.u3626 = KTree.node A10K2.u3618 (nat_lit 59387044) (nat_lit 12704109333) (nat_lit 0) A10K2.u3625 from rfl, totK_node, atot3618, atot3625]
  decide +kernel

theorem arows3641 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3641 = true := by
  rw [show A10K2.u3641 = KTree.node A10K2.u3633 (nat_lit 59483529) (nat_lit 4976127352) (nat_lit 0) A10K2.u3640 from rfl, allE_node, arows3633, irow3641, arows3640]
  all_goals rfl

theorem atot3641 : totK PA10K2 A10K2.u3641 = [0, 1609698614687, 10291658886470, 25386383824976, 28022715585899, 12651729346201, 1984302658582, 81057285836, 0, 0] := by
  rw [show A10K2.u3641 = KTree.node A10K2.u3633 (nat_lit 59483529) (nat_lit 4976127352) (nat_lit 0) A10K2.u3640 from rfl, totK_node, atot3633, atot3640]
  decide +kernel

theorem arows3658 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3658 = true := by
  rw [show A10K2.u3658 = KTree.node A10K2.u3650 (nat_lit 59619262) (nat_lit 13800404345) (nat_lit 0) A10K2.u3657 from rfl, allE_node, arows3650, irow3658, arows3657]
  all_goals rfl

theorem atot3658 : totK PA10K2 A10K2.u3658 = [0, 0, 2742697567505, 14846301421792, 28616763463500, 22694913876233, 7243779321897, 924086095100, 36704093874, 0] := by
  rw [show A10K2.u3658 = KTree.node A10K2.u3650 (nat_lit 59619262) (nat_lit 13800404345) (nat_lit 0) A10K2.u3657 from rfl, totK_node, atot3650, atot3657]
  decide +kernel

theorem arows3673 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3673 = true := by
  rw [show A10K2.u3673 = KTree.node A10K2.u3665 (nat_lit 59691272) (nat_lit 13013342995) (nat_lit 0) A10K2.u3672 from rfl, allE_node, arows3665, irow3673, arows3672]
  all_goals rfl

theorem atot3673 : totK PA10K2 A10K2.u3673 = [0, 573258531646, 4501607061753, 16006773846088, 28554182250292, 21884685117478, 5423106124266, 408624499413, 6239673734, 0] := by
  rw [show A10K2.u3673 = KTree.node A10K2.u3665 (nat_lit 59691272) (nat_lit 13013342995) (nat_lit 0) A10K2.u3672 from rfl, totK_node, atot3665, atot3672]
  decide +kernel

theorem arows3689 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3689 = true := by
  rw [show A10K2.u3689 = KTree.node A10K2.u3681 (nat_lit 59808839) (nat_lit 10996016878) (nat_lit 0) A10K2.u3688 from rfl, allE_node, arows3681, irow3689, arows3688]
  all_goals rfl

theorem atot3689 : totK PA10K2 A10K2.u3689 = [0, 2831657082060, 15043924083346, 28504929713343, 22518221259815, 6836000797867, 803752047228, 36196801203, 0, 0] := by
  rw [show A10K2.u3689 = KTree.node A10K2.u3681 (nat_lit 59808839) (nat_lit 10996016878) (nat_lit 0) A10K2.u3688 from rfl, totK_node, atot3681, atot3688]
  decide +kernel

theorem arows3704 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3704 = true := by
  rw [show A10K2.u3704 = KTree.node A10K2.u3696 (nat_lit 59889941) (nat_lit 7051909534) (nat_lit 0) A10K2.u3703 from rfl, allE_node, arows3696, irow3704, arows3703]
  all_goals rfl

theorem atot3704 : totK PA10K2 A10K2.u3704 = [0, 2488209812685, 13595080123075, 27465535848747, 24010560971875, 8397121808715, 1026172634019, 37204059898, 0, 0] := by
  rw [show A10K2.u3704 = KTree.node A10K2.u3696 (nat_lit 59889941) (nat_lit 7051909534) (nat_lit 0) A10K2.u3703 from rfl, totK_node, atot3696, atot3703]
  decide +kernel

theorem arows3722 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3722 = true := by
  rw [show A10K2.u3722 = KTree.node A10K2.u3714 (nat_lit 60031931) (nat_lit 2235365272) (nat_lit 0) A10K2.u3721 from rfl, allE_node, arows3714, irow3722, arows3721]
  all_goals rfl

theorem atot3722 : totK PA10K2 A10K2.u3722 = [0, 295989007569, 6880273641512, 24484734843688, 30050756633251, 12458874150353, 1699556300506, 69261865415, 0, 0] := by
  rw [show A10K2.u3722 = KTree.node A10K2.u3714 (nat_lit 60031931) (nat_lit 2235365272) (nat_lit 0) A10K2.u3721 from rfl, totK_node, atot3714, atot3721]
  decide +kernel

theorem arows3737 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3737 = true := by
  rw [show A10K2.u3737 = KTree.node A10K2.u3729 (nat_lit 60171703) (nat_lit 12677189900) (nat_lit 0) A10K2.u3736 from rfl, allE_node, arows3729, irow3737, arows3736]
  all_goals rfl

theorem atot3737 : totK PA10K2 A10K2.u3737 = [0, 0, 3573850966553, 18503913751751, 31631060433046, 18605060720225, 3226886866096, 149352211486, 0, 0] := by
  rw [show A10K2.u3737 = KTree.node A10K2.u3729 (nat_lit 60171703) (nat_lit 12677189900) (nat_lit 0) A10K2.u3736 from rfl, totK_node, atot3729, atot3736]
  decide +kernel

theorem arows3753 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3753 = true := by
  rw [show A10K2.u3753 = KTree.node A10K2.u3745 (nat_lit 60840454) (nat_lit 11733774296) (nat_lit 0) A10K2.u3752 from rfl, allE_node, arows3745, irow3753, arows3752]
  all_goals rfl

theorem atot3753 : totK PA10K2 A10K2.u3753 = [0, 0, 2714666560915, 14633535682998, 28984538212587, 23224580489550, 6384148185262, 635394858541, 11900787601, 0] := by
  rw [show A10K2.u3753 = KTree.node A10K2.u3745 (nat_lit 60840454) (nat_lit 11733774296) (nat_lit 0) A10K2.u3752 from rfl, totK_node, atot3745, atot3752]
  decide +kernel

theorem arows3768 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3768 = true := by
  rw [show A10K2.u3768 = KTree.node A10K2.u3760 (nat_lit 60984329) (nat_lit 9732766126) (nat_lit 0) A10K2.u3767 from rfl, allE_node, arows3760, irow3768, arows3767]
  all_goals rfl

theorem atot3768 : totK PA10K2 A10K2.u3768 = [0, 0, 2923475942417, 16066550602662, 30275570438288, 21784400109005, 4838082848936, 370131786906, 6354482628, 0] := by
  rw [show A10K2.u3768 = KTree.node A10K2.u3760 (nat_lit 60984329) (nat_lit 9732766126) (nat_lit 0) A10K2.u3767 from rfl, totK_node, atot3760, atot3767]
  decide +kernel

theorem arows3785 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3785 = true := by
  rw [show A10K2.u3785 = KTree.node A10K2.u3777 (nat_lit 61458068) (nat_lit 12027339891) (nat_lit 0) A10K2.u3784 from rfl, allE_node, arows3777, irow3785, arows3784]
  all_goals rfl

theorem atot3785 : totK PA10K2 A10K2.u3785 = [0, 0, 2382417698087, 13612292291281, 28179331529946, 24428124271728, 7997820985478, 974347054020, 37204059898, 0] := by
  rw [show A10K2.u3785 = KTree.node A10K2.u3777 (nat_lit 61458068) (nat_lit 12027339891) (nat_lit 0) A10K2.u3784 from rfl, totK_node, atot3777, atot3784]
  decide +kernel

theorem arows3800 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3800 = true := by
  rw [show A10K2.u3800 = KTree.node A10K2.u3792 (nat_lit 61547813) (nat_lit 7209997820) (nat_lit 0) A10K2.u3799 from rfl, allE_node, arows3792, irow3800, arows3799]
  all_goals rfl

theorem atot3800 : totK PA10K2 A10K2.u3800 = [0, 0, 2324395304794, 13984386084953, 29426658441599, 24626282865802, 7074659598382, 675808972206, 13401508080, 0] := by
  rw [show A10K2.u3800 = KTree.node A10K2.u3792 (nat_lit 61547813) (nat_lit 7209997820) (nat_lit 0) A10K2.u3799 from rfl, totK_node, atot3792, atot3799]
  decide +kernel

theorem arows3816 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3816 = true := by
  rw [show A10K2.u3816 = KTree.node A10K2.u3808 (nat_lit 61898801) (nat_lit 10026794723) (nat_lit 0) A10K2.u3815 from rfl, allE_node, arows3808, irow3816, arows3815]
  all_goals rfl

theorem atot3816 : totK PA10K2 A10K2.u3816 = [0, 0, 3102789104553, 16227194876188, 30079675277856, 22005245528020, 5242857321936, 407912641249, 5546304973, 0] := by
  rw [show A10K2.u3816 = KTree.node A10K2.u3808 (nat_lit 61898801) (nat_lit 10026794723) (nat_lit 0) A10K2.u3815 from rfl, totK_node, atot3808, atot3815]
  decide +kernel

theorem arows3831 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3831 = true := by
  rw [show A10K2.u3831 = KTree.node A10K2.u3823 (nat_lit 61983556) (nat_lit 12799683768) (nat_lit 0) A10K2.u3830 from rfl, allE_node, arows3823, irow3831, arows3830]
  all_goals rfl

theorem atot3831 : totK PA10K2 A10K2.u3831 = [0, 0, 2509358872759, 14199210203553, 28524666747737, 23382578846584, 7137829805396, 844507862786, 36768997705, 0] := by
  rw [show A10K2.u3831 = KTree.node A10K2.u3823 (nat_lit 61983556) (nat_lit 12799683768) (nat_lit 0) A10K2.u3830 from rfl, totK_node, atot3823, atot3830]
  decide +kernel

theorem arows3850 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3850 = true := by
  rw [show A10K2.u3850 = KTree.node A10K2.u3842 (nat_lit 62128236) (nat_lit 11430996088) (nat_lit 0) A10K2.u3849 from rfl, allE_node, arows3842, irow3850, arows3849]
  all_goals rfl

theorem atot3850 : totK PA10K2 A10K2.u3850 = [0, 0, 582523478866, 7887589320134, 25586690866315, 29364123522772, 10779451637837, 1382547514499, 49173662787, 0] := by
  rw [show A10K2.u3850 = KTree.node A10K2.u3842 (nat_lit 62128236) (nat_lit 11430996088) (nat_lit 0) A10K2.u3849 from rfl, totK_node, atot3842, atot3849]
  decide +kernel

theorem arows3865 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3865 = true := by
  rw [show A10K2.u3865 = KTree.node A10K2.u3857 (nat_lit 62273793) (nat_lit 9770762046) (nat_lit 0) A10K2.u3864 from rfl, allE_node, arows3857, irow3865, arows3864]
  all_goals rfl

theorem atot3865 : totK PA10K2 A10K2.u3865 = [0, 0, 0, 3556821957145, 18183549586062, 30834183807706, 18071532293562, 3758862505723, 211053561771, 0] := by
  rw [show A10K2.u3865 = KTree.node A10K2.u3857 (nat_lit 62273793) (nat_lit 9770762046) (nat_lit 0) A10K2.u3864 from rfl, totK_node, atot3857, atot3864]
  decide +kernel

theorem arows3881 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3881 = true := by
  rw [show A10K2.u3881 = KTree.node A10K2.u3873 (nat_lit 62946760) (nat_lit 13461853099) (nat_lit 0) A10K2.u3880 from rfl, allE_node, arows3873, irow3881, arows3880]
  all_goals rfl

theorem atot3881 : totK PA10K2 A10K2.u3881 = [0, 2989798215603, 15626575045645, 29043337914827, 22321882570695, 6696429749086, 1014785270919, 460192698193, 142269073820, 6354482628] := by
  rw [show A10K2.u3881 = KTree.node A10K2.u3873 (nat_lit 62946760) (nat_lit 13461853099) (nat_lit 0) A10K2.u3880 from rfl, totK_node, atot3873, atot3880]
  decide +kernel

theorem arows3896 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3896 = true := by
  rw [show A10K2.u3896 = KTree.node A10K2.u3888 (nat_lit 63148022) (nat_lit 16694986552) (nat_lit 0) A10K2.u3895 from rfl, allE_node, arows3888, irow3896, arows3895]
  all_goals rfl

theorem atot3896 : totK PA10K2 A10K2.u3896 = [0, 1461308260998, 10401660153650, 26153618295243, 27809754941039, 12012450259838, 1787491216593, 75062079822, 0, 0] := by
  rw [show A10K2.u3896 = KTree.node A10K2.u3888 (nat_lit 63148022) (nat_lit 16694986552) (nat_lit 0) A10K2.u3895 from rfl, totK_node, atot3888, atot3895]
  decide +kernel

theorem arows3913 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3913 = true := by
  rw [show A10K2.u3913 = KTree.node A10K2.u3905 (nat_lit 63213445) (nat_lit 2999851529) (nat_lit 0) A10K2.u3912 from rfl, allE_node, arows3905, irow3913, arows3912]
  all_goals rfl

theorem atot3913 : totK PA10K2 A10K2.u3913 = [0, 0, 2739371604150, 15834251836101, 30976269734466, 22829716807741, 5700121869791, 476762091131, 7903172220, 0] := by
  rw [show A10K2.u3913 = KTree.node A10K2.u3905 (nat_lit 63213445) (nat_lit 2999851529) (nat_lit 0) A10K2.u3912 from rfl, totK_node, atot3905, atot3912]
  decide +kernel

theorem arows3928 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3928 = true := by
  rw [show A10K2.u3928 = KTree.node A10K2.u3920 (nat_lit 63523616) (nat_lit 12401337551) (nat_lit 0) A10K2.u3927 from rfl, allE_node, arows3920, irow3928, arows3927]
  all_goals rfl

theorem atot3928 : totK PA10K2 A10K2.u3928 = [0, 2305653685916, 12844792915533, 26432360932003, 24610456425321, 10527301701643, 1817852369125, 93451449558, 0, 0] := by
  rw [show A10K2.u3928 = KTree.node A10K2.u3920 (nat_lit 63523616) (nat_lit 12401337551) (nat_lit 0) A10K2.u3927 from rfl, totK_node, atot3920, atot3927]
  decide +kernel

theorem arows3944 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3944 = true := by
  rw [show A10K2.u3944 = KTree.node A10K2.u3936 (nat_lit 63592606) (nat_lit 11222761755) (nat_lit 0) A10K2.u3943 from rfl, allE_node, arows3936, irow3944, arows3943]
  all_goals rfl

theorem atot3944 : totK PA10K2 A10K2.u3944 = [0, 2899447298876, 15403866126570, 29292687399454, 23212269876990, 6693945546066, 605477193304, 12475655917, 0, 0] := by
  rw [show A10K2.u3944 = KTree.node A10K2.u3936 (nat_lit 63592606) (nat_lit 11222761755) (nat_lit 0) A10K2.u3943 from rfl, totK_node, atot3936, atot3943]
  decide +kernel

theorem arows3959 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3959 = true := by
  rw [show A10K2.u3959 = KTree.node A10K2.u3951 (nat_lit 63680162) (nat_lit 14196339071) (nat_lit 0) A10K2.u3958 from rfl, allE_node, arows3951, irow3959, arows3958]
  all_goals rfl

theorem atot3959 : totK PA10K2 A10K2.u3959 = [0, 862423573369, 7875977404383, 23698445832332, 29476367099846, 14652195496887, 2401132715667, 106830828675, 0, 0] := by
  rw [show A10K2.u3959 = KTree.node A10K2.u3951 (nat_lit 63680162) (nat_lit 14196339071) (nat_lit 0) A10K2.u3958 from rfl, totK_node, atot3951, atot3958]
  decide +kernel

theorem arows3977 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3977 = true := by
  rw [show A10K2.u3977 = KTree.node A10K2.u3969 (nat_lit 63815044) (nat_lit 844051729) (nat_lit 0) A10K2.u3976 from rfl, allE_node, arows3969, irow3977, arows3976]
  all_goals rfl

theorem atot3977 : totK PA10K2 A10K2.u3977 = [0, 0, 2894672807528, 15151357791288, 28474970216050, 22770626703156, 7496379006902, 950094790160, 36704093874, 0] := by
  rw [show A10K2.u3977 = KTree.node A10K2.u3969 (nat_lit 63815044) (nat_lit 844051729) (nat_lit 0) A10K2.u3976 from rfl, totK_node, atot3969, atot3976]
  decide +kernel

theorem arows3992 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3992 = true := by
  rw [show A10K2.u3992 = KTree.node A10K2.u3984 (nat_lit 63909383) (nat_lit 14109498713) (nat_lit 0) A10K2.u3991 from rfl, allE_node, arows3984, irow3992, arows3991]
  all_goals rfl

theorem atot3992 : totK PA10K2 A10K2.u3992 = [0, 887742285343, 6107179921388, 18389155135740, 28084001778585, 19689736284306, 4803472653509, 372734079515, 6239673734, 0] := by
  rw [show A10K2.u3992 = KTree.node A10K2.u3984 (nat_lit 63909383) (nat_lit 14109498713) (nat_lit 0) A10K2.u3991 from rfl, totK_node, atot3984, atot3991]
  decide +kernel

theorem arows4008 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4008 = true := by
  rw [show A10K2.u4008 = KTree.node A10K2.u4000 (nat_lit 64545941) (nat_lit 5610224497) (nat_lit 0) A10K2.u4007 from rfl, allE_node, arows4000, irow4008, arows4007]
  all_goals rfl

theorem atot4008 : totK PA10K2 A10K2.u4008 = [0, 3116711694447, 16209659651955, 29810334082057, 22872400119908, 6789132823420, 687456839674, 13364899180, 0, 0] := by
  rw [show A10K2.u4008 = KTree.node A10K2.u4000 (nat_lit 64545941) (nat_lit 5610224497) (nat_lit 0) A10K2.u4007 from rfl, totK_node, atot4000, atot4007]
  decide +kernel

theorem arows4023 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4023 = true := by
  rw [show A10K2.u4023 = KTree.node A10K2.u4015 (nat_lit 64686179) (nat_lit 11933677) (nat_lit 0) A10K2.u4022 from rfl, allE_node, arows4015, irow4023, arows4022]
  all_goals rfl

theorem atot4023 : totK PA10K2 A10K2.u4023 = [0, 2389005205952, 13720581173922, 28399698490350, 24767676771379, 8378264848028, 1016079635584, 37204059898, 0, 0] := by
  rw [show A10K2.u4023 = KTree.node A10K2.u4015 (nat_lit 64686179) (nat_lit 11933677) (nat_lit 0) A10K2.u4022 from rfl, totK_node, atot4015, atot4022]
  decide +kernel

theorem arows4040 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4040 = true := by
  rw [show A10K2.u4040 = KTree.node A10K2.u4032 (nat_lit 64746930) (nat_lit 14679742760) (nat_lit 0) A10K2.u4039 from rfl, allE_node, arows4032, irow4040, arows4039]
  all_goals rfl

theorem atot4040 : totK PA10K2 A10K2.u4040 = [0, 0, 4254396478994, 20396903064048, 32365008119505, 18660558641006, 3341082250885, 150778795813, 0, 0] := by
  rw [show A10K2.u4040 = KTree.node A10K2.u4032 (nat_lit 64746930) (nat_lit 14679742760) (nat_lit 0) A10K2.u4039 from rfl, totK_node, atot4032, atot4039]
  decide +kernel

theorem arows4055 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4055 = true := by
  rw [show A10K2.u4055 = KTree.node A10K2.u4047 (nat_lit 64833804) (nat_lit 12145468572) (nat_lit 0) A10K2.u4054 from rfl, allE_node, arows4047, irow4055, arows4054]
  all_goals rfl

theorem atot4055 : totK PA10K2 A10K2.u4055 = [0, 0, 2131737177002, 13233834501744, 29028735520598, 25873069275133, 8129645097486, 767173143113, 14159155365, 0] := by
  rw [show A10K2.u4055 = KTree.node A10K2.u4047 (nat_lit 64833804) (nat_lit 12145468572) (nat_lit 0) A10K2.u4054 from rfl, totK_node, atot4047, atot4054]
  decide +kernel

theorem arows4071 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4071 = true := by
  rw [show A10K2.u4071 = KTree.node A10K2.u4063 (nat_lit 64974299) (nat_lit 6766853699) (nat_lit 0) A10K2.u4070 from rfl, allE_node, arows4063, irow4071, arows4070]
  all_goals rfl

theorem atot4071 : totK PA10K2 A10K2.u4071 = [0, 0, 2386020461250, 13738203929173, 28633322415654, 25238385731290, 8141805731516, 745806566364, 12758098799, 0] := by
  rw [show A10K2.u4071 = KTree.node A10K2.u4063 (nat_lit 64974299) (nat_lit 6766853699) (nat_lit 0) A10K2.u4070 from rfl, totK_node, atot4063, atot4070]
  decide +kernel

theorem arows4086 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4086 = true := by
  rw [show A10K2.u4086 = KTree.node A10K2.u4078 (nat_lit 67132181) (nat_lit 7018395041) (nat_lit 0) A10K2.u4085 from rfl, allE_node, arows4078, irow4086, arows4085]
  all_goals rfl

theorem atot4086 : totK PA10K2 A10K2.u4086 = [2338692983822, 12465376030733, 24087533611547, 19832615777801, 8197906693101, 5253665342275, 3771210818185, 961189328672, 61018386929, 0] := by
  rw [show A10K2.u4086 = KTree.node A10K2.u4078 (nat_lit 67132181) (nat_lit 7018395041) (nat_lit 0) A10K2.u4085 from rfl, totK_node, atot4078, atot4085]
  decide +kernel

theorem arows4109 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4109 = true := by
  rw [show A10K2.u4109 = KTree.node A10K2.u4101 (nat_lit 67258436) (nat_lit 11710074203) (nat_lit 0) A10K2.u4108 from rfl, allE_node, arows4101, irow4109, arows4108]
  all_goals rfl

theorem atot4109 : totK PA10K2 A10K2.u4109 = [2866031060996, 14885869798575, 28186156751032, 22786544335730, 6901264682907, 685528291605, 11900787601, 0, 0, 0] := by
  rw [show A10K2.u4109 = KTree.node A10K2.u4101 (nat_lit 67258436) (nat_lit 11710074203) (nat_lit 0) A10K2.u4108 from rfl, totK_node, atot4101, atot4108]
  decide +kernel

theorem arows4124 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4124 = true := by
  rw [show A10K2.u4124 = KTree.node A10K2.u4116 (nat_lit 67343295) (nat_lit 9955663627) (nat_lit 0) A10K2.u4123 from rfl, allE_node, arows4116, irow4124, arows4123]
  all_goals rfl

theorem atot4124 : totK PA10K2 A10K2.u4124 = [1078827900697, 9197848452971, 25161958500221, 28428978479926, 13228096640777, 2167348680196, 98846728256, 0, 0, 0] := by
  rw [show A10K2.u4124 = KTree.node A10K2.u4116 (nat_lit 67343295) (nat_lit 9955663627) (nat_lit 0) A10K2.u4123 from rfl, totK_node, atot4116, atot4123]
  decide +kernel

theorem arows4140 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4140 = true := by
  rw [show A10K2.u4140 = KTree.node A10K2.u4132 (nat_lit 67411332) (nat_lit 7922537177) (nat_lit 0) A10K2.u4139 from rfl, allE_node, arows4132, irow4140, arows4139]
  all_goals rfl

theorem atot4140 : totK PA10K2 A10K2.u4140 = [0, 2520604463893, 14379538317976, 28363165519494, 22775489080398, 7215245898260, 918869924319, 36134558889, 0, 0] := by
  rw [show A10K2.u4140 = KTree.node A10K2.u4132 (nat_lit 67411332) (nat_lit 7922537177) (nat_lit 0) A10K2.u4139 from rfl, totK_node, atot4132, atot4139]
  decide +kernel

theorem arows4155 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4155 = true := by
  rw [show A10K2.u4155 = KTree.node A10K2.u4147 (nat_lit 67568068) (nat_lit 8811840739) (nat_lit 0) A10K2.u4154 from rfl, allE_node, arows4147, irow4155, arows4154]
  all_goals rfl

theorem atot4155 : totK PA10K2 A10K2.u4155 = [833436429740, 5399320575807, 17086475871185, 28280728414420, 20257245294469, 4925439779776, 367789340581, 5676195732, 0, 0] := by
  rw [show A10K2.u4155 = KTree.node A10K2.u4147 (nat_lit 67568068) (nat_lit 8811840739) (nat_lit 0) A10K2.u4154 from rfl, totK_node, atot4147, atot4154]
  decide +kernel

theorem arows4172 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4172 = true := by
  rw [show A10K2.u4172 = KTree.node A10K2.u4164 (nat_lit 68193779) (nat_lit 7384936281) (nat_lit 0) A10K2.u4171 from rfl, allE_node, arows4164, irow4172, arows4171]
  all_goals rfl

theorem atot4172 : totK PA10K2 A10K2.u4172 = [2085320857616, 12978400042053, 27976676103228, 24609590801975, 8242493731426, 994238390780, 36196801203, 0, 0, 0] := by
  rw [show A10K2.u4172 = KTree.node A10K2.u4164 (nat_lit 68193779) (nat_lit 7384936281) (nat_lit 0) A10K2.u4171 from rfl, totK_node, atot4164, atot4171]
  decide +kernel

theorem arows4187 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4187 = true := by
  rw [show A10K2.u4187 = KTree.node A10K2.u4179 (nat_lit 68279149) (nat_lit 6121173289) (nat_lit 0) A10K2.u4186 from rfl, allE_node, arows4179, irow4187, arows4186]
  all_goals rfl

theorem atot4187 : totK PA10K2 A10K2.u4187 = [3033480209461, 15596499307402, 28351708158442, 21733813839242, 7129842792579, 924563980599, 37204059898, 0, 0, 0] := by
  rw [show A10K2.u4187 = KTree.node A10K2.u4179 (nat_lit 68279149) (nat_lit 6121173289) (nat_lit 0) A10K2.u4186 from rfl, totK_node, atot4179, atot4186]
  decide +kernel

theorem arows4203 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4203 = true := by
  rw [show A10K2.u4203 = KTree.node A10K2.u4195 (nat_lit 68424626) (nat_lit 9630801458) (nat_lit 0) A10K2.u4202 from rfl, allE_node, arows4195, irow4203, arows4202]
  all_goals rfl

theorem atot4203 : totK PA10K2 A10K2.u4203 = [0, 5164496104735, 22572393652455, 31611225408407, 15000684243699, 2233825939485, 81833253981, 0, 0, 0] := by
  rw [show A10K2.u4203 = KTree.node A10K2.u4195 (nat_lit 68424626) (nat_lit 9630801458) (nat_lit 0) A10K2.u4202 from rfl, totK_node, atot4195, atot4202]
  decide +kernel

theorem arows4218 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4218 = true := by
  rw [show A10K2.u4218 = KTree.node A10K2.u4210 (nat_lit 68566206) (nat_lit 11842463174) (nat_lit 0) A10K2.u4217 from rfl, allE_node, arows4210, irow4218, arows4217]
  all_goals rfl

theorem atot4218 : totK PA10K2 A10K2.u4218 = [0, 3028850032177, 16389434782886, 30152398405268, 20695805532968, 4875383769779, 360854821204, 0, 0, 0] := by
  rw [show A10K2.u4218 = KTree.node A10K2.u4210 (nat_lit 68566206) (nat_lit 11842463174) (nat_lit 0) A10K2.u4217 from rfl, totK_node, atot4210, atot4217]
  decide +kernel

theorem arows4236 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4236 = true := by
  rw [show A10K2.u4236 = KTree.node A10K2.u4228 (nat_lit 68714042) (nat_lit 11265855181) (nat_lit 0) A10K2.u4235 from rfl, allE_node, arows4228, irow4236, arows4235]
  all_goals rfl

theorem atot4236 : totK PA10K2 A10K2.u4236 = [2986070823486, 14944851591807, 27895383356684, 23209490138556, 7951745160263, 1070886135739, 121115588583, 6354482628, 0, 0] := by
  rw [show A10K2.u4236 = KTree.node A10K2.u4228 (nat_lit 68714042) (nat_lit 11265855181) (nat_lit 0) A10K2.u4235 from rfl, totK_node, atot4228, atot4235]
  decide +kernel

theorem arows4251 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4251 = true := by
  rw [show A10K2.u4251 = KTree.node A10K2.u4243 (nat_lit 68913472) (nat_lit 14362420927) (nat_lit 0) A10K2.u4250 from rfl, allE_node, arows4243, irow4251, arows4250]
  all_goals rfl

theorem atot4251 : totK PA10K2 A10K2.u4251 = [1463230794992, 10547167022627, 26169293171256, 27540004966205, 12139247748753, 1858256509742, 75062079822, 0, 0, 0] := by
  rw [show A10K2.u4251 = KTree.node A10K2.u4243 (nat_lit 68913472) (nat_lit 14362420927) (nat_lit 0) A10K2.u4250 from rfl, totK_node, atot4243, atot4250]
  decide +kernel

theorem arows4267 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4267 = true := by
  rw [show A10K2.u4267 = KTree.node A10K2.u4259 (nat_lit 68977209) (nat_lit 7193401148) (nat_lit 0) A10K2.u4266 from rfl, allE_node, arows4259, irow4267, arows4266]
  all_goals rfl

theorem atot4267 : totK PA10K2 A10K2.u4267 = [0, 2958483040502, 15736234734271, 29941470927825, 23024747807378, 6253895394471, 519453798615, 7007974415, 0, 0] := by
  rw [show A10K2.u4267 = KTree.node A10K2.u4259 (nat_lit 68977209) (nat_lit 7193401148) (nat_lit 0) A10K2.u4266 from rfl, totK_node, atot4259, atot4266]
  decide +kernel

theorem arows4282 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4282 = true := by
  rw [show A10K2.u4282 = KTree.node A10K2.u4274 (nat_lit 69182919) (nat_lit 14063348317) (nat_lit 0) A10K2.u4281 from rfl, allE_node, arows4274, irow4282, arows4281]
  all_goals rfl

theorem atot4282 : totK PA10K2 A10K2.u4282 = [0, 2043015104252, 12048298819830, 26384505187816, 25962022501223, 11010924848228, 1657743196918, 73776485728, 0, 0] := by
  rw [show A10K2.u4282 = KTree.node A10K2.u4274 (nat_lit 69182919) (nat_lit 14063348317) (nat_lit 0) A10K2.u4281 from rfl, totK_node, atot4274, atot4281]
  decide +kernel

theorem arows4299 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4299 = true := by
  rw [show A10K2.u4299 = KTree.node A10K2.u4291 (nat_lit 69243440) (nat_lit 14997150671) (nat_lit 0) A10K2.u4298 from rfl, allE_node, arows4291, irow4299, arows4298]
  all_goals rfl

theorem atot4299 : totK PA10K2 A10K2.u4299 = [0, 2463963093167, 13656028595690, 27624207306081, 23860212937867, 7947820447154, 963216203619, 36196801203, 0, 0] := by
  rw [show A10K2.u4299 = KTree.node A10K2.u4291 (nat_lit 69243440) (nat_lit 14997150671) (nat_lit 0) A10K2.u4298 from rfl, totK_node, atot4291, atot4298]
  decide +kernel

theorem arows4314 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4314 = true := by
  rw [show A10K2.u4314 = KTree.node A10K2.u4306 (nat_lit 69389138) (nat_lit 13118588630) (nat_lit 0) A10K2.u4313 from rfl, allE_node, arows4306, irow4314, arows4313]
  all_goals rfl

theorem atot4314 : totK PA10K2 A10K2.u4314 = [0, 2943941481045, 16137725816064, 30483882920979, 22193875354180, 5194491299745, 343437487009, 5976421810, 0, 0] := by
  rw [show A10K2.u4314 = KTree.node A10K2.u4306 (nat_lit 69389138) (nat_lit 13118588630) (nat_lit 0) A10K2.u4313 from rfl, totK_node, atot4306, atot4313]
  decide +kernel

theorem arows4330 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4330 = true := by
  rw [show A10K2.u4330 = KTree.node A10K2.u4322 (nat_lit 69472241) (nat_lit 8038460607) (nat_lit 0) A10K2.u4329 from rfl, allE_node, arows4322, irow4330, arows4329]
  all_goals rfl

theorem atot4330 : totK PA10K2 A10K2.u4330 = [0, 0, 4212337307024, 20098232374444, 31890092360746, 18062589073940, 3151733632073, 144265755835, 0, 0] := by
  rw [show A10K2.u4330 = KTree.node A10K2.u4322 (nat_lit 69472241) (nat_lit 8038460607) (nat_lit 0) A10K2.u4329 from rfl, totK_node, atot4322, atot4329]
  decide +kernel

theorem arows4345 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4345 = true := by
  rw [show A10K2.u4345 = KTree.node A10K2.u4337 (nat_lit 69606838) (nat_lit 16940207757) (nat_lit 0) A10K2.u4344 from rfl, allE_node, arows4337, irow4345, arows4344]
  all_goals rfl

theorem atot4345 : totK PA10K2 A10K2.u4345 = [0, 0, 2049263194366, 12945551541567, 27975690753263, 23306134351178, 7435489479563, 945726357714, 36134558889, 0] := by
  rw [show A10K2.u4345 = KTree.node A10K2.u4337 (nat_lit 69606838) (nat_lit 16940207757) (nat_lit 0) A10K2.u4344 from rfl, totK_node, atot4337, atot4344]
  decide +kernel

theorem arows4364 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4364 = true := by
  rw [show A10K2.u4364 = KTree.node A10K2.u4356 (nat_lit 70257194) (nat_lit 7956166165) (nat_lit 0) A10K2.u4363 from rfl, allE_node, arows4356, irow4364, arows4363]
  all_goals rfl

theorem atot4364 : totK PA10K2 A10K2.u4364 = [0, 2154550315718, 12463384928647, 26100444023043, 24144594701131, 10475996948811, 2278723333958, 227296609147, 5676195732, 0] := by
  rw [show A10K2.u4364 = KTree.node A10K2.u4356 (nat_lit 70257194) (nat_lit 7956166165) (nat_lit 0) A10K2.u4363 from rfl, totK_node, atot4356, atot4363]
  decide +kernel

theorem arows4379 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4379 = true := by
  rw [show A10K2.u4379 = KTree.node A10K2.u4371 (nat_lit 70335134) (nat_lit 11905083190) (nat_lit 0) A10K2.u4378 from rfl, allE_node, arows4371, irow4379, arows4378]
  all_goals rfl

theorem atot4379 : totK PA10K2 A10K2.u4379 = [0, 2121560808705, 12366482517815, 26666362188607, 25239594588635, 9185278202132, 1156898638942, 42317974492, 0, 0] := by
  rw [show A10K2.u4379 = KTree.node A10K2.u4371 (nat_lit 70335134) (nat_lit 11905083190) (nat_lit 0) A10K2.u4378 from rfl, totK_node, atot4371, atot4378]
  decide +kernel

theorem arows4395 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4395 = true := by
  rw [show A10K2.u4395 = KTree.node A10K2.u4387 (nat_lit 70421034) (nat_lit 8254110537) (nat_lit 0) A10K2.u4394 from rfl, allE_node, arows4387, irow4395, arows4394]
  all_goals rfl

theorem atot4395 : totK PA10K2 A10K2.u4395 = [0, 1671892701588, 11688299804419, 27570569747226, 25575109800535, 8490994777370, 1070553975481, 37172849495, 0, 0] := by
  rw [show A10K2.u4395 = KTree.node A10K2.u4387 (nat_lit 70421034) (nat_lit 8254110537) (nat_lit 0) A10K2.u4394 from rfl, totK_node, atot4387, atot4394]
  decide +kernel

theorem arows4410 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4410 = true := by
  rw [show A10K2.u4410 = KTree.node A10K2.u4402 (nat_lit 70605608) (nat_lit 11195828776) (nat_lit 0) A10K2.u4409 from rfl, allE_node, arows4402, irow4410, arows4409]
  all_goals rfl

theorem atot4410 : totK PA10K2 A10K2.u4410 = [0, 0, 4815558173113, 22169036995576, 32276055185313, 14904001462875, 1955606789769, 62025894999, 0, 0] := by
  rw [show A10K2.u4410 = KTree.node A10K2.u4402 (nat_lit 70605608) (nat_lit 11195828776) (nat_lit 0) A10K2.u4409 from rfl, totK_node, atot4402, atot4409]
  decide +kernel

theorem arows4427 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4427 = true := by
  rw [show A10K2.u4427 = KTree.node A10K2.u4419 (nat_lit 70797347) (nat_lit 8144796693) (nat_lit 0) A10K2.u4426 from rfl, allE_node, arows4419, irow4427, arows4426]
  all_goals rfl

theorem atot4427 : totK PA10K2 A10K2.u4427 = [0, 2201617000075, 11370331295118, 22966043869648, 23666727909809, 12911435168697, 3212006302375, 292013474143, 5976421810, 0] := by
  rw [show A10K2.u4427 = KTree.node A10K2.u4419 (nat_lit 70797347) (nat_lit 8144796693) (nat_lit 0) A10K2.u4426 from rfl, totK_node, atot4419, atot4426]
  decide +kernel

theorem arows4442 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4442 = true := by
  rw [show A10K2.u4442 = KTree.node A10K2.u4434 (nat_lit 71001836) (nat_lit 7791961771) (nat_lit 0) A10K2.u4441 from rfl, allE_node, arows4434, irow4442, arows4441]
  all_goals rfl

theorem atot4442 : totK PA10K2 A10K2.u4442 = [0, 2242114494754, 13446833394951, 28858046779734, 25749444493158, 8654299560093, 850744692480, 13671283666, 0, 0] := by
  rw [show A10K2.u4442 = KTree.node A10K2.u4434 (nat_lit 71001836) (nat_lit 7791961771) (nat_lit 0) A10K2.u4441 from rfl, totK_node, atot4434, atot4441]
  decide +kernel

theorem arows4458 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4458 = true := by
  rw [show A10K2.u4458 = KTree.node A10K2.u4450 (nat_lit 71915740) (nat_lit 11107961971) (nat_lit 0) A10K2.u4457 from rfl, allE_node, arows4450, irow4458, arows4457]
  all_goals rfl

theorem atot4458 : totK PA10K2 A10K2.u4458 = [2343825993506, 12513845083329, 24212462345624, 21380452696829, 11129636797913, 4784772357364, 1010421055992, 61110126106, 0, 0] := by
  rw [show A10K2.u4458 = KTree.node A10K2.u4450 (nat_lit 71915740) (nat_lit 11107961971) (nat_lit 0) A10K2.u4457 from rfl, totK_node, atot4450, atot4457]
  decide +kernel

theorem arows4473 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4473 = true := by
  rw [show A10K2.u4473 = KTree.node A10K2.u4465 (nat_lit 71976278) (nat_lit 10469819310) (nat_lit 0) A10K2.u4472 from rfl, allE_node, arows4465, irow4473, arows4472]
  all_goals rfl

theorem atot4473 : totK PA10K2 A10K2.u4473 = [2338931641324, 13619252898959, 28126250521042, 24099661789511, 7557107695226, 744896381106, 12475655917, 0, 0, 0] := by
  rw [show A10K2.u4473 = KTree.node A10K2.u4465 (nat_lit 71976278) (nat_lit 10469819310) (nat_lit 0) A10K2.u4472 from rfl, totK_node, atot4465, atot4472]
  decide +kernel

theorem arows4491 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4491 = true := by
  rw [show A10K2.u4491 = KTree.node A10K2.u4483 (nat_lit 72067432) (nat_lit 8656776880) (nat_lit 0) A10K2.u4490 from rfl, allE_node, arows4483, irow4491, arows4490]
  all_goals rfl

theorem atot4491 : totK PA10K2 A10K2.u4491 = [1611752829918, 10309629942251, 25078093538550, 27490770205087, 12915656590317, 2145539724865, 99925900411, 0, 0, 0] := by
  rw [show A10K2.u4491 = KTree.node A10K2.u4483 (nat_lit 72067432) (nat_lit 8656776880) (nat_lit 0) A10K2.u4490 from rfl, totK_node, atot4483, atot4490]
  decide +kernel

theorem arows4506 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4506 = true := by
  rw [show A10K2.u4506 = KTree.node A10K2.u4498 (nat_lit 72202348) (nat_lit 10246500942) (nat_lit 0) A10K2.u4505 from rfl, allE_node, arows4498, irow4506, arows4505]
  all_goals rfl

theorem atot4506 : totK PA10K2 A10K2.u4506 = [0, 2738348740810, 14707264267841, 28251930478421, 22710651545968, 7340192387451, 923786534200, 36704093874, 0, 0] := by
  rw [show A10K2.u4506 = KTree.node A10K2.u4498 (nat_lit 72202348) (nat_lit 10246500942) (nat_lit 0) A10K2.u4505 from rfl, totK_node, atot4498, atot4505]
  decide +kernel

theorem arows4522 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4522 = true := by
  rw [show A10K2.u4522 = KTree.node A10K2.u4514 (nat_lit 72275236) (nat_lit 13973624068) (nat_lit 0) A10K2.u4521 from rfl, allE_node, arows4514, irow4522, arows4521]
  all_goals rfl

theorem atot4522 : totK PA10K2 A10K2.u4522 = [301604122727, 3442322592034, 15428463391926, 29461187342251, 22681570394158, 5681749406198, 428131840815, 6239673734, 0, 0] := by
  rw [show A10K2.u4522 = KTree.node A10K2.u4514 (nat_lit 72275236) (nat_lit 13973624068) (nat_lit 0) A10K2.u4521 from rfl, totK_node, atot4514, atot4521]
  decide +kernel

theorem arows4537 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4537 = true := by
  rw [show A10K2.u4537 = KTree.node A10K2.u4529 (nat_lit 72400966) (nat_lit 13936640424) (nat_lit 0) A10K2.u4536 from rfl, allE_node, arows4529, irow4537, arows4536]
  all_goals rfl

theorem atot4537 : totK PA10K2 A10K2.u4537 = [2843989133946, 15359096509129, 28739099227691, 21965503013784, 6922915766498, 880672427879, 36196801203, 0, 0, 0] := by
  rw [show A10K2.u4537 = KTree.node A10K2.u4529 (nat_lit 72400966) (nat_lit 13936640424) (nat_lit 0) A10K2.u4536 from rfl, totK_node, atot4529, atot4536]
  decide +kernel

theorem arows4554 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4554 = true := by
  rw [show A10K2.u4554 = KTree.node A10K2.u4546 (nat_lit 72475802) (nat_lit 15217013153) (nat_lit 0) A10K2.u4553 from rfl, allE_node, arows4546, irow4554, arows4553]
  all_goals rfl

theorem atot4554 : totK PA10K2 A10K2.u4554 = [2809376952634, 14152082034082, 27001082516641, 23573998508290, 8497478217891, 1044045960991, 37204059898, 0, 0, 0] := by
  rw [show A10K2.u4554 = KTree.node A10K2.u4546 (nat_lit 72475802) (nat_lit 15217013153) (nat_lit 0) A10K2.u4553 from rfl, totK_node, atot4546, atot4553]
  decide +kernel

theorem arows4569 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4569 = true := by
  rw [show A10K2.u4569 = KTree.node A10K2.u4561 (nat_lit 72617000) (nat_lit 12795084312) (nat_lit 0) A10K2.u4568 from rfl, allE_node, arows4561, irow4569, arows4568]
  all_goals rfl

theorem atot4569 : totK PA10K2 A10K2.u4569 = [0, 6062632846493, 24116117891876, 30604498642233, 13568407623209, 1976147132119, 74979905973, 0, 0, 0] := by
  rw [show A10K2.u4569 = KTree.node A10K2.u4561 (nat_lit 72617000) (nat_lit 12795084312) (nat_lit 0) A10K2.u4568 from rfl, totK_node, atot4561, atot4568]
  decide +kernel

theorem arows4585 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4585 = true := by
  rw [show A10K2.u4585 = KTree.node A10K2.u4577 (nat_lit 72758456) (nat_lit 6314284505) (nat_lit 0) A10K2.u4584 from rfl, allE_node, arows4577, irow4585, arows4584]
  all_goals rfl

theorem atot4585 : totK PA10K2 A10K2.u4585 = [0, 3176490747594, 17633117416936, 31726287193411, 19732811450447, 3646918082841, 193743566895, 0, 0, 0] := by
  rw [show A10K2.u4585 = KTree.node A10K2.u4577 (nat_lit 72758456) (nat_lit 6314284505) (nat_lit 0) A10K2.u4584 from rfl, totK_node, atot4577, atot4584]
  decide +kernel

theorem arows4600 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4600 = true := by
  rw [show A10K2.u4600 = KTree.node A10K2.u4592 (nat_lit 72970630) (nat_lit 15746881228) (nat_lit 0) A10K2.u4599 from rfl, allE_node, arows4592, irow4600, arows4599]
  all_goals rfl

theorem atot4600 : totK PA10K2 A10K2.u4600 = [2211027775591, 12523200977551, 25826489686927, 23940780762890, 10720325754408, 2568238911836, 302818610077, 6354482628, 0, 0] := by
  rw [show A10K2.u4600 = KTree.node A10K2.u4592 (nat_lit 72970630) (nat_lit 15746881228) (nat_lit 0) A10K2.u4599 from rfl, totK_node, atot4592, atot4599]
  decide +kernel

theorem arows4620 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4620 = true := by
  rw [show A10K2.u4620 = KTree.node A10K2.u4612 (nat_lit 73104597) (nat_lit 5021260213) (nat_lit 0) A10K2.u4619 from rfl, allE_node, arows4612, irow4620, arows4619]
  all_goals rfl

theorem atot4620 : totK PA10K2 A10K2.u4620 = [2245477168038, 12733521226736, 27104996604021, 25950722127967, 10604360882347, 1343616866060, 26176060751, 0, 0, 0] := by
  rw [show A10K2.u4620 = KTree.node A10K2.u4612 (nat_lit 73104597) (nat_lit 5021260213) (nat_lit 0) A10K2.u4619 from rfl, totK_node, atot4612, atot4619]
  decide +kernel

theorem arows4635 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4635 = true := by
  rw [show A10K2.u4635 = KTree.node A10K2.u4627 (nat_lit 73234083) (nat_lit 10500319371) (nat_lit 0) A10K2.u4634 from rfl, allE_node, arows4627, irow4635, arows4634]
  all_goals rfl

theorem atot4635 : totK PA10K2 A10K2.u4635 = [0, 2803765108338, 15453039362442, 29947435015467, 23535550264422, 6737338268910, 571647212005, 7151180950, 0, 0] := by
  rw [show A10K2.u4635 = KTree.node A10K2.u4627 (nat_lit 73234083) (nat_lit 10500319371) (nat_lit 0) A10K2.u4634 from rfl, totK_node, atot4627, atot4634]
  decide +kernel

theorem arows4651 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4651 = true := by
  rw [show A10K2.u4651 = KTree.node A10K2.u4643 (nat_lit 73372430) (nat_lit 8369190303) (nat_lit 0) A10K2.u4650 from rfl, allE_node, arows4643, irow4651, arows4650]
  all_goals rfl

theorem atot4651 : totK PA10K2 A10K2.u4651 = [0, 2522612794679, 13180332271984, 26381283108313, 24944476269038, 10613358657837, 1632372015925, 73776485728, 0, 0] := by
  rw [show A10K2.u4651 = KTree.node A10K2.u4643 (nat_lit 73372430) (nat_lit 8369190303) (nat_lit 0) A10K2.u4650 from rfl, totK_node, atot4643, atot4650]
  decide +kernel

theorem arows4666 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4666 = true := by
  rw [show A10K2.u4666 = KTree.node A10K2.u4658 (nat_lit 74033928) (nat_lit 7983862248) (nat_lit 0) A10K2.u4665 from rfl, allE_node, arows4658, irow4666, arows4665]
  all_goals rfl

theorem atot4666 : totK PA10K2 A10K2.u4666 = [0, 2246707829068, 13069141798499, 27399646502715, 24344085709808, 8440554546171, 1014424354027, 37204059898, 0, 0] := by
  rw [show A10K2.u4666 = KTree.node A10K2.u4658 (nat_lit 74033928) (nat_lit 7983862248) (nat_lit 0) A10K2.u4665 from rfl, totK_node, atot4658, atot4665]
  decide +kernel

theorem arows4683 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4683 = true := by
  rw [show A10K2.u4683 = KTree.node A10K2.u4675 (nat_lit 74105356) (nat_lit 11070149331) (nat_lit 0) A10K2.u4682 from rfl, allE_node, arows4675, irow4683, arows4682]
  all_goals rfl

theorem atot4683 : totK PA10K2 A10K2.u4683 = [0, 3169975078601, 16775566539710, 30602914872874, 21586581813630, 5002454192208, 366506290026, 6354482628, 0, 0] := by
  rw [show A10K2.u4683 = KTree.node A10K2.u4675 (nat_lit 74105356) (nat_lit 11070149331) (nat_lit 0) A10K2.u4682 from rfl, totK_node, atot4675, atot4682]
  decide +kernel

theorem arows4698 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4698 = true := by
  rw [show A10K2.u4698 = KTree.node A10K2.u4690 (nat_lit 74186708) (nat_lit 5030814441) (nat_lit 0) A10K2.u4697 from rfl, allE_node, arows4690, irow4698, arows4697]
  all_goals rfl

theorem atot4698 : totK PA10K2 A10K2.u4698 = [0, 0, 4827337904972, 21885518434036, 32294071263818, 16772493266380, 2565557383827, 93148485416, 0, 0] := by
  rw [show A10K2.u4698 = KTree.node A10K2.u4690 (nat_lit 74186708) (nat_lit 5030814441) (nat_lit 0) A10K2.u4697 from rfl, totK_node, atot4690, atot4697]
  decide +kernel

theorem arows4714 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4714 = true := by
  rw [show A10K2.u4714 = KTree.node A10K2.u4706 (nat_lit 74322176) (nat_lit 15049380543) (nat_lit 0) A10K2.u4713 from rfl, allE_node, arows4706, irow4714, arows4713]
  all_goals rfl

theorem atot4714 : totK PA10K2 A10K2.u4714 = [0, 0, 2052502608483, 12955651877205, 28002550430794, 23778382243308, 7654927988161, 964397916948, 36704093874, 0] := by
  rw [show A10K2.u4714 = KTree.node A10K2.u4706 (nat_lit 74322176) (nat_lit 15049380543) (nat_lit 0) A10K2.u4713 from rfl, totK_node, atot4706, atot4713]
  decide +kernel

theorem arows4729 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4729 = true := by
  rw [show A10K2.u4729 = KTree.node A10K2.u4721 (nat_lit 74413212) (nat_lit 10571197638) (nat_lit 0) A10K2.u4728 from rfl, allE_node, arows4721, irow4729, arows4728]
  all_goals rfl

theorem atot4729 : totK PA10K2 A10K2.u4729 = [0, 1538660793789, 9814546661405, 23164882441618, 25672012122351, 14122939749640, 3367307032893, 305593688304, 5982052406, 0] := by
  rw [show A10K2.u4729 = KTree.node A10K2.u4721 (nat_lit 74413212) (nat_lit 10571197638) (nat_lit 0) A10K2.u4728 from rfl, totK_node, atot4721, atot4728]
  decide +kernel

theorem arows4747 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4747 = true := by
  rw [show A10K2.u4747 = KTree.node A10K2.u4739 (nat_lit 74537636) (nat_lit 13642311797) (nat_lit 0) A10K2.u4746 from rfl, allE_node, arows4739, irow4747, arows4746]
  all_goals rfl

theorem atot4747 : totK PA10K2 A10K2.u4747 = [0, 2161736226052, 12462849505598, 26730993867420, 24984661579807, 9051439378706, 1153215683749, 42750364871, 0, 0] := by
  rw [show A10K2.u4747 = KTree.node A10K2.u4739 (nat_lit 74537636) (nat_lit 13642311797) (nat_lit 0) A10K2.u4746 from rfl, totK_node, atot4739, atot4746]
  decide +kernel

theorem arows4762 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4762 = true := by
  rw [show A10K2.u4762 = KTree.node A10K2.u4754 (nat_lit 74599084) (nat_lit 13092961586) (nat_lit 0) A10K2.u4761 from rfl, allE_node, arows4754, irow4762, arows4761]
  all_goals rfl

theorem atot4762 : totK PA10K2 A10K2.u4762 = [0, 2254573189466, 13933634250183, 29352479823892, 23929918243903, 6455504752438, 548751584041, 6354482628, 0, 0] := by
  rw [show A10K2.u4762 = KTree.node A10K2.u4754 (nat_lit 74599084) (nat_lit 13092961586) (nat_lit 0) A10K2.u4761 from rfl, totK_node, atot4754, atot4761]
  decide +kernel

theorem arows4778 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4778 = true := by
  rw [show A10K2.u4778 = KTree.node A10K2.u4770 (nat_lit 74795222) (nat_lit 12138754253) (nat_lit 0) A10K2.u4777 from rfl, allE_node, arows4770, irow4778, arows4777]
  all_goals rfl

theorem atot4778 : totK PA10K2 A10K2.u4778 = [0, 0, 4354369618590, 21035660450277, 32596315207694, 16161645164357, 2258462298388, 87001189349, 0, 0] := by
  rw [show A10K2.u4778 = KTree.node A10K2.u4770 (nat_lit 74795222) (nat_lit 12138754253) (nat_lit 0) A10K2.u4777 from rfl, totK_node, atot4770, atot4777]
  decide +kernel

theorem arows4793 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4793 = true := by
  rw [show A10K2.u4793 = KTree.node A10K2.u4785 (nat_lit 74898216) (nat_lit 11223243644) (nat_lit 0) A10K2.u4792 from rfl, allE_node, arows4785, irow4793, arows4792]
  all_goals rfl

theorem atot4793 : totK PA10K2 A10K2.u4793 = [0, 2207301526707, 11123410181193, 22286970511260, 23753103873904, 13457338846175, 3306249775399, 308223447225, 6354482628, 0] := by
  rw [show A10K2.u4793 = KTree.node A10K2.u4785 (nat_lit 74898216) (nat_lit 11223243644) (nat_lit 0) A10K2.u4792 from rfl, totK_node, atot4785, atot4792]
  decide +kernel

theorem arows4810 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4810 = true := by
  rw [show A10K2.u4810 = KTree.node A10K2.u4802 (nat_lit 75173843) (nat_lit 8992610161) (nat_lit 0) A10K2.u4809 from rfl, allE_node, arows4802, irow4810, arows4809]
  all_goals rfl

theorem atot4810 : totK PA10K2 A10K2.u4810 = [0, 2243738283378, 13158380980069, 28028902171441, 25425786697825, 8999477584277, 1074678154260, 36968589557, 0, 0] := by
  rw [show A10K2.u4810 = KTree.node A10K2.u4802 (nat_lit 75173843) (nat_lit 8992610161) (nat_lit 0) A10K2.u4809 from rfl, totK_node, atot4802, atot4809]
  decide +kernel

theorem arows4825 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4825 = true := by
  rw [show A10K2.u4825 = KTree.node A10K2.u4817 (nat_lit 75499554) (nat_lit 8147872920) (nat_lit 0) A10K2.u4824 from rfl, allE_node, arows4817, irow4825, arows4824]
  all_goals rfl

theorem atot4825 : totK PA10K2 A10K2.u4825 = [2218643274008, 10626087448896, 18832915600180, 18974717252203, 16814357391697, 9158336745421, 1632695547828, 74789331576, 0, 0] := by
  rw [show A10K2.u4825 = KTree.node A10K2.u4817 (nat_lit 75499554) (nat_lit 8147872920) (nat_lit 0) A10K2.u4824 from rfl, totK_node, atot4817, atot4824]
  decide +kernel

theorem arows4841 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4841 = true := by
  rw [show A10K2.u4841 = KTree.node A10K2.u4833 (nat_lit 75632903) (nat_lit 10278940516) (nat_lit 0) A10K2.u4840 from rfl, allE_node, arows4833, irow4841, arows4840]
  all_goals rfl

theorem atot4841 : totK PA10K2 A10K2.u4841 = [2157467152652, 12950283532132, 27647001084272, 24486689583214, 8202721590793, 983476350225, 36196801203, 0, 0, 0] := by
  rw [show A10K2.u4841 = KTree.node A10K2.u4833 (nat_lit 75632903) (nat_lit 10278940516) (nat_lit 0) A10K2.u4840 from rfl, totK_node, atot4833, atot4840]
  decide +kernel

theorem arows4856 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4856 = true := by
  rw [show A10K2.u4856 = KTree.node A10K2.u4848 (nat_lit 75723660) (nat_lit 8029642609) (nat_lit 0) A10K2.u4855 from rfl, allE_node, arows4848, irow4856, arows4855]
  all_goals rfl

theorem atot4856 : totK PA10K2 A10K2.u4856 = [1364381863375, 9662468823852, 25025861890271, 27844993371286, 12154031496319, 1955169665590, 93583569434, 0, 0, 0] := by
  rw [show A10K2.u4856 = KTree.node A10K2.u4848 (nat_lit 75723660) (nat_lit 8029642609) (nat_lit 0) A10K2.u4855 from rfl, totK_node, atot4848, atot4855]
  decide +kernel

theorem arows4875 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4875 = true := by
  rw [show A10K2.u4875 = KTree.node A10K2.u4867 (nat_lit 75798533) (nat_lit 6744654663) (nat_lit 0) A10K2.u4874 from rfl, allE_node, arows4867, irow4875, arows4874]
  all_goals rfl

theorem atot4875 : totK PA10K2 A10K2.u4875 = [0, 2708277779533, 14356100271644, 27898330019619, 22964167299348, 7355135677097, 924330417212, 36134558889, 0, 0] := by
  rw [show A10K2.u4875 = KTree.node A10K2.u4867 (nat_lit 75798533) (nat_lit 6744654663) (nat_lit 0) A10K2.u4874 from rfl, totK_node, atot4867, atot4874]
  decide +kernel

theorem arows4890 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4890 = true := by
  rw [show A10K2.u4890 = KTree.node A10K2.u4882 (nat_lit 75945130) (nat_lit 12978655923) (nat_lit 0) A10K2.u4889 from rfl, allE_node, arows4882, irow4890, arows4889]
  all_goals rfl

theorem atot4890 : totK PA10K2 A10K2.u4890 = [848323660542, 5606629964362, 17622178244080, 28264145033592, 19463563671942, 4689043109131, 361411662005, 5676195732, 0, 0] := by
  rw [show A10K2.u4890 = KTree.node A10K2.u4882 (nat_lit 75945130) (nat_lit 12978655923) (nat_lit 0) A10K2.u4889 from rfl, totK_node, atot4882, atot4889]
  decide +kernel

theorem arows4906 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4906 = true := by
  rw [show A10K2.u4906 = KTree.node A10K2.u4898 (nat_lit 76133880) (nat_lit 5565562067) (nat_lit 0) A10K2.u4905 from rfl, allE_node, arows4898, irow4906, arows4905]
  all_goals rfl

theorem atot4906 : totK PA10K2 A10K2.u4906 = [2517737300429, 13728921748731, 27442937826363, 23895838755419, 8399192793320, 1023723808539, 37204059898, 0, 0, 0] := by
  rw [show A10K2.u4906 = KTree.node A10K2.u4898 (nat_lit 76133880) (nat_lit 5565562067) (nat_lit 0) A10K2.u4905 from rfl, totK_node, atot4898, atot4905]
  decide +kernel

theorem arows4921 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4921 = true := by
  rw [show A10K2.u4921 = KTree.node A10K2.u4913 (nat_lit 76203298) (nat_lit 13563626043) (nat_lit 0) A10K2.u4920 from rfl, allE_node, arows4913, irow4921, arows4920]
  all_goals rfl

theorem atot4921 : totK PA10K2 A10K2.u4921 = [2387167619127, 14423690692180, 29881179471486, 24082216329849, 6475971521369, 539292035681, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u4921 = KTree.node A10K2.u4913 (nat_lit 76203298) (nat_lit 13563626043) (nat_lit 0) A10K2.u4920 from rfl, totK_node, atot4913, atot4920]
  decide +kernel

theorem arows4938 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4938 = true := by
  rw [show A10K2.u4938 = KTree.node A10K2.u4930 (nat_lit 76367516) (nat_lit 11283911090) (nat_lit 0) A10K2.u4937 from rfl, allE_node, arows4930, irow4938, arows4937]
  all_goals rfl

theorem atot4938 : totK PA10K2 A10K2.u4938 = [0, 3153256514527, 16552389803919, 29747852771442, 21366738660514, 6104927473575, 734175604147, 31018567651, 0, 0] := by
  rw [show A10K2.u4938 = KTree.node A10K2.u4930 (nat_lit 76367516) (nat_lit 11283911090) (nat_lit 0) A10K2.u4937 from rfl, totK_node, atot4930, atot4937]
  decide +kernel

theorem arows4953 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4953 = true := by
  rw [show A10K2.u4953 = KTree.node A10K2.u4945 (nat_lit 76431752) (nat_lit 13971632595) (nat_lit 0) A10K2.u4952 from rfl, allE_node, arows4945, irow4953, arows4952]
  all_goals rfl

theorem atot4953 : totK PA10K2 A10K2.u4953 = [0, 2463751467192, 13902932212108, 28420073981050, 23771128451101, 6784822884280, 617934185074, 11925199957, 0, 0] := by
  rw [show A10K2.u4953 = KTree.node A10K2.u4945 (nat_lit 76431752) (nat_lit 13971632595) (nat_lit 0) A10K2.u4952 from rfl, totK_node, atot4945, atot4952]
  decide +kernel

theorem arows4969 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4969 = true := by
  rw [show A10K2.u4969 = KTree.node A10K2.u4961 (nat_lit 76562530) (nat_lit 7628563438) (nat_lit 0) A10K2.u4968 from rfl, allE_node, arows4961, irow4969, arows4968]
  all_goals rfl

theorem atot4969 : totK PA10K2 A10K2.u4969 = [2045425524865, 11672574880120, 25029673057611, 24924905565236, 11522130341225, 2165937296293, 118036528791, 0, 0, 0] := by
  rw [show A10K2.u4969 = KTree.node A10K2.u4961 (nat_lit 76562530) (nat_lit 7628563438) (nat_lit 0) A10K2.u4968 from rfl, totK_node, atot4961, atot4968]
  decide +kernel

theorem arows4984 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u4984 = true := by
  rw [show A10K2.u4984 = KTree.node A10K2.u4976 (nat_lit 76634145) (nat_lit 9876898653) (nat_lit 0) A10K2.u4983 from rfl, allE_node, arows4976, irow4984, arows4983]
  all_goals rfl

theorem atot4984 : totK PA10K2 A10K2.u4984 = [2052442624241, 12144668686254, 26557702171923, 25241492752762, 9404095048232, 1200433447687, 42750364871, 0, 0, 0] := by
  rw [show A10K2.u4984 = KTree.node A10K2.u4976 (nat_lit 76634145) (nat_lit 9876898653) (nat_lit 0) A10K2.u4983 from rfl, totK_node, atot4976, atot4983]
  decide +kernel

theorem arows5002 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5002 = true := by
  rw [show A10K2.u5002 = KTree.node A10K2.u4994 (nat_lit 76695872) (nat_lit 14090601422) (nat_lit 0) A10K2.u5001 from rfl, allE_node, arows4994, irow5002, arows5001]
  all_goals rfl

theorem atot5002 : totK PA10K2 A10K2.u5002 = [2343832716771, 14095285210297, 29204276452432, 23732169020727, 6503017323892, 553017962538, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u5002 = KTree.node A10K2.u4994 (nat_lit 76695872) (nat_lit 14090601422) (nat_lit 0) A10K2.u5001 from rfl, totK_node, atot4994, atot5001]
  decide +kernel

theorem arows5017 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5017 = true := by
  rw [show A10K2.u5017 = KTree.node A10K2.u5009 (nat_lit 76885726) (nat_lit 11283310526) (nat_lit 0) A10K2.u5016 from rfl, allE_node, arows5009, irow5017, arows5016]
  all_goals rfl

theorem atot5017 : totK PA10K2 A10K2.u5017 = [0, 4292319367356, 20404780505843, 31670008065008, 17166912266469, 2821914914190, 113410386985, 0, 0, 0] := by
  rw [show A10K2.u5017 = KTree.node A10K2.u5009 (nat_lit 76885726) (nat_lit 11283310526) (nat_lit 0) A10K2.u5016 from rfl, totK_node, atot5009, atot5016]
  decide +kernel

theorem arows5033 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5033 = true := by
  rw [show A10K2.u5033 = KTree.node A10K2.u5025 (nat_lit 76982035) (nat_lit 10800824107) (nat_lit 0) A10K2.u5032 from rfl, allE_node, arows5025, irow5033, arows5032]
  all_goals rfl

theorem atot5033 : totK PA10K2 A10K2.u5033 = [0, 3188435790636, 16457082775518, 29655036097161, 20529167829331, 4951034650305, 452258175328, 6354482628, 0, 0] := by
  rw [show A10K2.u5033 = KTree.node A10K2.u5025 (nat_lit 76982035) (nat_lit 10800824107) (nat_lit 0) A10K2.u5032 from rfl, totK_node, atot5025, atot5032]
  decide +kernel

theorem arows5048 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5048 = true := by
  rw [show A10K2.u5048 = KTree.node A10K2.u5040 (nat_lit 77646162) (nat_lit 12652768578) (nat_lit 0) A10K2.u5047 from rfl, allE_node, arows5040, irow5048, arows5047]
  all_goals rfl

theorem atot5048 : totK PA10K2 A10K2.u5048 = [0, 2237920936433, 13227414745336, 27920466630373, 24356480655972, 8088762783646, 970393817827, 36196801203, 0, 0] := by
  rw [show A10K2.u5048 = KTree.node A10K2.u5040 (nat_lit 77646162) (nat_lit 12652768578) (nat_lit 0) A10K2.u5047 from rfl, totK_node, atot5040, atot5047]
  decide +kernel

theorem arows5065 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5065 = true := by
  rw [show A10K2.u5065 = KTree.node A10K2.u5057 (nat_lit 77791852) (nat_lit 10805342613) (nat_lit 0) A10K2.u5064 from rfl, allE_node, arows5057, irow5065, arows5064]
  all_goals rfl

theorem atot5065 : totK PA10K2 A10K2.u5065 = [0, 1903771529870, 12575548675777, 28463897734491, 25638787446019, 8062044569566, 813961934525, 13259410892, 0, 0] := by
  rw [show A10K2.u5065 = KTree.node A10K2.u5057 (nat_lit 77791852) (nat_lit 10805342613) (nat_lit 0) A10K2.u5064 from rfl, totK_node, atot5057, atot5064]
  decide +kernel

theorem arows5080 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5080 = true := by
  rw [show A10K2.u5080 = KTree.node A10K2.u5072 (nat_lit 78214819) (nat_lit 10500319371) (nat_lit 0) A10K2.u5079 from rfl, allE_node, arows5072, irow5080, arows5079]
  all_goals rfl

theorem atot5080 : totK PA10K2 A10K2.u5080 = [0, 2495991777478, 13600932080121, 27369533055790, 24214015708436, 8557610185965, 1024750240107, 37204059898, 0, 0] := by
  rw [show A10K2.u5080 = KTree.node A10K2.u5072 (nat_lit 78214819) (nat_lit 10500319371) (nat_lit 0) A10K2.u5079 from rfl, totK_node, atot5072, atot5079]
  decide +kernel

theorem arows5096 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5096 = true := by
  rw [show A10K2.u5096 = KTree.node A10K2.u5088 (nat_lit 78284868) (nat_lit 11665821275) (nat_lit 0) A10K2.u5095 from rfl, allE_node, arows5088, irow5096, arows5095]
  all_goals rfl

theorem atot5096 : totK PA10K2 A10K2.u5096 = [0, 2942518006066, 15758445761120, 29709005075924, 22142207717861, 5633921411302, 486990716983, 6354482628, 0, 0] := by
  rw [show A10K2.u5096 = KTree.node A10K2.u5088 (nat_lit 78284868) (nat_lit 11665821275) (nat_lit 0) A10K2.u5095 from rfl, totK_node, atot5088, atot5095]
  decide +kernel

theorem arows5111 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5111 = true := by
  rw [show A10K2.u5111 = KTree.node A10K2.u5103 (nat_lit 78649444) (nat_lit 13454323247) (nat_lit 0) A10K2.u5110 from rfl, allE_node, arows5103, irow5111, arows5110]
  all_goals rfl

theorem atot5111 : totK PA10K2 A10K2.u5111 = [0, 2348796189751, 13619363533561, 28160431348074, 24335458870667, 8220872278829, 967758161246, 37267903822, 0, 0] := by
  rw [show A10K2.u5111 = KTree.node A10K2.u5103 (nat_lit 78649444) (nat_lit 13454323247) (nat_lit 0) A10K2.u5110 from rfl, totK_node, atot5103, atot5110]
  decide +kernel

theorem arows5132 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5132 = true := by
  rw [show A10K2.u5132 = KTree.node A10K2.u5124 (nat_lit 78729554) (nat_lit 13033647448) (nat_lit 0) A10K2.u5131 from rfl, allE_node, arows5124, irow5132, arows5131]
  all_goals rfl

theorem atot5132 : totK PA10K2 A10K2.u5132 = [0, 2048380810550, 12183965568000, 26968714163920, 25356531475654, 8709309301876, 1038371814839, 36194129389, 0, 0] := by
  rw [show A10K2.u5132 = KTree.node A10K2.u5124 (nat_lit 78729554) (nat_lit 13033647448) (nat_lit 0) A10K2.u5131 from rfl, totK_node, atot5124, atot5131]
  decide +kernel

theorem arows5147 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5147 = true := by
  rw [show A10K2.u5147 = KTree.node A10K2.u5139 (nat_lit 78793248) (nat_lit 13715175604) (nat_lit 0) A10K2.u5146 from rfl, allE_node, arows5139, irow5147, arows5146]
  all_goals rfl

theorem atot5147 : totK PA10K2 A10K2.u5147 = [0, 2332949133701, 14181845841717, 29421621288548, 23526300494031, 6019002882505, 515191621575, 6354482628, 0, 0] := by
  rw [show A10K2.u5147 = KTree.node A10K2.u5139 (nat_lit 78793248) (nat_lit 13715175604) (nat_lit 0) A10K2.u5146 from rfl, totK_node, atot5139, atot5146]
  decide +kernel

theorem arows5163 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5163 = true := by
  rw [show A10K2.u5163 = KTree.node A10K2.u5155 (nat_lit 78985883) (nat_lit 9946235799) (nat_lit 0) A10K2.u5162 from rfl, allE_node, arows5155, irow5163, arows5162]
  all_goals rfl

theorem atot5163 : totK PA10K2 A10K2.u5163 = [0, 0, 4974538886097, 22141737086373, 31587199232169, 14621966689180, 2187439822484, 104190109466, 0, 0] := by
  rw [show A10K2.u5163 = KTree.node A10K2.u5155 (nat_lit 78985883) (nat_lit 9946235799) (nat_lit 0) A10K2.u5162 from rfl, totK_node, atot5155, atot5162]
  decide +kernel

theorem arows5178 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5178 = true := by
  rw [show A10K2.u5178 = KTree.node A10K2.u5170 (nat_lit 79088411) (nat_lit 8657443410) (nat_lit 0) A10K2.u5177 from rfl, allE_node, arows5170, irow5178, arows5177]
  all_goals rfl

theorem atot5178 : totK PA10K2 A10K2.u5178 = [0, 2338692983822, 10614009437805, 20228842752262, 22842281361290, 14478360033274, 4047879462292, 415966008549, 6354482628, 0] := by
  rw [show A10K2.u5178 = KTree.node A10K2.u5170 (nat_lit 79088411) (nat_lit 8657443410) (nat_lit 0) A10K2.u5177 from rfl, totK_node, atot5170, atot5177]
  decide +kernel

theorem arows5195 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5195 = true := by
  rw [show A10K2.u5195 = KTree.node A10K2.u5187 (nat_lit 83944904) (nat_lit 12729350791) (nat_lit 0) A10K2.u5194 from rfl, allE_node, arows5187, irow5195, arows5194]
  all_goals rfl

theorem atot5195 : totK PA10K2 A10K2.u5195 = [0, 2056441471990, 12844197783311, 27684569021854, 24572041228958, 8332932212155, 985248287330, 36196801203, 0, 0] := by
  rw [show A10K2.u5195 = KTree.node A10K2.u5187 (nat_lit 83944904) (nat_lit 12729350791) (nat_lit 0) A10K2.u5194 from rfl, totK_node, atot5187, atot5194]
  decide +kernel

theorem arows5210 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5210 = true := by
  rw [show A10K2.u5210 = KTree.node A10K2.u5202 (nat_lit 84089399) (nat_lit 11298208646) (nat_lit 0) A10K2.u5209 from rfl, allE_node, arows5202, irow5210, arows5209]
  all_goals rfl

theorem atot5210 : totK PA10K2 A10K2.u5210 = [0, 1888417489703, 12065890700121, 27872652832140, 26517044335796, 8973103598215, 895600106344, 13259410892, 0, 0] := by
  rw [show A10K2.u5210 = KTree.node A10K2.u5202 (nat_lit 84089399) (nat_lit 11298208646) (nat_lit 0) A10K2.u5209 from rfl, totK_node, atot5202, atot5209]
  decide +kernel

theorem arows5226 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5226 = true := by
  rw [show A10K2.u5226 = KTree.node A10K2.u5218 (nat_lit 84168782) (nat_lit 10386679269) (nat_lit 0) A10K2.u5225 from rfl, allE_node, arows5218, irow5226, arows5225]
  all_goals rfl

theorem atot5226 : totK PA10K2 A10K2.u5226 = [0, 0, 3131977466728, 16265507069174, 29555944179508, 21346479991333, 5929383505536, 718035835364, 30605747850, 0] := by
  rw [show A10K2.u5226 = KTree.node A10K2.u5218 (nat_lit 84168782) (nat_lit 10386679269) (nat_lit 0) A10K2.u5225 from rfl, totK_node, atot5218, atot5225]
  decide +kernel

theorem arows5241 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5241 = true := by
  rw [show A10K2.u5241 = KTree.node A10K2.u5233 (nat_lit 84297777) (nat_lit 9560489884) (nat_lit 0) A10K2.u5240 from rfl, allE_node, arows5233, irow5241, arows5240]
  all_goals rfl

theorem atot5241 : totK PA10K2 A10K2.u5241 = [0, 0, 2861731879039, 15338960968872, 29021231993765, 21973631851142, 5994828964057, 551627425362, 11205006771, 0] := by
  rw [show A10K2.u5241 = KTree.node A10K2.u5233 (nat_lit 84297777) (nat_lit 9560489884) (nat_lit 0) A10K2.u5240 from rfl, totK_node, atot5233, atot5240]
  decide +kernel

theorem arows5259 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5259 = true := by
  rw [show A10K2.u5259 = KTree.node A10K2.u5251 (nat_lit 84942284) (nat_lit 6383717942) (nat_lit 0) A10K2.u5258 from rfl, allE_node, arows5251, irow5259, arows5258]
  all_goals rfl

theorem atot5259 : totK PA10K2 A10K2.u5259 = [0, 2155773174296, 12011103690899, 25307780067241, 25042175098152, 11326260526925, 1915720307035, 92504676549, 0, 0] := by
  rw [show A10K2.u5259 = KTree.node A10K2.u5251 (nat_lit 84942284) (nat_lit 6383717942) (nat_lit 0) A10K2.u5258 from rfl, totK_node, atot5251, atot5258]
  decide +kernel

theorem arows5274 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5274 = true := by
  rw [show A10K2.u5274 = KTree.node A10K2.u5266 (nat_lit 85020954) (nat_lit 12688060200) (nat_lit 0) A10K2.u5273 from rfl, allE_node, arows5266, irow5274, arows5273]
  all_goals rfl

theorem atot5274 : totK PA10K2 A10K2.u5274 = [0, 2304591608535, 12982698369024, 27121460376334, 24551373815074, 8808708001905, 1072956964326, 42750364871, 0, 0] := by
  rw [show A10K2.u5274 = KTree.node A10K2.u5266 (nat_lit 85020954) (nat_lit 12688060200) (nat_lit 0) A10K2.u5273 from rfl, totK_node, atot5266, atot5273]
  decide +kernel

theorem arows5290 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5290 = true := by
  rw [show A10K2.u5290 = KTree.node A10K2.u5282 (nat_lit 85108055) (nat_lit 6118585603) (nat_lit 0) A10K2.u5289 from rfl, allE_node, arows5282, irow5290, arows5289]
  all_goals rfl

theorem atot5290 : totK PA10K2 A10K2.u5290 = [0, 1491872713986, 11025213484189, 27012708829125, 26217875565131, 9174047058055, 1110308253822, 37172849495, 0, 0] := by
  rw [show A10K2.u5290 = KTree.node A10K2.u5282 (nat_lit 85108055) (nat_lit 6118585603) (nat_lit 0) A10K2.u5289 from rfl, totK_node, atot5282, atot5289]
  decide +kernel

theorem arows5305 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5305 = true := by
  rw [show A10K2.u5305 = KTree.node A10K2.u5297 (nat_lit 85283180) (nat_lit 12674247042) (nat_lit 0) A10K2.u5304 from rfl, allE_node, arows5297, irow5305, arows5304]
  all_goals rfl

theorem atot5305 : totK PA10K2 A10K2.u5305 = [0, 0, 4535636867120, 21118142242549, 31929089905384, 16322817269734, 2506881163859, 112093215346, 0, 0] := by
  rw [show A10K2.u5305 = KTree.node A10K2.u5297 (nat_lit 85283180) (nat_lit 12674247042) (nat_lit 0) A10K2.u5304 from rfl, totK_node, atot5297, atot5304]
  decide +kernel

theorem arows5322 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5322 = true := by
  rw [show A10K2.u5322 = KTree.node A10K2.u5314 (nat_lit 85463392) (nat_lit 12824100409) (nat_lit 0) A10K2.u5321 from rfl, allE_node, arows5314, irow5322, arows5321]
  all_goals rfl

theorem atot5322 : totK PA10K2 A10K2.u5322 = [0, 2205441570080, 11109056056171, 22203512152396, 23476399306633, 13729574796084, 3654757849837, 384962563863, 6354482628, 0] := by
  rw [show A10K2.u5322 = KTree.node A10K2.u5314 (nat_lit 85463392) (nat_lit 12824100409) (nat_lit 0) A10K2.u5321 from rfl, totK_node, atot5314, atot5321]
  decide +kernel

theorem arows5337 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5337 = true := by
  rw [show A10K2.u5337 = KTree.node A10K2.u5329 (nat_lit 85665495) (nat_lit 10127825238) (nat_lit 0) A10K2.u5336 from rfl, allE_node, arows5329, irow5337, arows5336]
  all_goals rfl

theorem atot5337 : totK PA10K2 A10K2.u5337 = [0, 2243860048398, 12791747182959, 27101273537967, 25490129851319, 9806994977198, 1291124800296, 43101729467, 0, 0] := by
  rw [show A10K2.u5337 = KTree.node A10K2.u5329 (nat_lit 85665495) (nat_lit 10127825238) (nat_lit 0) A10K2.u5336 from rfl, totK_node, atot5329, atot5336]
  decide +kernel

theorem arows5353 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5353 = true := by
  rw [show A10K2.u5353 = KTree.node A10K2.u5345 (nat_lit 85728008) (nat_lit 12416319108) (nat_lit 0) A10K2.u5352 from rfl, allE_node, arows5345, irow5353, arows5352]
  all_goals rfl

theorem atot5353 : totK PA10K2 A10K2.u5353 = [0, 0, 3489325574319, 17599912046262, 30630297893046, 21116808821030, 5323074639398, 468440793693, 7007974415, 0] := by
  rw [show A10K2.u5353 = KTree.node A10K2.u5345 (nat_lit 85728008) (nat_lit 12416319108) (nat_lit 0) A10K2.u5352 from rfl, totK_node, atot5345, atot5352]
  decide +kernel

theorem arows5368 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5368 = true := by
  rw [show A10K2.u5368 = KTree.node A10K2.u5360 (nat_lit 85945348) (nat_lit 9189952623) (nat_lit 0) A10K2.u5367 from rfl, allE_node, arows5360, irow5368, arows5367]
  all_goals rfl

theorem atot5368 : totK PA10K2 A10K2.u5368 = [0, 1600415090483, 9680924121573, 22905493700309, 26728799691132, 14889161031315, 2845215226998, 136912387279, 0, 0] := by
  rw [show A10K2.u5368 = KTree.node A10K2.u5360 (nat_lit 85945348) (nat_lit 9189952623) (nat_lit 0) A10K2.u5367 from rfl, totK_node, atot5360, atot5367]
  decide +kernel

theorem arows5387 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5387 = true := by
  rw [show A10K2.u5387 = KTree.node A10K2.u5379 (nat_lit 88724712) (nat_lit 4544092738) (nat_lit 0) A10K2.u5386 from rfl, allE_node, arows5379, irow5387, arows5386]
  all_goals rfl

theorem atot5387 : totK PA10K2 A10K2.u5387 = [0, 2503532627413, 13340077371246, 26976222932418, 24412712647322, 8776037129780, 1041610797094, 37204059898, 0, 0] := by
  rw [show A10K2.u5387 = KTree.node A10K2.u5379 (nat_lit 88724712) (nat_lit 4544092738) (nat_lit 0) A10K2.u5386 from rfl, totK_node, atot5379, atot5386]
  decide +kernel

theorem arows5402 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5402 = true := by
  rw [show A10K2.u5402 = KTree.node A10K2.u5394 (nat_lit 88810781) (nat_lit 6271232542) (nat_lit 0) A10K2.u5401 from rfl, allE_node, arows5394, irow5402, arows5401]
  all_goals rfl

theorem atot5402 : totK PA10K2 A10K2.u5402 = [0, 2190562746852, 13774341956134, 29507330654332, 24854011666915, 7231210742395, 623219714744, 6354482628, 0, 0] := by
  rw [show A10K2.u5402 = KTree.node A10K2.u5394 (nat_lit 88810781) (nat_lit 6271232542) (nat_lit 0) A10K2.u5401 from rfl, totK_node, atot5394, atot5401]
  decide +kernel

theorem arows5418 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5418 = true := by
  rw [show A10K2.u5418 = KTree.node A10K2.u5410 (nat_lit 88949000) (nat_lit 11083052107) (nat_lit 0) A10K2.u5417 from rfl, allE_node, arows5410, irow5418, arows5417]
  all_goals rfl

theorem atot5418 : totK PA10K2 A10K2.u5418 = [0, 0, 3365867360228, 17197844521835, 30270776978357, 20943229137577, 5535755208033, 618870829240, 25565504801, 0] := by
  rw [show A10K2.u5418 = KTree.node A10K2.u5410 (nat_lit 88949000) (nat_lit 11083052107) (nat_lit 0) A10K2.u5417 from rfl, totK_node, atot5410, atot5417]
  decide +kernel

theorem arows5433 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5433 = true := by
  rw [show A10K2.u5433 = KTree.node A10K2.u5425 (nat_lit 89012513) (nat_lit 9173356087) (nat_lit 0) A10K2.u5432 from rfl, allE_node, arows5425, irow5433, arows5432]
  all_goals rfl

theorem atot5433 : totK PA10K2 A10K2.u5433 = [0, 0, 2179063574147, 13304115953717, 28592386499905, 24133407082704, 6969310095807, 691503179575, 17378262807, 0] := by
  rw [show A10K2.u5433 = KTree.node A10K2.u5425 (nat_lit 89012513) (nat_lit 9173356087) (nat_lit 0) A10K2.u5432 from rfl, totK_node, atot5425, atot5432]
  decide +kernel

theorem arows5450 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5450 = true := by
  rw [show A10K2.u5450 = KTree.node A10K2.u5442 (nat_lit 89132038) (nat_lit 15264674383) (nat_lit 0) A10K2.u5449 from rfl, allE_node, arows5442, irow5450, arows5449]
  all_goals rfl

theorem atot5450 : totK PA10K2 A10K2.u5450 = [0, 1538660793789, 10312668256632, 24987581113320, 26673429722421, 12517708911022, 2166576457789, 104810682555, 0, 0] := by
  rw [show A10K2.u5450 = KTree.node A10K2.u5442 (nat_lit 89132038) (nat_lit 15264674383) (nat_lit 0) A10K2.u5449 from rfl, totK_node, atot5442, atot5449]
  decide +kernel

theorem arows5465 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5465 = true := by
  rw [show A10K2.u5465 = KTree.node A10K2.u5457 (nat_lit 89222775) (nat_lit 14483952203) (nat_lit 0) A10K2.u5464 from rfl, allE_node, arows5457, irow5465, arows5464]
  all_goals rfl

theorem atot5465 : totK PA10K2 A10K2.u5465 = [0, 2161736226052, 12320422829160, 26521717260510, 25238707277601, 9402400853677, 1164333578990, 42750364871, 0, 0] := by
  rw [show A10K2.u5465 = KTree.node A10K2.u5457 (nat_lit 89222775) (nat_lit 14483952203) (nat_lit 0) A10K2.u5464 from rfl, totK_node, atot5457, atot5464]
  decide +kernel

theorem arows5481 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5481 = true := by
  rw [show A10K2.u5481 = KTree.node A10K2.u5473 (nat_lit 89282881) (nat_lit 9660119737) (nat_lit 0) A10K2.u5480 from rfl, allE_node, arows5473, irow5481, arows5480]
  all_goals rfl

theorem atot5481 : totK PA10K2 A10K2.u5481 = [0, 2254573189466, 13447819416455, 28222694747426, 24088830902425, 7493579521951, 833781116820, 31725663621, 0, 0] := by
  rw [show A10K2.u5481 = KTree.node A10K2.u5473 (nat_lit 89282881) (nat_lit 9660119737) (nat_lit 0) A10K2.u5480 from rfl, totK_node, atot5473, atot5480]
  decide +kernel

theorem arows5496 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5496 = true := by
  rw [show A10K2.u5496 = KTree.node A10K2.u5488 (nat_lit 89477474) (nat_lit 10815490172) (nat_lit 0) A10K2.u5495 from rfl, allE_node, arows5488, irow5496, arows5495]
  all_goals rfl

theorem atot5496 : totK PA10K2 A10K2.u5496 = [0, 0, 4354369618590, 20435705466646, 31756034264448, 17170703212118, 2739657177990, 117649795563, 0, 0] := by
  rw [show A10K2.u5496 = KTree.node A10K2.u5488 (nat_lit 89477474) (nat_lit 10815490172) (nat_lit 0) A10K2.u5495 from rfl, totK_node, atot5488, atot5495]
  decide +kernel

theorem arows5514 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5514 = true := by
  rw [show A10K2.u5514 = KTree.node A10K2.u5506 (nat_lit 89578280) (nat_lit 11223243644) (nat_lit 0) A10K2.u5513 from rfl, allE_node, arows5506, irow5514, arows5513]
  all_goals rfl

theorem atot5514 : totK PA10K2 A10K2.u5514 = [0, 2211027775591, 11148978753092, 22245789646429, 23447970213500, 13646650283830, 3632832861278, 384962563863, 6354482628, 0] := by
  rw [show A10K2.u5514 = KTree.node A10K2.u5506 (nat_lit 89578280) (nat_lit 11223243644) (nat_lit 0) A10K2.u5513 from rfl, totK_node, atot5506, atot5513]
  decide +kernel

theorem arows5529 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5529 = true := by
  rw [show A10K2.u5529 = KTree.node A10K2.u5521 (nat_lit 89853888) (nat_lit 14718895254) (nat_lit 0) A10K2.u5528 from rfl, allE_node, arows5521, irow5529, arows5528]
  all_goals rfl

theorem atot5529 : totK PA10K2 A10K2.u5529 = [0, 2245477168038, 13168295018934, 27990923415026, 25466049846560, 9088420259782, 1080420025359, 37204059898, 0, 0] := by
  rw [show A10K2.u5529 = KTree.node A10K2.u5521 (nat_lit 89853888) (nat_lit 14718895254) (nat_lit 0) A10K2.u5528 from rfl, totK_node, atot5521, atot5528]
  decide +kernel

theorem arows5545 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5545 = true := by
  rw [show A10K2.u5545 = KTree.node A10K2.u5537 (nat_lit 89991103) (nat_lit 14114270882) (nat_lit 0) A10K2.u5544 from rfl, allE_node, arows5537, irow5545, arows5544]
  all_goals rfl

theorem atot5545 : totK PA10K2 A10K2.u5545 = [0, 0, 3980015659678, 19574963349274, 32250679487869, 19577620986361, 3665222332002, 176030134338, 0, 0] := by
  rw [show A10K2.u5545 = KTree.node A10K2.u5537 (nat_lit 89991103) (nat_lit 14114270882) (nat_lit 0) A10K2.u5544 from rfl, totK_node, atot5537, atot5544]
  decide +kernel

theorem arows5560 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5560 = true := by
  rw [show A10K2.u5560 = KTree.node A10K2.u5552 (nat_lit 90125653) (nat_lit 6336130842) (nat_lit 0) A10K2.u5559 from rfl, allE_node, arows5552, irow5560, arows5559]
  all_goals rfl

theorem atot5560 : totK PA10K2 A10K2.u5560 = [0, 1137674346764, 7054000128366, 19121692889914, 27336348237741, 18955443864994, 5032702022856, 441570056573, 7151180950, 0] := by
  rw [show A10K2.u5560 = KTree.node A10K2.u5552 (nat_lit 90125653) (nat_lit 6336130842) (nat_lit 0) A10K2.u5559 from rfl, totK_node, atot5552, atot5559]
  decide +kernel

theorem arows5577 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5577 = true := by
  rw [show A10K2.u5577 = KTree.node A10K2.u5569 (nat_lit 92324294) (nat_lit 15113133158) (nat_lit 0) A10K2.u5576 from rfl, allE_node, arows5569, irow5577, arows5576]
  all_goals rfl

theorem atot5577 : totK PA10K2 A10K2.u5577 = [0, 2418191564556, 13692090013964, 27829790416836, 23811573728072, 8043709740320, 974310293121, 36196801203, 0, 0] := by
  rw [show A10K2.u5577 = KTree.node A10K2.u5569 (nat_lit 92324294) (nat_lit 15113133158) (nat_lit 0) A10K2.u5576 from rfl, totK_node, atot5569, atot5576]
  decide +kernel

theorem arows5592 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5592 = true := by
  rw [show A10K2.u5592 = KTree.node A10K2.u5584 (nat_lit 92460439) (nat_lit 9264170262) (nat_lit 0) A10K2.u5591 from rfl, allE_node, arows5584, irow5592, arows5591]
  all_goals rfl

theorem atot5592 : totK PA10K2 A10K2.u5592 = [0, 2184626378715, 13286188891362, 28575401898462, 24880123143124, 7649927095190, 759346090814, 13259410892, 0, 0] := by
  rw [show A10K2.u5592 = KTree.node A10K2.u5584 (nat_lit 92460439) (nat_lit 9264170262) (nat_lit 0) A10K2.u5591 from rfl, totK_node, atot5584, atot5591]
  decide +kernel

theorem arows5608 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5608 = true := by
  rw [show A10K2.u5608 = KTree.node A10K2.u5600 (nat_lit 92561970) (nat_lit 9985369790) (nat_lit 0) A10K2.u5607 from rfl, allE_node, arows5600, irow5608, arows5607]
  all_goals rfl

theorem atot5608 : totK PA10K2 A10K2.u5608 = [0, 0, 3112171365948, 15977068478002, 29100231557957, 21442872360168, 6162174692872, 759055144479, 36134558889, 0] := by
  rw [show A10K2.u5608 = KTree.node A10K2.u5600 (nat_lit 92561970) (nat_lit 9985369790) (nat_lit 0) A10K2.u5607 from rfl, totK_node, atot5600, atot5607]
  decide +kernel

theorem arows5623 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5623 = true := by
  rw [show A10K2.u5623 = KTree.node A10K2.u5615 (nat_lit 92702933) (nat_lit 6356134920) (nat_lit 0) A10K2.u5622 from rfl, allE_node, arows5615, irow5623, arows5622]
  all_goals rfl

theorem atot5623 : totK PA10K2 A10K2.u5623 = [0, 0, 3212031132150, 17293327650066, 30989574367003, 20050778965708, 4291311067211, 330997345666, 5676195732, 0] := by
  rw [show A10K2.u5623 = KTree.node A10K2.u5615 (nat_lit 92702933) (nat_lit 6356134920) (nat_lit 0) A10K2.u5622 from rfl, totK_node, atot5615, atot5622]
  decide +kernel

theorem arows5643 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5643 = true := by
  rw [show A10K2.u5643 = KTree.node A10K2.u5635 (nat_lit 92894622) (nat_lit 15508892991) (nat_lit 0) A10K2.u5642 from rfl, allE_node, arows5635, irow5643, arows5642]
  all_goals rfl

theorem atot5643 : totK PA10K2 A10K2.u5643 = [0, 2498694883001, 13269767684959, 26633973585519, 24340097130144, 9378148603803, 1243891697330, 44057407906, 0, 0] := by
  rw [show A10K2.u5643 = KTree.node A10K2.u5635 (nat_lit 92894622) (nat_lit 15508892991) (nat_lit 0) A10K2.u5642 from rfl, totK_node, atot5635, atot5642]
  decide +kernel

theorem arows5658 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5658 = true := by
  rw [show A10K2.u5658 = KTree.node A10K2.u5650 (nat_lit 92963434) (nat_lit 3853136308) (nat_lit 0) A10K2.u5657 from rfl, allE_node, arows5650, irow5658, arows5657]
  all_goals rfl

theorem atot5658 : totK PA10K2 A10K2.u5658 = [0, 2946609876572, 15761881994534, 29642169507501, 22277299227269, 5710747077448, 488074911691, 6354482628, 0, 0] := by
  rw [show A10K2.u5658 = KTree.node A10K2.u5650 (nat_lit 92963434) (nat_lit 3853136308) (nat_lit 0) A10K2.u5657 from rfl, totK_node, atot5650, atot5657]
  decide +kernel

theorem arows5674 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5674 = true := by
  rw [show A10K2.u5674 = KTree.node A10K2.u5666 (nat_lit 93138838) (nat_lit 15959983175) (nat_lit 0) A10K2.u5673 from rfl, allE_node, arows5666, irow5674, arows5673]
  all_goals rfl

theorem atot5674 : totK PA10K2 A10K2.u5674 = [0, 307923820525, 5671226774296, 21551652147687, 30919527825756, 17154918981961, 2972228479651, 131650551297, 0, 0] := by
  rw [show A10K2.u5674 = KTree.node A10K2.u5666 (nat_lit 93138838) (nat_lit 15959983175) (nat_lit 0) A10K2.u5673 from rfl, totK_node, atot5666, atot5673]
  decide +kernel

theorem arows5689 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5689 = true := by
  rw [show A10K2.u5689 = KTree.node A10K2.u5681 (nat_lit 93206276) (nat_lit 12384035311) (nat_lit 0) A10K2.u5688 from rfl, allE_node, arows5681, irow5689, arows5688]
  all_goals rfl

theorem atot5689 : totK PA10K2 A10K2.u5689 = [0, 0, 2158005291967, 13495706152250, 28760071772206, 23492675403318, 6767238417327, 794591882212, 36704093874, 0] := by
  rw [show A10K2.u5689 = KTree.node A10K2.u5681 (nat_lit 93206276) (nat_lit 12384035311) (nat_lit 0) A10K2.u5688 from rfl, totK_node, atot5681, atot5688]
  decide +kernel

theorem arows5706 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5706 = true := by
  rw [show A10K2.u5706 = KTree.node A10K2.u5698 (nat_lit 93329932) (nat_lit 11379314781) (nat_lit 0) A10K2.u5705 from rfl, allE_node, arows5698, irow5706, arows5705]
  all_goals rfl

theorem atot5706 : totK PA10K2 A10K2.u5706 = [0, 2045425524865, 11814461541455, 25082281629598, 24257456029050, 11147581075739, 2441218510806, 259908924341, 6239673734, 0] := by
  rw [show A10K2.u5706 = KTree.node A10K2.u5698 (nat_lit 93329932) (nat_lit 11379314781) (nat_lit 0) A10K2.u5705 from rfl, totK_node, atot5698, atot5705]
  decide +kernel

theorem arows5721 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5721 = true := by
  rw [show A10K2.u5721 = KTree.node A10K2.u5713 (nat_lit 93409550) (nat_lit 8822982571) (nat_lit 0) A10K2.u5720 from rfl, allE_node, arows5713, irow5721, arows5720]
  all_goals rfl

theorem atot5721 : totK PA10K2 A10K2.u5721 = [0, 2052442624241, 12186350852564, 26988095646796, 25436133446959, 8807568067204, 969407992176, 36629191582, 0, 0] := by
  rw [show A10K2.u5721 = KTree.node A10K2.u5713 (nat_lit 93409550) (nat_lit 8822982571) (nat_lit 0) A10K2.u5720 from rfl, totK_node, atot5713, atot5720]
  decide +kernel

theorem arows5737 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5737 = true := by
  rw [show A10K2.u5737 = KTree.node A10K2.u5729 (nat_lit 93472694) (nat_lit 10267057088) (nat_lit 0) A10K2.u5736 from rfl, allE_node, arows5729, irow5737, arows5736]
  all_goals rfl

theorem atot5737 : totK PA10K2 A10K2.u5737 = [0, 2343832716771, 13966762890039, 28701575874069, 23594748250436, 6829196329154, 664020722522, 12475655917, 0, 0] := by
  rw [show A10K2.u5737 = KTree.node A10K2.u5729 (nat_lit 93472694) (nat_lit 10267057088) (nat_lit 0) A10K2.u5736 from rfl, totK_node, atot5729, atot5736]
  decide +kernel

theorem arows5752 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5752 = true := by
  rw [show A10K2.u5752 = KTree.node A10K2.u5744 (nat_lit 93662615) (nat_lit 14535722111) (nat_lit 0) A10K2.u5751 from rfl, allE_node, arows5744, irow5752, arows5751]
  all_goals rfl

theorem atot5752 : totK PA10K2 A10K2.u5752 = [0, 0, 4523926816100, 20911070910584, 31679131937823, 16362699461637, 2445025396904, 113410386985, 0, 0] := by
  rw [show A10K2.u5752 = KTree.node A10K2.u5744 (nat_lit 93662615) (nat_lit 14535722111) (nat_lit 0) A10K2.u5751 from rfl, totK_node, atot5744, atot5751]
  decide +kernel

theorem arows5770 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5770 = true := by
  rw [show A10K2.u5770 = KTree.node A10K2.u5762 (nat_lit 93759141) (nat_lit 6969042730) (nat_lit 0) A10K2.u5769 from rfl, allE_node, arows5762, irow5770, arows5769]
  all_goals rfl

theorem atot5770 : totK PA10K2 A10K2.u5770 = [0, 0, 3146571183344, 16318499378868, 29667375882667, 20465629406829, 4952512314531, 452258175328, 6354482628, 0] := by
  rw [show A10K2.u5770 = KTree.node A10K2.u5762 (nat_lit 93759141) (nat_lit 6969042730) (nat_lit 0) A10K2.u5769 from rfl, totK_node, atot5762, atot5769]
  decide +kernel

theorem arows5785 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5785 = true := by
  rw [show A10K2.u5785 = KTree.node A10K2.u5777 (nat_lit 94425160) (nat_lit 13769138022) (nat_lit 0) A10K2.u5784 from rfl, allE_node, arows5777, irow5785, arows5784]
  all_goals rfl

theorem atot5785 : totK PA10K2 A10K2.u5785 = [0, 0, 2679795072844, 14692374464243, 28670080743135, 22811231791396, 6727907256430, 798083248743, 36196801203, 0] := by
  rw [show A10K2.u5785 = KTree.node A10K2.u5777 (nat_lit 94425160) (nat_lit 13769138022) (nat_lit 0) A10K2.u5784 from rfl, totK_node, atot5777, atot5784]
  decide +kernel

theorem arows5801 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5801 = true := by
  rw [show A10K2.u5801 = KTree.node A10K2.u5793 (nat_lit 94571974) (nat_lit 15803271880) (nat_lit 0) A10K2.u5800 from rfl, allE_node, arows5793, irow5801, arows5800]
  all_goals rfl

theorem atot5801 : totK PA10K2 A10K2.u5801 = [0, 0, 2973416838051, 16092730126013, 30091903306681, 21846845495914, 5341779853223, 462647174306, 6354482628, 0] := by
  rw [show A10K2.u5801 = KTree.node A10K2.u5793 (nat_lit 94571974) (nat_lit 15803271880) (nat_lit 0) A10K2.u5800 from rfl, totK_node, atot5793, atot5800]
  decide +kernel

theorem arows5816 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5816 = true := by
  rw [show A10K2.u5816 = KTree.node A10K2.u5808 (nat_lit 95015169) (nat_lit 9993845645) (nat_lit 0) A10K2.u5815 from rfl, allE_node, arows5808, irow5816, arows5815]
  all_goals rfl

theorem atot5816 : totK PA10K2 A10K2.u5816 = [0, 0, 2757251005786, 14837442576121, 28684741514236, 22866592562011, 6856893497186, 817700977355, 37204059898, 0] := by
  rw [show A10K2.u5816 = KTree.node A10K2.u5808 (nat_lit 95015169) (nat_lit 9993845645) (nat_lit 0) A10K2.u5815 from rfl, totK_node, atot5808, atot5815]
  decide +kernel

theorem arows5833 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5833 = true := by
  rw [show A10K2.u5833 = KTree.node A10K2.u5825 (nat_lit 95104456) (nat_lit 10915384193) (nat_lit 0) A10K2.u5832 from rfl, allE_node, arows5825, irow5833, arows5832]
  all_goals rfl

theorem atot5833 : totK PA10K2 A10K2.u5833 = [0, 0, 3058540980672, 16322614381006, 30071469711469, 21693107850318, 5280667008174, 462614328341, 6354482628, 0] := by
  rw [show A10K2.u5833 = KTree.node A10K2.u5825 (nat_lit 95104456) (nat_lit 10915384193) (nat_lit 0) A10K2.u5832 from rfl, totK_node, atot5825, atot5832]
  decide +kernel

theorem arows5848 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5848 = true := by
  rw [show A10K2.u5848 = KTree.node A10K2.u5840 (nat_lit 95478061) (nat_lit 5718164862) (nat_lit 0) A10K2.u5847 from rfl, allE_node, arows5840, irow5848, arows5847]
  all_goals rfl

theorem atot5848 : totK PA10K2 A10K2.u5848 = [0, 0, 2501325934731, 14528773460353, 29033607997333, 22693498518913, 6366566623462, 786949983941, 35767183343, 0] := by
  rw [show A10K2.u5848 = KTree.node A10K2.u5840 (nat_lit 95478061) (nat_lit 5718164862) (nat_lit 0) A10K2.u5847 from rfl, totK_node, atot5840, atot5847]
  decide +kernel

theorem arows5864 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5864 = true := by
  rw [show A10K2.u5864 = KTree.node A10K2.u5856 (nat_lit 95558464) (nat_lit 13423509569) (nat_lit 0) A10K2.u5863 from rfl, allE_node, arows5856, irow5864, arows5863]
  all_goals rfl

theorem atot5864 : totK PA10K2 A10K2.u5864 = [0, 0, 2317656958010, 13541771998043, 27924347798431, 23395290330660, 7090931034451, 868750677741, 36768997705, 0] := by
  rw [show A10K2.u5864 = KTree.node A10K2.u5856 (nat_lit 95558464) (nat_lit 13423509569) (nat_lit 0) A10K2.u5863 from rfl, totK_node, atot5856, atot5863]
  decide +kernel

theorem arows5879 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5879 = true := by
  rw [show A10K2.u5879 = KTree.node A10K2.u5871 (nat_lit 95703428) (nat_lit 9133102325) (nat_lit 0) A10K2.u5878 from rfl, allE_node, arows5871, irow5879, arows5878]
  all_goals rfl

theorem atot5879 : totK PA10K2 A10K2.u5879 = [0, 0, 0, 5527483695552, 23545157547331, 31053954886747, 13194343169483, 2010179064986, 80469708548, 0] := by
  rw [show A10K2.u5879 = KTree.node A10K2.u5871 (nat_lit 95703428) (nat_lit 9133102325) (nat_lit 0) A10K2.u5878 from rfl, totK_node, atot5871, atot5878]
  decide +kernel

theorem arows5898 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5898 = true := by
  rw [show A10K2.u5898 = KTree.node A10K2.u5890 (nat_lit 95847204) (nat_lit 13711877624) (nat_lit 0) A10K2.u5897 from rfl, allE_node, arows5890, irow5898, arows5897]
  all_goals rfl

theorem atot5898 : totK PA10K2 A10K2.u5898 = [1058637277771, 4454015480509, 6525423530273, 5621920481659, 12454503576825, 23066341588678, 16474091549655, 4491975057858, 446040892095, 6354482628] := by
  rw [show A10K2.u5898 = KTree.node A10K2.u5890 (nat_lit 95847204) (nat_lit 13711877624) (nat_lit 0) A10K2.u5897 from rfl, totK_node, atot5890, atot5897]
  decide +kernel

theorem arows5913 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5913 = true := by
  rw [show A10K2.u5913 = KTree.node A10K2.u5905 (nat_lit 100702563) (nat_lit 5599039736) (nat_lit 0) A10K2.u5912 from rfl, allE_node, arows5905, irow5913, arows5912]
  all_goals rfl

theorem atot5913 : totK PA10K2 A10K2.u5913 = [2317223048421, 13572205907543, 27782889436402, 23969025671600, 8173070622589, 988882073945, 36196801203, 0, 0, 0] := by
  rw [show A10K2.u5913 = KTree.node A10K2.u5905 (nat_lit 100702563) (nat_lit 5599039736) (nat_lit 0) A10K2.u5912 from rfl, totK_node, atot5905, atot5912]
  decide +kernel

theorem arows5929 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5929 = true := by
  rw [show A10K2.u5929 = KTree.node A10K2.u5921 (nat_lit 100861957) (nat_lit 6751821106) (nat_lit 0) A10K2.u5928 from rfl, allE_node, arows5921, irow5929, arows5928]
  all_goals rfl

theorem atot5929 : totK PA10K2 A10K2.u5929 = [2910957610618, 15693169355407, 29982397572375, 22878983681489, 6016461968469, 507194582731, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u5929 = KTree.node A10K2.u5921 (nat_lit 100861957) (nat_lit 6751821106) (nat_lit 0) A10K2.u5928 from rfl, totK_node, atot5921, atot5928]
  decide +kernel

theorem arows5944 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5944 = true := by
  rw [show A10K2.u5944 = KTree.node A10K2.u5936 (nat_lit 100927564) (nat_lit 10942262896) (nat_lit 0) A10K2.u5943 from rfl, allE_node, arows5936, irow5944, arows5943]
  all_goals rfl

theorem atot5944 : totK PA10K2 A10K2.u5944 = [0, 4190734284969, 20144097031255, 32210763283367, 18539938048061, 3282560151538, 146629947540, 0, 0, 0] := by
  rw [show A10K2.u5944 = KTree.node A10K2.u5936 (nat_lit 100927564) (nat_lit 10942262896) (nat_lit 0) A10K2.u5943 from rfl, totK_node, atot5936, atot5943]
  decide +kernel

theorem arows5961 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5961 = true := by
  rw [show A10K2.u5961 = KTree.node A10K2.u5953 (nat_lit 101060599) (nat_lit 14849519599) (nat_lit 0) A10K2.u5960 from rfl, allE_node, arows5953, irow5961, arows5960]
  all_goals rfl

theorem atot5961 : totK PA10K2 A10K2.u5961 = [0, 1788659381433, 12068032168009, 27515813550881, 24873313091160, 8038760539921, 965951250300, 36134558889, 0, 0] := by
  rw [show A10K2.u5961 = KTree.node A10K2.u5953 (nat_lit 101060599) (nat_lit 14849519599) (nat_lit 0) A10K2.u5960 from rfl, totK_node, atot5953, atot5960]
  decide +kernel

theorem arows5976 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5976 = true := by
  rw [show A10K2.u5976 = KTree.node A10K2.u5968 (nat_lit 101151646) (nat_lit 14990867186) (nat_lit 0) A10K2.u5975 from rfl, allE_node, arows5968, irow5976, arows5975]
  all_goals rfl

theorem atot5976 : totK PA10K2 A10K2.u5976 = [2182481654920, 11709067094258, 23806595601274, 23998562104532, 13177456288041, 3296066432452, 287123001718, 5676195732, 0, 0] := by
  rw [show A10K2.u5976 = KTree.node A10K2.u5968 (nat_lit 101151646) (nat_lit 14990867186) (nat_lit 0) A10K2.u5975 from rfl, totK_node, atot5968, atot5975]
  decide +kernel

theorem arows5992 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u5992 = true := by
  rw [show A10K2.u5992 = KTree.node A10K2.u5984 (nat_lit 101843213) (nat_lit 5875885541) (nat_lit 0) A10K2.u5991 from rfl, allE_node, arows5984, irow5992, arows5991]
  all_goals rfl

theorem atot5992 : totK PA10K2 A10K2.u5992 = [2147550714988, 13016562881592, 27769038610300, 24601687673896, 8371530400443, 1007102403793, 36196801203, 0, 0, 0] := by
  rw [show A10K2.u5992 = KTree.node A10K2.u5984 (nat_lit 101843213) (nat_lit 5875885541) (nat_lit 0) A10K2.u5991 from rfl, totK_node, atot5984, atot5991]
  decide +kernel

theorem arows6007 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6007 = true := by
  rw [show A10K2.u6007 = KTree.node A10K2.u5999 (nat_lit 101981618) (nat_lit 12467972683) (nat_lit 0) A10K2.u6006 from rfl, allE_node, arows5999, irow6007, arows6006]
  all_goals rfl

theorem atot6007 : totK PA10K2 A10K2.u6007 = [0, 5067708091990, 22421381348924, 31856798424471, 15085433310028, 2173369145620, 80455563677, 0, 0, 0] := by
  rw [show A10K2.u6007 = KTree.node A10K2.u5999 (nat_lit 101981618) (nat_lit 12467972683) (nat_lit 0) A10K2.u6006 from rfl, totK_node, atot5999, atot6006]
  decide +kernel

theorem arows6025 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6025 = true := by
  rw [show A10K2.u6025 = KTree.node A10K2.u6017 (nat_lit 102156397) (nat_lit 5512705346) (nat_lit 0) A10K2.u6024 from rfl, allE_node, arows6017, irow6025, arows6024]
  all_goals rfl

theorem atot6025 : totK PA10K2 A10K2.u6025 = [2176975535692, 10389409114814, 20418924663357, 23141789047355, 15094614572382, 4074518758194, 415966008549, 6354482628, 0, 0] := by
  rw [show A10K2.u6025 = KTree.node A10K2.u6017 (nat_lit 102156397) (nat_lit 5512705346) (nat_lit 0) A10K2.u6024 from rfl, totK_node, atot6017, atot6024]
  decide +kernel

theorem arows6040 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6040 = true := by
  rw [show A10K2.u6040 = KTree.node A10K2.u6032 (nat_lit 102297494) (nat_lit 16036162020) (nat_lit 0) A10K2.u6039 from rfl, allE_node, arows6032, irow6040, arows6039]
  all_goals rfl

theorem atot6040 : totK PA10K2 A10K2.u6040 = [1606735580082, 11312438640739, 27762520102867, 27688956000948, 9886655112887, 1128885091217, 36196801203, 0, 0, 0] := by
  rw [show A10K2.u6040 = KTree.node A10K2.u6032 (nat_lit 102297494) (nat_lit 16036162020) (nat_lit 0) A10K2.u6039 from rfl, totK_node, atot6032, atot6039]
  decide +kernel

theorem arows6056 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6056 = true := by
  rw [show A10K2.u6056 = KTree.node A10K2.u6048 (nat_lit 102457458) (nat_lit 10418642867) (nat_lit 0) A10K2.u6055 from rfl, allE_node, arows6048, irow6056, arows6055]
  all_goals rfl

theorem atot6056 : totK PA10K2 A10K2.u6056 = [2346766361561, 13250876082624, 27612293128050, 25457556020433, 9856991094666, 1346765726643, 45034840325, 0, 0, 0] := by
  rw [show A10K2.u6056 = KTree.node A10K2.u6048 (nat_lit 102457458) (nat_lit 10418642867) (nat_lit 0) A10K2.u6055 from rfl, totK_node, atot6048, atot6055]
  decide +kernel

theorem arows6071 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6071 = true := by
  rw [show A10K2.u6071 = KTree.node A10K2.u6063 (nat_lit 102518820) (nat_lit 13324647755) (nat_lit 0) A10K2.u6070 from rfl, allE_node, arows6063, irow6071, arows6070]
  all_goals rfl

theorem atot6071 : totK PA10K2 A10K2.u6071 = [0, 3058745704221, 16200638684173, 30104355381593, 22331035398044, 5873820913229, 499782588848, 7007974415, 0, 0] := by
  rw [show A10K2.u6071 = KTree.node A10K2.u6063 (nat_lit 102518820) (nat_lit 13324647755) (nat_lit 0) A10K2.u6070 from rfl, totK_node, atot6063, atot6070]
  decide +kernel

theorem arows6088 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6088 = true := by
  rw [show A10K2.u6088 = KTree.node A10K2.u6080 (nat_lit 102607018) (nat_lit 12841543123) (nat_lit 0) A10K2.u6087 from rfl, allE_node, arows6080, irow6088, arows6087]
  all_goals rfl

theorem atot6088 : totK PA10K2 A10K2.u6088 = [0, 3067944840355, 16054168854743, 30182086779312, 23816070711046, 6898446853388, 579069682142, 7151180950, 0, 0] := by
  rw [show A10K2.u6088 = KTree.node A10K2.u6080 (nat_lit 102607018) (nat_lit 12841543123) (nat_lit 0) A10K2.u6087 from rfl, totK_node, atot6080, atot6087]
  decide +kernel

theorem arows6103 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6103 = true := by
  rw [show A10K2.u6103 = KTree.node A10K2.u6095 (nat_lit 102739898) (nat_lit 14095699885) (nat_lit 0) A10K2.u6102 from rfl, allE_node, arows6095, irow6103, arows6102]
  all_goals rfl

theorem atot6103 : totK PA10K2 A10K2.u6103 = [0, 2045843252504, 11790808312591, 26064172768523, 26313558868712, 11149884804085, 1663203689811, 73776485728, 0, 0] := by
  rw [show A10K2.u6103 = KTree.node A10K2.u6095 (nat_lit 102739898) (nat_lit 14095699885) (nat_lit 0) A10K2.u6102 from rfl, totK_node, atot6095, atot6102]
  decide +kernel

theorem arows6119 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6119 = true := by
  rw [show A10K2.u6119 = KTree.node A10K2.u6111 (nat_lit 102800439) (nat_lit 14838044417) (nat_lit 0) A10K2.u6118 from rfl, allE_node, arows6111, irow6119, arows6118]
  all_goals rfl

theorem atot6119 : totK PA10K2 A10K2.u6119 = [0, 2263990848010, 13190444300801, 27721253745714, 24290276502875, 8027506534808, 963789926287, 36196801203, 0, 0] := by
  rw [show A10K2.u6119 = KTree.node A10K2.u6111 (nat_lit 102800439) (nat_lit 14838044417) (nat_lit 0) A10K2.u6118 from rfl, totK_node, atot6111, atot6118]
  decide +kernel

theorem arows6134 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6134 = true := by
  rw [show A10K2.u6134 = KTree.node A10K2.u6126 (nat_lit 102960193) (nat_lit 10332167580) (nat_lit 0) A10K2.u6133 from rfl, allE_node, arows6126, irow6134, arows6133]
  all_goals rfl

theorem atot6134 : totK PA10K2 A10K2.u6134 = [0, 2869607167599, 15781958786858, 30314603532478, 22890661705936, 5698669312968, 402109074047, 5976421810, 0, 0] := by
  rw [show A10K2.u6134 = KTree.node A10K2.u6126 (nat_lit 102960193) (nat_lit 10332167580) (nat_lit 0) A10K2.u6133 from rfl, totK_node, atot6126, atot6133]
  decide +kernel

theorem arows6156 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6156 = true := by
  rw [show A10K2.u6156 = KTree.node A10K2.u6148 (nat_lit 103027476) (nat_lit 11803689551) (nat_lit 0) A10K2.u6155 from rfl, allE_node, arows6148, irow6156, arows6155]
  all_goals rfl

theorem atot6156 : totK PA10K2 A10K2.u6156 = [0, 0, 3979855394117, 19247846118808, 31449137248384, 18957824364111, 3785744088996, 205736891917, 0, 0] := by
  rw [show A10K2.u6156 = KTree.node A10K2.u6148 (nat_lit 103027476) (nat_lit 11803689551) (nat_lit 0) A10K2.u6155 from rfl, totK_node, atot6148, atot6155]
  decide +kernel

theorem arows6171 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6171 = true := by
  rw [show A10K2.u6171 = KTree.node A10K2.u6163 (nat_lit 103168014) (nat_lit 7996168213) (nat_lit 0) A10K2.u6170 from rfl, allE_node, arows6163, irow6171, arows6170]
  all_goals rfl

theorem atot6171 : totK PA10K2 A10K2.u6171 = [0, 0, 2196438079391, 12822336051783, 27048150937407, 23405378098406, 7825149459016, 1055990226592, 41810754621, 0] := by
  rw [show A10K2.u6171 = KTree.node A10K2.u6163 (nat_lit 103168014) (nat_lit 7996168213) (nat_lit 0) A10K2.u6170 from rfl, totK_node, atot6163, atot6170]
  decide +kernel

theorem arows6187 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6187 = true := by
  rw [show A10K2.u6187 = KTree.node A10K2.u6179 (nat_lit 103813920) (nat_lit 13294287949) (nat_lit 0) A10K2.u6186 from rfl, allE_node, arows6179, irow6187, arows6186]
  all_goals rfl

theorem atot6187 : totK PA10K2 A10K2.u6187 = [0, 2181258796342, 12711202049568, 27041047536743, 25061105291170, 9874197230013, 1530881382151, 80801378504, 0, 0] := by
  rw [show A10K2.u6187 = KTree.node A10K2.u6179 (nat_lit 103813920) (nat_lit 13294287949) (nat_lit 0) A10K2.u6186 from rfl, totK_node, atot6179, atot6186]
  decide +kernel

theorem arows6202 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6202 = true := by
  rw [show A10K2.u6202 = KTree.node A10K2.u6194 (nat_lit 103950621) (nat_lit 6421608984) (nat_lit 0) A10K2.u6201 from rfl, allE_node, arows6194, irow6202, arows6201]
  all_goals rfl

theorem atot6202 : totK PA10K2 A10K2.u6202 = [0, 2145113445699, 13302569358754, 28510569679871, 24419232067444, 7269117510469, 677017214117, 10957026886, 0, 0] := by
  rw [show A10K2.u6202 = KTree.node A10K2.u6194 (nat_lit 103950621) (nat_lit 6421608984) (nat_lit 0) A10K2.u6201 from rfl, totK_node, atot6194, atot6201]
  decide +kernel

theorem arows6219 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6219 = true := by
  rw [show A10K2.u6219 = KTree.node A10K2.u6211 (nat_lit 104099429) (nat_lit 4981639273) (nat_lit 0) A10K2.u6218 from rfl, allE_node, arows6211, irow6219, arows6218]
  all_goals rfl

theorem atot6219 : totK PA10K2 A10K2.u6219 = [0, 0, 4436339614692, 21316984823423, 32295539081264, 15582413642776, 2276939405892, 86489779238, 0, 0] := by
  rw [show A10K2.u6219 = KTree.node A10K2.u6211 (nat_lit 104099429) (nat_lit 4981639273) (nat_lit 0) A10K2.u6218 from rfl, totK_node, atot6211, atot6218]
  decide +kernel

theorem arows6234 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6234 = true := by
  rw [show A10K2.u6234 = KTree.node A10K2.u6226 (nat_lit 104340940) (nat_lit 6383717942) (nat_lit 0) A10K2.u6233 from rfl, allE_node, arows6226, irow6234, arows6233]
  all_goals rfl

theorem atot6234 : totK PA10K2 A10K2.u6234 = [0, 2176975535692, 10970949716640, 22079244272627, 23728347330171, 13667104271791, 3407231745730, 298367956771, 5976421810, 0] := by
  rw [show A10K2.u6234 = KTree.node A10K2.u6226 (nat_lit 104340940) (nat_lit 6383717942) (nat_lit 0) A10K2.u6233 from rfl, totK_node, atot6226, atot6233]
  decide +kernel

theorem arows6250 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6250 = true := by
  rw [show A10K2.u6250 = KTree.node A10K2.u6242 (nat_lit 104429247) (nat_lit 12309121275) (nat_lit 0) A10K2.u6249 from rfl, allE_node, arows6242, irow6250, arows6249]
  all_goals rfl

theorem atot6250 : totK PA10K2 A10K2.u6250 = [0, 2637398187092, 14649961823811, 29716515341965, 25063758968906, 7511760192926, 648034815346, 7380853412, 0, 0] := by
  rw [show A10K2.u6250 = KTree.node A10K2.u6242 (nat_lit 104429247) (nat_lit 12309121275) (nat_lit 0) A10K2.u6249 from rfl, totK_node, atot6242, atot6249]
  decide +kernel

theorem arows6265 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6265 = true := by
  rw [show A10K2.u6265 = KTree.node A10K2.u6257 (nat_lit 104569197) (nat_lit 5779581562) (nat_lit 0) A10K2.u6264 from rfl, allE_node, arows6257, irow6265, arows6264]
  all_goals rfl

theorem atot6265 : totK PA10K2 A10K2.u6265 = [872244600920, 4724465958786, 13099930417208, 23896574901300, 24409757703039, 11061172398202, 1721472110222, 74781409772, 0, 0] := by
  rw [show A10K2.u6265 = KTree.node A10K2.u6257 (nat_lit 104569197) (nat_lit 5779581562) (nat_lit 0) A10K2.u6264 from rfl, totK_node, atot6257, atot6264]
  decide +kernel

theorem arows6283 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6283 = true := by
  rw [show A10K2.u6283 = KTree.node A10K2.u6275 (nat_lit 105491574) (nat_lit 16144931505) (nat_lit 0) A10K2.u6282 from rfl, allE_node, arows6275, irow6283, arows6282]
  all_goals rfl

theorem atot6283 : totK PA10K2 A10K2.u6283 = [2302572247910, 13132528738643, 27300340049997, 24364024523241, 8639263448740, 1044896768122, 37204059898, 0, 0, 0] := by
  rw [show A10K2.u6283 = KTree.node A10K2.u6275 (nat_lit 105491574) (nat_lit 16144931505) (nat_lit 0) A10K2.u6282 from rfl, totK_node, atot6275, atot6282]
  decide +kernel

theorem arows6298 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6298 = true := by
  rw [show A10K2.u6298 = KTree.node A10K2.u6290 (nat_lit 105566273) (nat_lit 10228612899) (nat_lit 0) A10K2.u6297 from rfl, allE_node, arows6290, irow6298, arows6297]
  all_goals rfl

theorem atot6298 : totK PA10K2 A10K2.u6298 = [3133277154614, 16536771990805, 30444160792380, 22129455899399, 5511277469626, 457862252709, 6354482628, 0, 0, 0] := by
  rw [show A10K2.u6298 = KTree.node A10K2.u6290 (nat_lit 105566273) (nat_lit 10228612899) (nat_lit 0) A10K2.u6297 from rfl, totK_node, atot6290, atot6297]
  decide +kernel

theorem arows6314 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6314 = true := by
  rw [show A10K2.u6314 = KTree.node A10K2.u6306 (nat_lit 105641686) (nat_lit 13610480969) (nat_lit 0) A10K2.u6313 from rfl, allE_node, arows6306, irow6314, arows6313]
  all_goals rfl

theorem atot6314 : totK PA10K2 A10K2.u6314 = [0, 4944691235659, 22046307252792, 32206043167903, 16815626720376, 2695068720819, 113070502409, 0, 0, 0] := by
  rw [show A10K2.u6314 = KTree.node A10K2.u6306 (nat_lit 105641686) (nat_lit 13610480969) (nat_lit 0) A10K2.u6313 from rfl, totK_node, atot6306, atot6313]
  decide +kernel

theorem arows6329 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6329 = true := by
  rw [show A10K2.u6329 = KTree.node A10K2.u6321 (nat_lit 105770711) (nat_lit 12471947999) (nat_lit 0) A10K2.u6328 from rfl, allE_node, arows6321, irow6329, arows6328]
  all_goals rfl

theorem atot6329 : totK PA10K2 A10K2.u6329 = [0, 1793477866547, 12239479228737, 27834962936401, 25118508300448, 8312096484148, 987909221103, 36704093874, 0, 0] := by
  rw [show A10K2.u6329 = KTree.node A10K2.u6321 (nat_lit 105770711) (nat_lit 12471947999) (nat_lit 0) A10K2.u6328 from rfl, totK_node, atot6321, atot6328]
  decide +kernel

theorem arows6346 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6346 = true := by
  rw [show A10K2.u6346 = KTree.node A10K2.u6338 (nat_lit 105865682) (nat_lit 14319642472) (nat_lit 0) A10K2.u6345 from rfl, allE_node, arows6338, irow6346, arows6345]
  all_goals rfl

theorem atot6346 : totK PA10K2 A10K2.u6346 = [1592824415474, 8984783793431, 20549893626673, 25521395546583, 16957485420724, 4390799885014, 359391462096, 6239673734, 0, 0] := by
  rw [show A10K2.u6346 = KTree.node A10K2.u6338 (nat_lit 105865682) (nat_lit 14319642472) (nat_lit 0) A10K2.u6345 from rfl, totK_node, atot6338, atot6345]
  decide +kernel

theorem arows6361 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6361 = true := by
  rw [show A10K2.u6361 = KTree.node A10K2.u6353 (nat_lit 106026146) (nat_lit 14377112747) (nat_lit 0) A10K2.u6360 from rfl, allE_node, arows6353, irow6361, arows6360]
  all_goals rfl

theorem atot6361 : totK PA10K2 A10K2.u6361 = [2437533910714, 13414470901652, 27391488925695, 24500802257447, 8753852253100, 1056894765053, 37204059898, 0, 0, 0] := by
  rw [show A10K2.u6361 = KTree.node A10K2.u6353 (nat_lit 106026146) (nat_lit 14377112747) (nat_lit 0) A10K2.u6360 from rfl, totK_node, atot6353, atot6360]
  decide +kernel

theorem arows6377 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6377 = true := by
  rw [show A10K2.u6377 = KTree.node A10K2.u6369 (nat_lit 106244342) (nat_lit 14317516840) (nat_lit 0) A10K2.u6376 from rfl, allE_node, arows6369, irow6377, arows6376]
  all_goals rfl

theorem atot6377 : totK PA10K2 A10K2.u6377 = [306750524226, 6984282367902, 24746170760622, 30233454477142, 12893742258110, 1719668771568, 51124281457, 0, 0, 0] := by
  rw [show A10K2.u6377 = KTree.node A10K2.u6369 (nat_lit 106244342) (nat_lit 14317516840) (nat_lit 0) A10K2.u6376 from rfl, totK_node, atot6369, atot6376]
  decide +kernel

theorem arows6392 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6392 = true := by
  rw [show A10K2.u6392 = KTree.node A10K2.u6384 (nat_lit 106341783) (nat_lit 13276784823) (nat_lit 0) A10K2.u6391 from rfl, allE_node, arows6384, irow6392, arows6391]
  all_goals rfl

theorem atot6392 : totK PA10K2 A10K2.u6392 = [1602700457968, 8088794513411, 18647685220142, 25471244810475, 17544951423279, 4562328415608, 446040892095, 6354482628, 0, 0] := by
  rw [show A10K2.u6392 = KTree.node A10K2.u6384 (nat_lit 106341783) (nat_lit 13276784823) (nat_lit 0) A10K2.u6391 from rfl, totK_node, atot6384, atot6391]
  decide +kernel

theorem arows6411 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6411 = true := by
  rw [show A10K2.u6411 = KTree.node A10K2.u6403 (nat_lit 106509573) (nat_lit 6339445756) (nat_lit 0) A10K2.u6410 from rfl, allE_node, arows6403, irow6411, arows6410]
  all_goals rfl

theorem atot6411 : totK PA10K2 A10K2.u6411 = [2183007671712, 13601233734074, 29352449316603, 25481281398250, 7902949025770, 836011404882, 30650496230, 0, 0, 0] := by
  rw [show A10K2.u6411 = KTree.node A10K2.u6403 (nat_lit 106509573) (nat_lit 6339445756) (nat_lit 0) A10K2.u6410 from rfl, totK_node, atot6403, atot6410]
  decide +kernel

theorem arows6426 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6426 = true := by
  rw [show A10K2.u6426 = KTree.node A10K2.u6418 (nat_lit 106637559) (nat_lit 13993872137) (nat_lit 0) A10K2.u6425 from rfl, allE_node, arows6418, irow6426, arows6425]
  all_goals rfl

theorem atot6426 : totK PA10K2 A10K2.u6426 = [2347203525858, 13038230632583, 27108689096710, 25338545823438, 9964487070625, 1348114212997, 44108988162, 0, 0, 0] := by
  rw [show A10K2.u6426 = KTree.node A10K2.u6418 (nat_lit 106637559) (nat_lit 13993872137) (nat_lit 0) A10K2.u6425 from rfl, totK_node, atot6418, atot6425]
  decide +kernel

theorem arows6442 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6442 = true := by
  rw [show A10K2.u6442 = KTree.node A10K2.u6434 (nat_lit 106697256) (nat_lit 12601254881) (nat_lit 0) A10K2.u6441 from rfl, allE_node, arows6434, irow6442, arows6441]
  all_goals rfl

theorem atot6442 : totK PA10K2 A10K2.u6442 = [0, 3215496122788, 16736400176907, 30591109005079, 22827679676717, 6131644234786, 514661275493, 7007974415, 0, 0] := by
  rw [show A10K2.u6442 = KTree.node A10K2.u6434 (nat_lit 106697256) (nat_lit 12601254881) (nat_lit 0) A10K2.u6441 from rfl, totK_node, atot6434, atot6441]
  decide +kernel

theorem arows6457 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6457 = true := by
  rw [show A10K2.u6457 = KTree.node A10K2.u6449 (nat_lit 106790300) (nat_lit 7073727762) (nat_lit 0) A10K2.u6456 from rfl, allE_node, arows6449, irow6457, arows6456]
  all_goals rfl

theorem atot6457 : totK PA10K2 A10K2.u6457 = [0, 2939043508777, 15663073920361, 29769775709055, 23261445666996, 6670690299055, 566482147339, 7151180950, 0, 0] := by
  rw [show A10K2.u6457 = KTree.node A10K2.u6449 (nat_lit 106790300) (nat_lit 7073727762) (nat_lit 0) A10K2.u6456 from rfl, totK_node, atot6449, atot6456]
  decide +kernel

theorem arows6474 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6474 = true := by
  rw [show A10K2.u6474 = KTree.node A10K2.u6466 (nat_lit 106926661) (nat_lit 3382720221) (nat_lit 0) A10K2.u6473 from rfl, allE_node, arows6466, irow6474, arows6473]
  all_goals rfl

theorem atot6474 : totK PA10K2 A10K2.u6474 = [0, 2452241519401, 13059635591656, 26322648955740, 25107749022883, 10697876372667, 1632372015925, 73776485728, 0, 0] := by
  rw [show A10K2.u6474 = KTree.node A10K2.u6466 (nat_lit 106926661) (nat_lit 3382720221) (nat_lit 0) A10K2.u6473 from rfl, totK_node, atot6466, atot6473]
  decide +kernel

theorem arows6489 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6489 = true := by
  rw [show A10K2.u6489 = KTree.node A10K2.u6481 (nat_lit 107587847) (nat_lit 1690802133) (nat_lit 0) A10K2.u6488 from rfl, allE_node, arows6481, irow6489, arows6488]
  all_goals rfl

theorem atot6489 : totK PA10K2 A10K2.u6489 = [0, 2196113577261, 12848658315768, 27424736295514, 24678582818138, 8498429551792, 1014424354027, 37204059898, 0, 0] := by
  rw [show A10K2.u6489 = KTree.node A10K2.u6481 (nat_lit 107587847) (nat_lit 1690802133) (nat_lit 0) A10K2.u6488 from rfl, totK_node, atot6481, atot6488]
  decide +kernel

theorem arows6505 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6505 = true := by
  rw [show A10K2.u6505 = KTree.node A10K2.u6497 (nat_lit 107661665) (nat_lit 8951841821) (nat_lit 0) A10K2.u6504 from rfl, allE_node, arows6497, irow6505, arows6504]
  all_goals rfl

theorem atot6505 : totK PA10K2 A10K2.u6505 = [0, 3239735825263, 16955800110727, 30600771604829, 21621086139555, 5145580286839, 374944688795, 6354482628, 0, 0] := by
  rw [show A10K2.u6505 = KTree.node A10K2.u6497 (nat_lit 107661665) (nat_lit 8951841821) (nat_lit 0) A10K2.u6504 from rfl, totK_node, atot6497, atot6504]
  decide +kernel

theorem arows6520 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6520 = true := by
  rw [show A10K2.u6520 = KTree.node A10K2.u6512 (nat_lit 107740168) (nat_lit 13690824799) (nat_lit 0) A10K2.u6519 from rfl, allE_node, arows6512, irow6520, arows6519]
  all_goals rfl

theorem atot6520 : totK PA10K2 A10K2.u6520 = [0, 0, 5107615313615, 22686559399468, 32302989699385, 15985600247317, 2349044970413, 86185743065, 0, 0] := by
  rw [show A10K2.u6520 = KTree.node A10K2.u6512 (nat_lit 107740168) (nat_lit 13690824799) (nat_lit 0) A10K2.u6519 from rfl, totK_node, atot6512, atot6519]
  decide +kernel

theorem arows6538 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6538 = true := by
  rw [show A10K2.u6538 = KTree.node A10K2.u6530 (nat_lit 107875107) (nat_lit 9519231988) (nat_lit 0) A10K2.u6537 from rfl, allE_node, arows6530, irow6538, arows6537]
  all_goals rfl

theorem atot6538 : totK PA10K2 A10K2.u6538 = [0, 0, 1787188660232, 12156177350141, 27824096518600, 24835006638858, 8059382483077, 984473792653, 36704093874, 0] := by
  rw [show A10K2.u6538 = KTree.node A10K2.u6530 (nat_lit 107875107) (nat_lit 9519231988) (nat_lit 0) A10K2.u6537 from rfl, totK_node, atot6530, atot6537]
  decide +kernel

theorem arows6553 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6553 = true := by
  rw [show A10K2.u6553 = KTree.node A10K2.u6545 (nat_lit 107967880) (nat_lit 11561439080) (nat_lit 0) A10K2.u6552 from rfl, allE_node, arows6545, irow6553, arows6552]
  all_goals rfl

theorem atot6553 : totK PA10K2 A10K2.u6553 = [0, 2187980212392, 11909831360446, 24131412294141, 23678865750748, 12739159680281, 3126492058478, 292480554950, 5982052406, 0] := by
  rw [show A10K2.u6553 = KTree.node A10K2.u6545 (nat_lit 107967880) (nat_lit 11561439080) (nat_lit 0) A10K2.u6552 from rfl, totK_node, atot6545, atot6552]
  decide +kernel

theorem arows6569 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6569 = true := by
  rw [show A10K2.u6569 = KTree.node A10K2.u6561 (nat_lit 108134798) (nat_lit 13192143130) (nat_lit 0) A10K2.u6568 from rfl, allE_node, arows6561, irow6569, arows6568]
  all_goals rfl

theorem atot6569 : totK PA10K2 A10K2.u6569 = [0, 2149128638022, 12852583368706, 27494744414755, 24689965709761, 8593243031999, 1041998584991, 37204059898, 0, 0] := by
  rw [show A10K2.u6569 = KTree.node A10K2.u6561 (nat_lit 108134798) (nat_lit 13192143130) (nat_lit 0) A10K2.u6568 from rfl, totK_node, atot6561, atot6568]
  decide +kernel

theorem arows6584 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6584 = true := by
  rw [show A10K2.u6584 = KTree.node A10K2.u6576 (nat_lit 108347436) (nat_lit 12812578913) (nat_lit 0) A10K2.u6583 from rfl, allE_node, arows6576, irow6584, arows6583]
  all_goals rfl

theorem atot6584 : totK PA10K2 A10K2.u6584 = [0, 0, 5379160560295, 23358522935171, 31958128915998, 14028183070128, 1839242512134, 56584774350, 0, 0] := by
  rw [show A10K2.u6584 = KTree.node A10K2.u6576 (nat_lit 108347436) (nat_lit 12812578913) (nat_lit 0) A10K2.u6583 from rfl, totK_node, atot6576, atot6583]
  decide +kernel

theorem arows6601 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6601 = true := by
  rw [show A10K2.u6601 = KTree.node A10K2.u6593 (nat_lit 108450180) (nat_lit 9133102325) (nat_lit 0) A10K2.u6600 from rfl, allE_node, arows6593, irow6601, arows6600]
  all_goals rfl

theorem atot6601 : totK PA10K2 A10K2.u6601 = [0, 1602700457968, 9071742679861, 21082979167924, 25772093606052, 15461057553876, 3703152142639, 333192676350, 6354482628, 0] := by
  rw [show A10K2.u6601 = KTree.node A10K2.u6593 (nat_lit 108450180) (nat_lit 9133102325) (nat_lit 0) A10K2.u6600 from rfl, totK_node, atot6593, atot6600]
  decide +kernel

theorem arows6616 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6616 = true := by
  rw [show A10K2.u6616 = KTree.node A10K2.u6608 (nat_lit 108618240) (nat_lit 15596688358) (nat_lit 0) A10K2.u6615 from rfl, allE_node, arows6608, irow6616, arows6615]
  all_goals rfl

theorem atot6616 : totK PA10K2 A10K2.u6616 = [0, 2183007671712, 12512782149951, 26787384428325, 25487288328124, 9803564694935, 1285094056304, 44205990376, 0, 0] := by
  rw [show A10K2.u6616 = KTree.node A10K2.u6608 (nat_lit 108618240) (nat_lit 15596688358) (nat_lit 0) A10K2.u6615 from rfl, totK_node, atot6608, atot6615]
  decide +kernel

theorem arows6632 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6632 = true := by
  rw [show A10K2.u6632 = KTree.node A10K2.u6624 (nat_lit 108752020) (nat_lit 9343414493) (nat_lit 0) A10K2.u6631 from rfl, allE_node, arows6624, irow6632, arows6631]
  all_goals rfl

theorem atot6632 : totK PA10K2 A10K2.u6632 = [0, 2347203525858, 13636690245133, 28791118547847, 25612499364176, 8728246866597, 855437705893, 13679205470, 0, 0] := by
  rw [show A10K2.u6632 = KTree.node A10K2.u6624 (nat_lit 108752020) (nat_lit 9343414493) (nat_lit 0) A10K2.u6631 from rfl, totK_node, atot6624, atot6631]
  decide +kernel

theorem arows6647 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6647 = true := by
  rw [show A10K2.u6647 = KTree.node A10K2.u6639 (nat_lit 113271110) (nat_lit 11785411376) (nat_lit 0) A10K2.u6646 from rfl, allE_node, arows6639, irow6647, arows6646]
  all_goals rfl

theorem atot6647 : totK PA10K2 A10K2.u6647 = [2231826234337, 11809077488475, 23289789304572, 21871567620270, 12011886339288, 4924012321857, 1010289274565, 61110126106, 0, 0] := by
  rw [show A10K2.u6647 = KTree.node A10K2.u6639 (nat_lit 113271110) (nat_lit 11785411376) (nat_lit 0) A10K2.u6646 from rfl, totK_node, atot6639, atot6646]
  decide +kernel

theorem arows6667 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6667 = true := by
  rw [show A10K2.u6667 = KTree.node A10K2.u6659 (nat_lit 113426547) (nat_lit 1444371908) (nat_lit 0) A10K2.u6666 from rfl, allE_node, arows6659, irow6667, arows6666]
  all_goals rfl

theorem atot6667 : totK PA10K2 A10K2.u6667 = [3405682775673, 17055798505545, 30127868063177, 21548890650793, 5664075303860, 554088834107, 11900787601, 0, 0, 0] := by
  rw [show A10K2.u6667 = KTree.node A10K2.u6659 (nat_lit 113426547) (nat_lit 1444371908) (nat_lit 0) A10K2.u6666 from rfl, totK_node, atot6659, atot6666]
  decide +kernel

theorem arows6682 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6682 = true := by
  rw [show A10K2.u6682 = KTree.node A10K2.u6674 (nat_lit 113501979) (nat_lit 9838264813) (nat_lit 0) A10K2.u6681 from rfl, allE_node, arows6674, irow6682, arows6681]
  all_goals rfl

theorem atot6682 : totK PA10K2 A10K2.u6682 = [165731654200, 5672836753943, 22439052154330, 31206484172747, 16150046901748, 2622902149464, 111598773623, 0, 0, 0] := by
  rw [show A10K2.u6682 = KTree.node A10K2.u6674 (nat_lit 113501979) (nat_lit 9838264813) (nat_lit 0) A10K2.u6681 from rfl, totK_node, atot6674, atot6681]
  decide +kernel

theorem arows6698 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6698 = true := by
  rw [show A10K2.u6698 = KTree.node A10K2.u6690 (nat_lit 113566277) (nat_lit 5624454250) (nat_lit 0) A10K2.u6697 from rfl, allE_node, arows6690, irow6698, arows6697]
  all_goals rfl

theorem atot6698 : totK PA10K2 A10K2.u6698 = [0, 1822925243264, 12485889695809, 28386600576377, 25130118903512, 8134136167771, 982804592537, 36134558889, 0, 0] := by
  rw [show A10K2.u6698 = KTree.node A10K2.u6690 (nat_lit 113566277) (nat_lit 5624454250) (nat_lit 0) A10K2.u6697 from rfl, totK_node, atot6690, atot6697]
  decide +kernel

theorem arows6713 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6713 = true := by
  rw [show A10K2.u6713 = KTree.node A10K2.u6705 (nat_lit 113734558) (nat_lit 14990867186) (nat_lit 0) A10K2.u6712 from rfl, allE_node, arows6705, irow6713, arows6712]
  all_goals rfl

theorem atot6713 : totK PA10K2 A10K2.u6713 = [2238164317933, 11885977809119, 24061840341862, 24047305078292, 12845364707902, 3138332414403, 280864616360, 5676195732, 0, 0] := by
  rw [show A10K2.u6713 = KTree.node A10K2.u6705 (nat_lit 113734558) (nat_lit 14990867186) (nat_lit 0) A10K2.u6712 from rfl, totK_node, atot6705, atot6712]
  decide +kernel

theorem arows6730 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6730 = true := by
  rw [show A10K2.u6730 = KTree.node A10K2.u6722 (nat_lit 113896992) (nat_lit 10008485991) (nat_lit 0) A10K2.u6729 from rfl, allE_node, arows6722, irow6730, arows6729]
  all_goals rfl

theorem atot6730 : totK PA10K2 A10K2.u6730 = [1323934157412, 10514588775737, 27189447498173, 27686183540701, 9948882470176, 1140286022023, 37204059898, 0, 0, 0] := by
  rw [show A10K2.u6730 = KTree.node A10K2.u6722 (nat_lit 113896992) (nat_lit 10008485991) (nat_lit 0) A10K2.u6729 from rfl, totK_node, atot6722, atot6729]
  decide +kernel

theorem arows6745 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6745 = true := by
  rw [show A10K2.u6745 = KTree.node A10K2.u6737 (nat_lit 113997266) (nat_lit 15365736412) (nat_lit 0) A10K2.u6744 from rfl, allE_node, arows6737, irow6745, arows6744]
  all_goals rfl

theorem atot6745 : totK PA10K2 A10K2.u6745 = [2253625996168, 12778834660850, 27123531129957, 25756463176606, 10290926742186, 1306296181064, 26373394822, 0, 0, 0] := by
  rw [show A10K2.u6745 = KTree.node A10K2.u6737 (nat_lit 113997266) (nat_lit 15365736412) (nat_lit 0) A10K2.u6744 from rfl, totK_node, atot6737, atot6744]
  decide +kernel

theorem arows6761 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6761 = true := by
  rw [show A10K2.u6761 = KTree.node A10K2.u6753 (nat_lit 114127240) (nat_lit 13209203202) (nat_lit 0) A10K2.u6760 from rfl, allE_node, arows6753, irow6761, arows6760]
  all_goals rfl

theorem atot6761 : totK PA10K2 A10K2.u6761 = [0, 2541131481759, 13795322063130, 27858741322475, 24030152763085, 8150077212450, 1005137957788, 36704093874, 0, 0] := by
  rw [show A10K2.u6761 = KTree.node A10K2.u6753 (nat_lit 114127240) (nat_lit 13209203202) (nat_lit 0) A10K2.u6760 from rfl, totK_node, atot6753, atot6760]
  decide +kernel

theorem arows6776 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6776 = true := by
  rw [show A10K2.u6776 = KTree.node A10K2.u6768 (nat_lit 114229633) (nat_lit 10422756214) (nat_lit 0) A10K2.u6775 from rfl, allE_node, arows6768, irow6776, arows6775]
  all_goals rfl

theorem atot6776 : totK PA10K2 A10K2.u6776 = [0, 3271189187264, 17305657390995, 31104498441117, 21523925939160, 4963997640982, 363265427281, 6239673734, 0, 0] := by
  rw [show A10K2.u6776 = KTree.node A10K2.u6768 (nat_lit 114229633) (nat_lit 10422756214) (nat_lit 0) A10K2.u6775 from rfl, totK_node, atot6768, atot6775]
  decide +kernel

theorem arows6794 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6794 = true := by
  rw [show A10K2.u6794 = KTree.node A10K2.u6786 (nat_lit 114851770) (nat_lit 13787922445) (nat_lit 0) A10K2.u6793 from rfl, allE_node, arows6786, irow6794, arows6793]
  all_goals rfl

theorem atot6794 : totK PA10K2 A10K2.u6794 = [2892010650422, 14911389241972, 27854406352660, 22786731768110, 8031707426444, 1281289279417, 79484392320, 0, 0, 0] := by
  rw [show A10K2.u6794 = KTree.node A10K2.u6786 (nat_lit 114851770) (nat_lit 13787922445) (nat_lit 0) A10K2.u6793 from rfl, totK_node, atot6786, atot6793]
  decide +kernel

theorem arows6809 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6809 = true := by
  rw [show A10K2.u6809 = KTree.node A10K2.u6801 (nat_lit 114931154) (nat_lit 15449247974) (nat_lit 0) A10K2.u6808 from rfl, allE_node, arows6801, irow6809, arows6808]
  all_goals rfl

theorem atot6809 : totK PA10K2 A10K2.u6809 = [2577340011055, 14107457022719, 28156477684727, 24053478271092, 8230614913585, 1008966203076, 37204059898, 0, 0, 0] := by
  rw [show A10K2.u6809 = KTree.node A10K2.u6801 (nat_lit 114931154) (nat_lit 15449247974) (nat_lit 0) A10K2.u6808 from rfl, totK_node, atot6801, atot6808]
  decide +kernel

theorem arows6825 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6825 = true := by
  rw [show A10K2.u6825 = KTree.node A10K2.u6817 (nat_lit 115056091) (nat_lit 5820006244) (nat_lit 0) A10K2.u6824 from rfl, allE_node, arows6817, irow6825, arows6824]
  all_goals rfl

theorem atot6825 : totK PA10K2 A10K2.u6825 = [1124207821172, 9128528688612, 25163735972741, 28727134399201, 12909462076405, 1916212927843, 75062079822, 0, 0, 0] := by
  rw [show A10K2.u6825 = KTree.node A10K2.u6817 (nat_lit 115056091) (nat_lit 5820006244) (nat_lit 0) A10K2.u6824 from rfl, totK_node, atot6817, atot6824]
  decide +kernel

theorem arows6840 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6840 = true := by
  rw [show A10K2.u6840 = KTree.node A10K2.u6832 (nat_lit 115118663) (nat_lit 9832245233) (nat_lit 0) A10K2.u6839 from rfl, allE_node, arows6832, irow6840, arows6839]
  all_goals rfl

theorem atot6840 : totK PA10K2 A10K2.u6840 = [0, 2744638052841, 15184533141720, 29666666305457, 23282388822430, 6459833660517, 545008656137, 7007974415, 0, 0] := by
  rw [show A10K2.u6840 = KTree.node A10K2.u6832 (nat_lit 115118663) (nat_lit 9832245233) (nat_lit 0) A10K2.u6839 from rfl, totK_node, atot6832, atot6839]
  decide +kernel

theorem arows6857 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6857 = true := by
  rw [show A10K2.u6857 = KTree.node A10K2.u6849 (nat_lit 115278081) (nat_lit 10404522250) (nat_lit 0) A10K2.u6856 from rfl, allE_node, arows6849, irow6857, arows6856]
  all_goals rfl

theorem atot6857 : totK PA10K2 A10K2.u6857 = [0, 3035014609315, 16184199830198, 30330869226102, 23016007402315, 6205337453284, 504206630911, 7151180950, 0, 0] := by
  rw [show A10K2.u6857 = KTree.node A10K2.u6849 (nat_lit 115278081) (nat_lit 10404522250) (nat_lit 0) A10K2.u6856 from rfl, totK_node, atot6849, atot6856]
  decide +kernel

theorem arows6872 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6872 = true := by
  rw [show A10K2.u6872 = KTree.node A10K2.u6864 (nat_lit 115340160) (nat_lit 15096893104) (nat_lit 0) A10K2.u6871 from rfl, allE_node, arows6864, irow6872, arows6871]
  all_goals rfl

theorem atot6872 : totK PA10K2 A10K2.u6872 = [0, 2231826234337, 12318441962727, 25888252952695, 25118850007745, 10785141347743, 1650188075472, 73776485728, 0, 0] := by
  rw [show A10K2.u6872 = KTree.node A10K2.u6864 (nat_lit 115340160) (nat_lit 15096893104) (nat_lit 0) A10K2.u6871 from rfl, totK_node, atot6864, atot6871]
  decide +kernel

theorem arows6888 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6888 = true := by
  rw [show A10K2.u6888 = KTree.node A10K2.u6880 (nat_lit 115404388) (nat_lit 8448881649) (nat_lit 0) A10K2.u6887 from rfl, allE_node, arows6880, irow6888, arows6887]
  all_goals rfl

theorem atot6888 : totK PA10K2 A10K2.u6888 = [0, 1318949507170, 10460170377047, 27158312378659, 27458160703931, 9586645459677, 1107396165197, 36196801203, 0, 0] := by
  rw [show A10K2.u6888 = KTree.node A10K2.u6880 (nat_lit 115404388) (nat_lit 8448881649) (nat_lit 0) A10K2.u6887 from rfl, totK_node, atot6880, atot6887]
  decide +kernel

theorem arows6903 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6903 = true := by
  rw [show A10K2.u6903 = KTree.node A10K2.u6895 (nat_lit 115570560) (nat_lit 13700452529) (nat_lit 0) A10K2.u6902 from rfl, allE_node, arows6895, irow6903, arows6902]
  all_goals rfl

theorem atot6903 : totK PA10K2 A10K2.u6903 = [0, 2252464922703, 12762271493482, 27064131996330, 25801361926522, 10229677967158, 1181852179506, 25714663954, 0, 0] := by
  rw [show A10K2.u6903 = KTree.node A10K2.u6895 (nat_lit 115570560) (nat_lit 13700452529) (nat_lit 0) A10K2.u6902 from rfl, totK_node, atot6895, atot6902]
  decide +kernel

theorem arows6922 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6922 = true := by
  rw [show A10K2.u6922 = KTree.node A10K2.u6914 (nat_lit 115634672) (nat_lit 14075027958) (nat_lit 0) A10K2.u6921 from rfl, allE_node, arows6914, irow6922, arows6921]
  all_goals rfl

theorem atot6922 : totK PA10K2 A10K2.u6922 = [0, 0, 2991204473914, 16039274444849, 29803437706763, 22014206237005, 5862582977470, 520648953284, 7237400819, 0] := by
  rw [show A10K2.u6922 = KTree.node A10K2.u6914 (nat_lit 115634672) (nat_lit 14075027958) (nat_lit 0) A10K2.u6921 from rfl, totK_node, atot6914, atot6921]
  decide +kernel

theorem arows6937 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6937 = true := by
  rw [show A10K2.u6937 = KTree.node A10K2.u6929 (nat_lit 115828158) (nat_lit 16292101936) (nat_lit 0) A10K2.u6936 from rfl, allE_node, arows6929, irow6937, arows6936]
  all_goals rfl

theorem atot6937 : totK PA10K2 A10K2.u6937 = [0, 1624997771604, 9832444539952, 23805476307729, 27040639005100, 13217743022564, 2207965103075, 93516990493, 0, 0] := by
  rw [show A10K2.u6937 = KTree.node A10K2.u6929 (nat_lit 115828158) (nat_lit 16292101936) (nat_lit 0) A10K2.u6936 from rfl, totK_node, atot6929, atot6936]
  decide +kernel

theorem arows6953 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6953 = true := by
  rw [show A10K2.u6953 = KTree.node A10K2.u6945 (nat_lit 115989036) (nat_lit 12629208085) (nat_lit 0) A10K2.u6952 from rfl, allE_node, arows6945, irow6953, arows6952]
  all_goals rfl

theorem atot6953 : totK PA10K2 A10K2.u6953 = [0, 1937100703741, 12551908532521, 27942333017964, 25684238177189, 8955367997567, 1058311546695, 36968589557, 0, 0] := by
  rw [show A10K2.u6953 = KTree.node A10K2.u6945 (nat_lit 115989036) (nat_lit 12629208085) (nat_lit 0) A10K2.u6952 from rfl, totK_node, atot6945, atot6952]
  decide +kernel

theorem arows6968 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6968 = true := by
  rw [show A10K2.u6968 = KTree.node A10K2.u6960 (nat_lit 116091954) (nat_lit 11922706525) (nat_lit 0) A10K2.u6967 from rfl, allE_node, arows6960, irow6968, arows6967]
  all_goals rfl

theorem atot6968 : totK PA10K2 A10K2.u6968 = [0, 2253625996168, 13004454062630, 27789916657413, 25691798984165, 9330293043169, 1012808435641, 20033688098, 0, 0] := by
  rw [show A10K2.u6968 = KTree.node A10K2.u6960 (nat_lit 116091954) (nat_lit 11922706525) (nat_lit 0) A10K2.u6967 from rfl, totK_node, atot6960, atot6967]
  decide +kernel

theorem arows6985 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u6985 = true := by
  rw [show A10K2.u6985 = KTree.node A10K2.u6977 (nat_lit 116221147) (nat_lit 9760440877) (nat_lit 0) A10K2.u6984 from rfl, allE_node, arows6977, irow6985, arows6984]
  all_goals rfl

theorem atot6985 : totK PA10K2 A10K2.u6985 = [0, 0, 2865381601627, 15405657112078, 29785323911816, 23132076105965, 6249960452538, 531929651065, 7380853412, 0] := by
  rw [show A10K2.u6985 = KTree.node A10K2.u6977 (nat_lit 116221147) (nat_lit 9760440877) (nat_lit 0) A10K2.u6984 from rfl, totK_node, atot6977, atot6984]
  decide +kernel

theorem arows7000 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7000 = true := by
  rw [show A10K2.u7000 = KTree.node A10K2.u6992 (nat_lit 116351024) (nat_lit 15045118921) (nat_lit 0) A10K2.u6999 from rfl, allE_node, arows6992, irow7000, arows6999]
  all_goals rfl

theorem atot7000 : totK PA10K2 A10K2.u7000 = [0, 1427351586688, 9538098351847, 24130129073626, 27546156017174, 13296388752559, 2153635594489, 88154479705, 0, 0] := by
  rw [show A10K2.u7000 = KTree.node A10K2.u6992 (nat_lit 116351024) (nat_lit 15045118921) (nat_lit 0) A10K2.u6999 from rfl, totK_node, atot6992, atot6999]
  decide +kernel

theorem arows7016 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7016 = true := by
  rw [show A10K2.u7016 = KTree.node A10K2.u7008 (nat_lit 116974838) (nat_lit 16070085294) (nat_lit 0) A10K2.u7015 from rfl, allE_node, arows7008, irow7016, arows7015]
  all_goals rfl

theorem atot7016 : totK PA10K2 A10K2.u7016 = [0, 2741970490149, 14917707278943, 29164928355840, 23831150242151, 7382976386715, 717339887582, 12477124820, 0, 0] := by
  rw [show A10K2.u7016 = KTree.node A10K2.u7008 (nat_lit 116974838) (nat_lit 16070085294) (nat_lit 0) A10K2.u7015 from rfl, totK_node, atot7008, atot7015]
  decide +kernel

theorem arows7031 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7031 = true := by
  rw [show A10K2.u7031 = KTree.node A10K2.u7023 (nat_lit 117116535) (nat_lit 14459905030) (nat_lit 0) A10K2.u7030 from rfl, allE_node, arows7023, irow7031, arows7030]
  all_goals rfl

theorem atot7031 : totK PA10K2 A10K2.u7031 = [0, 2424236405812, 13907511738775, 28623737832629, 24756634458780, 8084294471730, 773118199197, 12696458652, 0, 0] := by
  rw [show A10K2.u7031 = KTree.node A10K2.u7023 (nat_lit 117116535) (nat_lit 14459905030) (nat_lit 0) A10K2.u7030 from rfl, totK_node, atot7023, atot7030]
  decide +kernel

theorem arows7049 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7049 = true := by
  rw [show A10K2.u7049 = KTree.node A10K2.u7041 (nat_lit 117177740) (nat_lit 6339225081) (nat_lit 0) A10K2.u7048 from rfl, allE_node, arows7041, irow7049, arows7048]
  all_goals rfl

theorem atot7049 : totK PA10K2 A10K2.u7049 = [0, 0, 4308318245609, 20396425176106, 32056969287328, 18477120644860, 3262578563716, 149891021453, 0, 0] := by
  rw [show A10K2.u7049 = KTree.node A10K2.u7041 (nat_lit 117177740) (nat_lit 6339225081) (nat_lit 0) A10K2.u7048 from rfl, totK_node, atot7041, atot7048]
  decide +kernel

theorem arows7064 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7064 = true := by
  rw [show A10K2.u7064 = KTree.node A10K2.u7056 (nat_lit 117262166) (nat_lit 10781426821) (nat_lit 0) A10K2.u7063 from rfl, allE_node, arows7056, irow7064, arows7063]
  all_goals rfl

theorem atot7064 : totK PA10K2 A10K2.u7064 = [0, 0, 2081414072245, 13383878547453, 29336129308228, 25602411553420, 7594791718250, 659916102853, 13585869933, 0] := by
  rw [show A10K2.u7064 = KTree.node A10K2.u7056 (nat_lit 117262166) (nat_lit 10781426821) (nat_lit 0) A10K2.u7063 from rfl, totK_node, atot7056, atot7063]
  decide +kernel

theorem arows7080 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7080 = true := by
  rw [show A10K2.u7080 = KTree.node A10K2.u7072 (nat_lit 117404154) (nat_lit 12455262960) (nat_lit 0) A10K2.u7079 from rfl, allE_node, arows7072, irow7080, arows7079]
  all_goals rfl

theorem atot7080 : totK PA10K2 A10K2.u7080 = [0, 0, 2407789929719, 13668771604058, 28364442782840, 25131304011910, 8106697221197, 780077243497, 12758098799, 0] := by
  rw [show A10K2.u7080 = KTree.node A10K2.u7072 (nat_lit 117404154) (nat_lit 12455262960) (nat_lit 0) A10K2.u7079 from rfl, totK_node, atot7072, atot7079]
  decide +kernel

theorem arows7095 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7095 = true := by
  rw [show A10K2.u7095 = KTree.node A10K2.u7087 (nat_lit 117466569) (nat_lit 6637225323) (nat_lit 0) A10K2.u7094 from rfl, allE_node, arows7087, irow7095, arows7094]
  all_goals rfl

theorem atot7095 : totK PA10K2 A10K2.u7095 = [0, 2339048713180, 12614470156470, 24740295842428, 21646953263331, 10036027426148, 4061725835844, 946338611571, 61018386929, 0] := by
  rw [show A10K2.u7095 = KTree.node A10K2.u7087 (nat_lit 117466569) (nat_lit 6637225323) (nat_lit 0) A10K2.u7094 from rfl, totK_node, atot7087, atot7094]
  decide +kernel

theorem arows7112 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7112 = true := by
  rw [show A10K2.u7112 = KTree.node A10K2.u7104 (nat_lit 117604637) (nat_lit 6199480913) (nat_lit 0) A10K2.u7111 from rfl, allE_node, arows7104, irow7112, arows7111]
  all_goals rfl

theorem atot7112 : totK PA10K2 A10K2.u7112 = [0, 3112623060759, 16136734698705, 29795631464000, 22240070309997, 5640443313709, 422578747529, 6354482628, 0, 0] := by
  rw [show A10K2.u7112 = KTree.node A10K2.u7104 (nat_lit 117604637) (nat_lit 6199480913) (nat_lit 0) A10K2.u7111 from rfl, totK_node, atot7104, atot7111]
  decide +kernel

theorem arows7127 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7127 = true := by
  rw [show A10K2.u7127 = KTree.node A10K2.u7119 (nat_lit 117682107) (nat_lit 6755606656) (nat_lit 0) A10K2.u7126 from rfl, allE_node, arows7119, irow7127, arows7126]
  all_goals rfl

theorem atot7127 : totK PA10K2 A10K2.u7127 = [0, 845700278790, 8098931164978, 24189853552909, 29568361803155, 14497092622312, 2375557691521, 105893753708, 0, 0] := by
  rw [show A10K2.u7127 = KTree.node A10K2.u7119 (nat_lit 117682107) (nat_lit 6755606656) (nat_lit 0) A10K2.u7126 from rfl, totK_node, atot7119, atot7126]
  decide +kernel

theorem arows7143 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7143 = true := by
  rw [show A10K2.u7143 = KTree.node A10K2.u7135 (nat_lit 117752385) (nat_lit 10282547901) (nat_lit 0) A10K2.u7142 from rfl, allE_node, arows7135, irow7143, arows7142]
  all_goals rfl

theorem atot7143 : totK PA10K2 A10K2.u7143 = [0, 0, 2630908036854, 14365923234748, 28137132259145, 22668682586711, 7244941779913, 924904139880, 36134558889, 0] := by
  rw [show A10K2.u7143 = KTree.node A10K2.u7135 (nat_lit 117752385) (nat_lit 10282547901) (nat_lit 0) A10K2.u7142 from rfl, totK_node, atot7135, atot7142]
  decide +kernel

theorem arows7158 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7158 = true := by
  rw [show A10K2.u7158 = KTree.node A10K2.u7150 (nat_lit 117904135) (nat_lit 9249131015) (nat_lit 0) A10K2.u7157 from rfl, allE_node, arows7150, irow7158, arows7157]
  all_goals rfl

theorem atot7158 : totK PA10K2 A10K2.u7158 = [0, 839403861465, 5756503567667, 17926850550675, 28256055925763, 19787886019556, 4732199936026, 368906305970, 5676195732, 0] := by
  rw [show A10K2.u7158 = KTree.node A10K2.u7150 (nat_lit 117904135) (nat_lit 9249131015) (nat_lit 0) A10K2.u7157 from rfl, totK_node, atot7150, atot7157]
  decide +kernel

theorem arows7179 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7179 = true := by
  rw [show A10K2.u7179 = KTree.node A10K2.u7171 (nat_lit 118526757) (nat_lit 7130481161) (nat_lit 0) A10K2.u7178 from rfl, allE_node, arows7171, irow7179, arows7178]
  all_goals rfl

theorem atot7179 : totK PA10K2 A10K2.u7179 = [0, 2562092438069, 13925731483813, 27910619434080, 23955290015992, 7939171537184, 953222398956, 36196801203, 0, 0] := by
  rw [show A10K2.u7179 = KTree.node A10K2.u7171 (nat_lit 118526757) (nat_lit 7130481161) (nat_lit 0) A10K2.u7178 from rfl, totK_node, atot7171, atot7178]
  decide +kernel

theorem arows7194 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7194 = true := by
  rw [show A10K2.u7194 = KTree.node A10K2.u7186 (nat_lit 118671524) (nat_lit 13773832359) (nat_lit 0) A10K2.u7193 from rfl, allE_node, arows7186, irow7194, arows7193]
  all_goals rfl

theorem atot7194 : totK PA10K2 A10K2.u7194 = [0, 928536070374, 9268838259599, 26264721340238, 28014406151293, 10359887311604, 1291825896888, 43527332123, 0, 0] := by
  rw [show A10K2.u7194 = KTree.node A10K2.u7186 (nat_lit 118671524) (nat_lit 13773832359) (nat_lit 0) A10K2.u7193 from rfl, totK_node, atot7186, atot7193]
  decide +kernel

theorem arows7210 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7210 = true := by
  rw [show A10K2.u7210 = KTree.node A10K2.u7202 (nat_lit 118904894) (nat_lit 8165067903) (nat_lit 0) A10K2.u7209 from rfl, allE_node, arows7202, irow7210, arows7209]
  all_goals rfl

theorem atot7210 : totK PA10K2 A10K2.u7210 = [0, 835923233680, 5888045937121, 18458914301545, 28322531935542, 18002176586911, 3972167474062, 312805982935, 6354482628, 0] := by
  rw [show A10K2.u7210 = KTree.node A10K2.u7202 (nat_lit 118904894) (nat_lit 8165067903) (nat_lit 0) A10K2.u7209 from rfl, totK_node, atot7202, atot7209]
  decide +kernel

theorem arows7225 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7225 = true := by
  rw [show A10K2.u7225 = KTree.node A10K2.u7217 (nat_lit 119053320) (nat_lit 14462297835) (nat_lit 0) A10K2.u7224 from rfl, allE_node, arows7217, irow7225, arows7224]
  all_goals rfl

theorem atot7225 : totK PA10K2 A10K2.u7225 = [0, 2947787882094, 15240358791412, 28736783487070, 23432679703690, 7639378707779, 953877476667, 36196801203, 0, 0] := by
  rw [show A10K2.u7225 = KTree.node A10K2.u7217 (nat_lit 119053320) (nat_lit 14462297835) (nat_lit 0) A10K2.u7224 from rfl, totK_node, atot7217, atot7224]
  decide +kernel

theorem arows7242 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7242 = true := by
  rw [show A10K2.u7242 = KTree.node A10K2.u7234 (nat_lit 119214862) (nat_lit 9728122146) (nat_lit 0) A10K2.u7241 from rfl, allE_node, arows7234, irow7242, arows7241]
  all_goals rfl

theorem atot7242 : totK PA10K2 A10K2.u7242 = [0, 2346766361561, 14169356292136, 29876387841799, 25400379018737, 7808813994968, 746218993293, 13576218110, 0, 0] := by
  rw [show A10K2.u7242 = KTree.node A10K2.u7234 (nat_lit 119214862) (nat_lit 9728122146) (nat_lit 0) A10K2.u7241 from rfl, totK_node, atot7234, atot7241]
  decide +kernel

theorem arows7257 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7257 = true := by
  rw [show A10K2.u7257 = KTree.node A10K2.u7249 (nat_lit 119278094) (nat_lit 11762319368) (nat_lit 0) A10K2.u7256 from rfl, allE_node, arows7249, irow7257, arows7256]
  all_goals rfl

theorem atot7257 : totK PA10K2 A10K2.u7257 = [0, 0, 3743665198565, 18910077221124, 32046539261359, 20048106271324, 3952283110735, 199474213002, 0, 0] := by
  rw [show A10K2.u7257 = KTree.node A10K2.u7249 (nat_lit 119278094) (nat_lit 11762319368) (nat_lit 0) A10K2.u7256 from rfl, totK_node, atot7249, atot7256]
  decide +kernel

theorem arows7273 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7273 = true := by
  rw [show A10K2.u7273 = KTree.node A10K2.u7265 (nat_lit 119367324) (nat_lit 10918137108) (nat_lit 0) A10K2.u7272 from rfl, allE_node, arows7265, irow7273, arows7272]
  all_goals rfl

theorem atot7273 : totK PA10K2 A10K2.u7273 = [0, 0, 2382562630947, 13666749182009, 28873814241610, 26009163558382, 8360607314539, 789329086160, 14159155365, 0] := by
  rw [show A10K2.u7273 = KTree.node A10K2.u7265 (nat_lit 119367324) (nat_lit 10918137108) (nat_lit 0) A10K2.u7272 from rfl, totK_node, atot7265, atot7272]
  decide +kernel

theorem arows7288 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7288 = true := by
  rw [show A10K2.u7288 = KTree.node A10K2.u7280 (nat_lit 119507972) (nat_lit 10228656735) (nat_lit 0) A10K2.u7287 from rfl, allE_node, arows7280, irow7288, arows7287]
  all_goals rfl

theorem atot7288 : totK PA10K2 A10K2.u7288 = [0, 0, 1995573685863, 11833068383849, 26575027204597, 26593090301573, 10988930510388, 1644363756575, 73776485728, 0] := by
  rw [show A10K2.u7288 = KTree.node A10K2.u7280 (nat_lit 119507972) (nat_lit 10228656735) (nat_lit 0) A10K2.u7287 from rfl, totK_node, atot7280, atot7287]
  decide +kernel

theorem arows7306 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7306 = true := by
  rw [show A10K2.u7306 = KTree.node A10K2.u7298 (nat_lit 119570467) (nat_lit 6096870732) (nat_lit 0) A10K2.u7305 from rfl, allE_node, arows7298, irow7306, arows7305]
  all_goals rfl

theorem atot7306 : totK PA10K2 A10K2.u7306 = [0, 0, 2487922856643, 13921406263697, 27849025669975, 23500039291991, 7807404402277, 957755710726, 36196801203, 0] := by
  rw [show A10K2.u7306 = KTree.node A10K2.u7298 (nat_lit 119570467) (nat_lit 6096870732) (nat_lit 0) A10K2.u7305 from rfl, totK_node, atot7298, atot7305]
  decide +kernel

theorem arows7321 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7321 = true := by
  rw [show A10K2.u7321 = KTree.node A10K2.u7313 (nat_lit 119719277) (nat_lit 6382360939) (nat_lit 0) A10K2.u7320 from rfl, allE_node, arows7313, irow7321, arows7320]
  all_goals rfl

theorem atot7321 : totK PA10K2 A10K2.u7321 = [0, 0, 3381326935015, 17254281345771, 30734938011306, 21163789119857, 4661190116038, 350722166347, 5976421810, 0] := by
  rw [show A10K2.u7321 = KTree.node A10K2.u7313 (nat_lit 119719277) (nat_lit 6382360939) (nat_lit 0) A10K2.u7320 from rfl, totK_node, atot7313, atot7320]
  decide +kernel

theorem arows7337 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7337 = true := by
  rw [show A10K2.u7337 = KTree.node A10K2.u7329 (nat_lit 119799191) (nat_lit 14616934806) (nat_lit 0) A10K2.u7336 from rfl, allE_node, arows7329, irow7337, arows7336]
  all_goals rfl

theorem atot7337 : totK PA10K2 A10K2.u7337 = [0, 0, 0, 5331438055334, 23076797327981, 32169775821598, 15421200095030, 2290576139822, 84865518449, 0] := by
  rw [show A10K2.u7337 = KTree.node A10K2.u7329 (nat_lit 119799191) (nat_lit 14616934806) (nat_lit 0) A10K2.u7336 from rfl, totK_node, atot7329, atot7336]
  decide +kernel

theorem arows7352 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7352 = true := by
  rw [show A10K2.u7352 = KTree.node A10K2.u7344 (nat_lit 119937312) (nat_lit 13011022447) (nat_lit 0) A10K2.u7351 from rfl, allE_node, arows7344, irow7352, arows7351]
  all_goals rfl

theorem atot7352 : totK PA10K2 A10K2.u7352 = [0, 0, 0, 3763148235362, 18084800982174, 30282924082107, 19641519690469, 4919858228667, 458953710825, 7903172220] := by
  rw [show A10K2.u7352 = KTree.node A10K2.u7344 (nat_lit 119937312) (nat_lit 13011022447) (nat_lit 0) A10K2.u7351 from rfl, totK_node, atot7344, atot7351]
  decide +kernel

theorem arows7369 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7369 = true := by
  rw [show A10K2.u7369 = KTree.node A10K2.u7361 (nat_lit 120611766) (nat_lit 16784593185) (nat_lit 0) A10K2.u7368 from rfl, allE_node, arows7361, irow7369, arows7368]
  all_goals rfl

theorem atot7369 : totK PA10K2 A10K2.u7369 = [0, 0, 2943603500681, 15363470396029, 28830022921023, 22604345512552, 7063615708885, 952578093763, 41049666843, 0] := by
  rw [show A10K2.u7369 = KTree.node A10K2.u7361 (nat_lit 120611766) (nat_lit 16784593185) (nat_lit 0) A10K2.u7368 from rfl, totK_node, atot7361, atot7368]
  decide +kernel

theorem arows7384 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7384 = true := by
  rw [show A10K2.u7384 = KTree.node A10K2.u7376 (nat_lit 120760243) (nat_lit 9405989294) (nat_lit 0) A10K2.u7383 from rfl, allE_node, arows7376, irow7384, arows7383]
  all_goals rfl

theorem atot7384 : totK PA10K2 A10K2.u7384 = [0, 0, 2754898913470, 15496414482770, 30136773423795, 22076855474265, 4973012353779, 375171133749, 6354482628, 0] := by
  rw [show A10K2.u7384 = KTree.node A10K2.u7376 (nat_lit 120760243) (nat_lit 9405989294) (nat_lit 0) A10K2.u7383 from rfl, totK_node, atot7376, atot7383]
  decide +kernel

theorem arows7400 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7400 = true := by
  rw [show A10K2.u7400 = KTree.node A10K2.u7392 (nat_lit 121169619) (nat_lit 10055765055) (nat_lit 0) A10K2.u7399 from rfl, allE_node, arows7392, irow7400, arows7399]
  all_goals rfl

theorem atot7400 : totK PA10K2 A10K2.u7400 = [0, 0, 2400184610980, 14285429581381, 29822532541929, 25502719560940, 7701486348193, 722121982336, 13364899180, 0] := by
  rw [show A10K2.u7400 = KTree.node A10K2.u7392 (nat_lit 121169619) (nat_lit 10055765055) (nat_lit 0) A10K2.u7399 from rfl, totK_node, atot7392, atot7399]
  decide +kernel

theorem arows7415 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7415 = true := by
  rw [show A10K2.u7415 = KTree.node A10K2.u7407 (nat_lit 121332077) (nat_lit 3059592127) (nat_lit 32) A10K2.u7414 from rfl, allE_node, arows7407, irow7415, arows7414]
  all_goals rfl

theorem atot7415 : totK PA10K2 A10K2.u7415 = [0, 0, 2346766361561, 13247569473109, 28174426161691, 25947903748418, 9369843591993, 981387429705, 21052137078, 0] := by
  rw [show A10K2.u7415 = KTree.node A10K2.u7407 (nat_lit 121332077) (nat_lit 3059592127) (nat_lit 32) A10K2.u7414 from rfl, totK_node, atot7407, atot7414]
  decide +kernel

theorem arows7434 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7434 = true := by
  rw [show A10K2.u7434 = KTree.node A10K2.u7426 (nat_lit 122243424) (nat_lit 12213653678) (nat_lit 0) A10K2.u7433 from rfl, allE_node, arows7426, irow7434, arows7433]
  all_goals rfl

theorem atot7434 : totK PA10K2 A10K2.u7434 = [0, 2344179177151, 12176180422361, 23183866209234, 21266393417070, 12385156124878, 5346285481154, 1060824572261, 61110126106, 0] := by
  rw [show A10K2.u7434 = KTree.node A10K2.u7426 (nat_lit 122243424) (nat_lit 12213653678) (nat_lit 0) A10K2.u7433 from rfl, totK_node, atot7426, atot7433]
  decide +kernel

theorem arows7449 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7449 = true := by
  rw [show A10K2.u7449 = KTree.node A10K2.u7441 (nat_lit 122307988) (nat_lit 9300682144) (nat_lit 0) A10K2.u7448 from rfl, allE_node, arows7441, irow7449, arows7448]
  all_goals rfl

theorem atot7449 : totK PA10K2 A10K2.u7449 = [0, 2304506188524, 13526208580584, 28494320714275, 24591898754755, 7365999789335, 659133350987, 12475655917, 0, 0] := by
  rw [show A10K2.u7449 = KTree.node A10K2.u7441 (nat_lit 122307988) (nat_lit 9300682144) (nat_lit 0) A10K2.u7448 from rfl, totK_node, atot7441, atot7448]
  decide +kernel

theorem arows7465 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7465 = true := by
  rw [show A10K2.u7465 = KTree.node A10K2.u7457 (nat_lit 122395862) (nat_lit 15097797148) (nat_lit 0) A10K2.u7464 from rfl, allE_node, arows7457, irow7465, arows7464]
  all_goals rfl

theorem atot7465 : totK PA10K2 A10K2.u7465 = [0, 1659408637769, 10834805873016, 26127113164511, 27545157166640, 12039663317841, 1814625241864, 75062079822, 0, 0] := by
  rw [show A10K2.u7465 = KTree.node A10K2.u7457 (nat_lit 122395862) (nat_lit 15097797148) (nat_lit 0) A10K2.u7464 from rfl, totK_node, atot7457, atot7464]
  decide +kernel

theorem arows7480 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7480 = true := by
  rw [show A10K2.u7480 = KTree.node A10K2.u7472 (nat_lit 122530928) (nat_lit 11487139187) (nat_lit 0) A10K2.u7479 from rfl, allE_node, arows7472, irow7480, arows7479]
  all_goals rfl

theorem atot7480 : totK PA10K2 A10K2.u7480 = [0, 0, 2520370877285, 14037275561678, 28045105976899, 23309880473890, 7626528063640, 955555283053, 36704093874, 0] := by
  rw [show A10K2.u7480 = KTree.node A10K2.u7472 (nat_lit 122530928) (nat_lit 11487139187) (nat_lit 0) A10K2.u7479 from rfl, totK_node, atot7472, atot7479]
  decide +kernel

theorem arows7497 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7497 = true := by
  rw [show A10K2.u7497 = KTree.node A10K2.u7489 (nat_lit 122607902) (nat_lit 7373259823) (nat_lit 0) A10K2.u7496 from rfl, allE_node, arows7489, irow7497, arows7496]
  all_goals rfl

theorem atot7497 : totK PA10K2 A10K2.u7497 = [0, 0, 2909866056204, 16137439503307, 30856035637081, 22538147270812, 5133453744719, 361487700539, 6239673734, 0] := by
  rw [show A10K2.u7497 = KTree.node A10K2.u7489 (nat_lit 122607902) (nat_lit 7373259823) (nat_lit 0) A10K2.u7496 from rfl, totK_node, atot7489, atot7496]
  decide +kernel

theorem arows7512 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7512 = true := by
  rw [show A10K2.u7512 = KTree.node A10K2.u7504 (nat_lit 122781078) (nat_lit 16090923929) (nat_lit 0) A10K2.u7511 from rfl, allE_node, arows7504, irow7512, arows7511]
  all_goals rfl

theorem atot7512 : totK PA10K2 A10K2.u7512 = [0, 2749136384700, 14177315504860, 27106536906599, 23372173728530, 8796693088789, 1436519951331, 86341982022, 0, 0] := by
  rw [show A10K2.u7512 = KTree.node A10K2.u7504 (nat_lit 122781078) (nat_lit 16090923929) (nat_lit 0) A10K2.u7511 from rfl, totK_node, atot7504, atot7511]
  decide +kernel

theorem arows7528 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7528 = true := by
  rw [show A10K2.u7528 = KTree.node A10K2.u7520 (nat_lit 122856596) (nat_lit 12401416741) (nat_lit 0) A10K2.u7527 from rfl, allE_node, arows7520, irow7528, arows7527]
  all_goals rfl

theorem atot7528 : totK PA10K2 A10K2.u7528 = [0, 1587972465714, 11594763344153, 27664732476146, 25671370306217, 8709136023680, 1086464147742, 37807056478, 0, 0] := by
  rw [show A10K2.u7528 = KTree.node A10K2.u7520 (nat_lit 122856596) (nat_lit 12401416741) (nat_lit 0) A10K2.u7527 from rfl, totK_node, atot7520, atot7527]
  decide +kernel

theorem arows7543 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7543 = true := by
  rw [show A10K2.u7543 = KTree.node A10K2.u7535 (nat_lit 123091178) (nat_lit 12403245268) (nat_lit 0) A10K2.u7542 from rfl, allE_node, arows7535, irow7543, arows7542]
  all_goals rfl

theorem atot7543 : totK PA10K2 A10K2.u7543 = [0, 0, 3031020189798, 16830485806356, 31283379748077, 20636166549495, 4064791910525, 212489180984, 0, 0] := by
  rw [show A10K2.u7543 = KTree.node A10K2.u7535 (nat_lit 123091178) (nat_lit 12403245268) (nat_lit 0) A10K2.u7542 from rfl, totK_node, atot7535, atot7542]
  decide +kernel

theorem arows7561 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7561 = true := by
  rw [show A10K2.u7561 = KTree.node A10K2.u7553 (nat_lit 123245070) (nat_lit 12877705286) (nat_lit 0) A10K2.u7560 from rfl, allE_node, arows7553, irow7561, arows7560]
  all_goals rfl

theorem atot7561 : totK PA10K2 A10K2.u7561 = [0, 3466343333767, 16894770236630, 29582268618145, 21877494933983, 6502809183649, 1057439173050, 150047772073, 6354482628, 0] := by
  rw [show A10K2.u7561 = KTree.node A10K2.u7553 (nat_lit 123245070) (nat_lit 12877705286) (nat_lit 0) A10K2.u7560 from rfl, totK_node, atot7553, atot7560]
  decide +kernel

theorem arows7576 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7576 = true := by
  rw [show A10K2.u7576 = KTree.node A10K2.u7568 (nat_lit 123331938) (nat_lit 13022466572) (nat_lit 0) A10K2.u7575 from rfl, allE_node, arows7568, irow7576, arows7575]
  all_goals rfl

theorem atot7576 : totK PA10K2 A10K2.u7576 = [0, 2666568321771, 14516393994965, 28541164746088, 24127440677704, 8283447608079, 1022853437193, 37204059898, 0, 0] := by
  rw [show A10K2.u7576 = KTree.node A10K2.u7568 (nat_lit 123331938) (nat_lit 13022466572) (nat_lit 0) A10K2.u7575 from rfl, totK_node, atot7568, atot7575]
  decide +kernel

theorem arows7592 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7592 = true := by
  rw [show A10K2.u7592 = KTree.node A10K2.u7584 (nat_lit 123464868) (nat_lit 7641841242) (nat_lit 0) A10K2.u7591 from rfl, allE_node, arows7584, irow7592, arows7591]
  all_goals rfl

theorem atot7592 : totK PA10K2 A10K2.u7592 = [0, 0, 4946617711373, 21999869116217, 32546832980320, 17793443922868, 2951151216810, 107549202733, 0, 0] := by
  rw [show A10K2.u7592 = KTree.node A10K2.u7584 (nat_lit 123464868) (nat_lit 7641841242) (nat_lit 0) A10K2.u7591 from rfl, totK_node, atot7584, atot7591]
  decide +kernel

theorem arows7607 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7607 = true := by
  rw [show A10K2.u7607 = KTree.node A10K2.u7599 (nat_lit 123553982) (nat_lit 11381047664) (nat_lit 0) A10K2.u7606 from rfl, allE_node, arows7599, irow7607, arows7606]
  all_goals rfl

theorem atot7607 : totK PA10K2 A10K2.u7607 = [0, 0, 2183007671712, 13340064710264, 28756019638270, 25461616883461, 8235386064786, 804087074879, 14159155365, 0] := by
  rw [show A10K2.u7607 = KTree.node A10K2.u7599 (nat_lit 123553982) (nat_lit 11381047664) (nat_lit 0) A10K2.u7606 from rfl, totK_node, atot7599, atot7606]
  decide +kernel

theorem arows7624 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7624 = true := by
  rw [show A10K2.u7624 = KTree.node A10K2.u7616 (nat_lit 123694514) (nat_lit 14500382976) (nat_lit 0) A10K2.u7623 from rfl, allE_node, arows7616, irow7624, arows7623]
  all_goals rfl

theorem atot7624 : totK PA10K2 A10K2.u7624 = [0, 0, 2345709048318, 13699366840572, 28986413669681, 25832141453443, 8329110662530, 752122227678, 12758098799, 0] := by
  rw [show A10K2.u7624 = KTree.node A10K2.u7616 (nat_lit 123694514) (nat_lit 14500382976) (nat_lit 0) A10K2.u7623 from rfl, totK_node, atot7616, atot7623]
  decide +kernel

theorem arows7639 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7639 = true := by
  rw [show A10K2.u7639 = KTree.node A10K2.u7631 (nat_lit 124346952) (nat_lit 13168029242) (nat_lit 0) A10K2.u7638 from rfl, allE_node, arows7631, irow7639, arows7638]
  all_goals rfl

theorem atot7639 : totK PA10K2 A10K2.u7639 = [0, 0, 2344175488518, 12624249677895, 25914453992458, 24324767938673, 10320297787011, 1755159340109, 92101273538, 0] := by
  rw [show A10K2.u7639 = KTree.node A10K2.u7631 (nat_lit 124346952) (nat_lit 13168029242) (nat_lit 0) A10K2.u7638 from rfl, totK_node, atot7631, atot7638]
  decide +kernel

theorem arows7655 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7655 = true := by
  rw [show A10K2.u7655 = KTree.node A10K2.u7647 (nat_lit 124422501) (nat_lit 7336690236) (nat_lit 0) A10K2.u7654 from rfl, allE_node, arows7647, irow7655, arows7654]
  all_goals rfl

theorem atot7655 : totK PA10K2 A10K2.u7655 = [0, 0, 3117720635311, 16319418267648, 29805683098601, 22139865765463, 5936069662373, 536701779479, 12475655917, 0] := by
  rw [show A10K2.u7655 = KTree.node A10K2.u7647 (nat_lit 124422501) (nat_lit 7336690236) (nat_lit 0) A10K2.u7654 from rfl, totK_node, atot7647, atot7654]
  decide +kernel

theorem arows7670 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7670 = true := by
  rw [show A10K2.u7670 = KTree.node A10K2.u7662 (nat_lit 124501061) (nat_lit 1004950078) (nat_lit 0) A10K2.u7669 from rfl, allE_node, arows7662, irow7670, arows7669]
  all_goals rfl

theorem atot7670 : totK PA10K2 A10K2.u7670 = [0, 0, 846194190982, 8169951313424, 24785191077733, 29662144064549, 13575354436768, 2029879635865, 79946069331, 0] := by
  rw [show A10K2.u7670 = KTree.node A10K2.u7662 (nat_lit 124501061) (nat_lit 1004950078) (nat_lit 0) A10K2.u7669 from rfl, totK_node, atot7662, atot7669]
  decide +kernel

theorem arows7690 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7690 = true := by
  rw [show A10K2.u7690 = KTree.node A10K2.u7682 (nat_lit 124642814) (nat_lit 15856477616) (nat_lit 0) A10K2.u7689 from rfl, allE_node, arows7682, irow7690, arows7689]
  all_goals rfl

theorem atot7690 : totK PA10K2 A10K2.u7690 = [0, 0, 0, 3586708273377, 17996723379212, 30501785991160, 19896277849196, 4964839842697, 461552366527, 8047840951] := by
  rw [show A10K2.u7690 = KTree.node A10K2.u7682 (nat_lit 124642814) (nat_lit 15856477616) (nat_lit 0) A10K2.u7689 from rfl, totK_node, atot7682, atot7689]
  decide +kernel

theorem arows7705 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7705 = true := by
  rw [show A10K2.u7705 = KTree.node A10K2.u7697 (nat_lit 124862734) (nat_lit 4554836921) (nat_lit 0) A10K2.u7704 from rfl, allE_node, arows7697, irow7705, arows7704]
  all_goals rfl

theorem atot7705 : totK PA10K2 A10K2.u7705 = [0, 0, 3516284413366, 16489259656576, 28105477247334, 21371706500269, 7801615075580, 1213082625470, 55162827605, 0] := by
  rw [show A10K2.u7705 = KTree.node A10K2.u7697 (nat_lit 124862734) (nat_lit 4554836921) (nat_lit 0) A10K2.u7704 from rfl, totK_node, atot7697, atot7704]
  decide +kernel

theorem arows7721 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7721 = true := by
  rw [show A10K2.u7721 = KTree.node A10K2.u7713 (nat_lit 124963095) (nat_lit 7448943542) (nat_lit 0) A10K2.u7720 from rfl, allE_node, arows7713, irow7721, arows7720]
  all_goals rfl

theorem atot7721 : totK PA10K2 A10K2.u7721 = [0, 0, 2423524895016, 14991699330814, 30595844851294, 23591551367666, 5807948416971, 443262101160, 6354482628, 0] := by
  rw [show A10K2.u7721 = KTree.node A10K2.u7713 (nat_lit 124963095) (nat_lit 7448943542) (nat_lit 0) A10K2.u7720 from rfl, totK_node, atot7713, atot7720]
  decide +kernel

theorem arows7736 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7736 = true := by
  rw [show A10K2.u7736 = KTree.node A10K2.u7728 (nat_lit 125395351) (nat_lit 14568056812) (nat_lit 0) A10K2.u7735 from rfl, allE_node, arows7728, irow7736, arows7735]
  all_goals rfl

theorem atot7736 : totK PA10K2 A10K2.u7736 = [0, 0, 2183007671712, 12777753214877, 27817873695320, 26037736145868, 9159765446696, 975731940285, 20813618929, 0] := by
  rw [show A10K2.u7736 = KTree.node A10K2.u7728 (nat_lit 125395351) (nat_lit 14568056812) (nat_lit 0) A10K2.u7735 from rfl, totK_node, atot7728, atot7735]
  decide +kernel

theorem arows7753 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7753 = true := by
  rw [show A10K2.u7753 = KTree.node A10K2.u7745 (nat_lit 125529714) (nat_lit 11419339156) (nat_lit 0) A10K2.u7752 from rfl, allE_node, arows7745, irow7753, arows7752]
  all_goals rfl

theorem atot7753 : totK PA10K2 A10K2.u7753 = [0, 0, 2347203525858, 13707684992804, 28914300881574, 25576211371548, 8586784895891, 804144765419, 13679205470, 0] := by
  rw [show A10K2.u7753 = KTree.node A10K2.u7745 (nat_lit 125529714) (nat_lit 11419339156) (nat_lit 0) A10K2.u7752 from rfl, totK_node, atot7745, atot7752]
  decide +kernel

theorem arows7768 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7768 = true := by
  rw [show A10K2.u7768 = KTree.node A10K2.u7760 (nat_lit 130049182) (nat_lit 14941068844) (nat_lit 0) A10K2.u7767 from rfl, allE_node, arows7760, irow7768, arows7767]
  all_goals rfl

theorem atot7768 : totK PA10K2 A10K2.u7768 = [0, 2231826234337, 12105345806399, 24034629153760, 21871500846279, 11253187381335, 4701030118269, 1003910249441, 61110126106, 0] := by
  rw [show A10K2.u7768 = KTree.node A10K2.u7760 (nat_lit 130049182) (nat_lit 14941068844) (nat_lit 0) A10K2.u7767 from rfl, totK_node, atot7760, atot7767]
  decide +kernel

theorem arows7784 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7784 = true := by
  rw [show A10K2.u7784 = KTree.node A10K2.u7776 (nat_lit 130205866) (nat_lit 12716874340) (nat_lit 0) A10K2.u7783 from rfl, allE_node, arows7776, irow7784, arows7783]
  all_goals rfl

theorem atot7784 : totK PA10K2 A10K2.u7784 = [0, 3571414429873, 18128419072745, 31638993363667, 20969701907784, 4353588720409, 220803170364, 0, 0, 0] := by
  rw [show A10K2.u7784 = KTree.node A10K2.u7776 (nat_lit 130205866) (nat_lit 12716874340) (nat_lit 0) A10K2.u7783 from rfl, totK_node, atot7776, atot7783]
  decide +kernel

theorem arows7799 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7799 = true := by
  rw [show A10K2.u7799 = KTree.node A10K2.u7791 (nat_lit 130282738) (nat_lit 15007491767) (nat_lit 0) A10K2.u7798 from rfl, allE_node, arows7791, irow7799, arows7798]
  all_goals rfl

theorem atot7799 : totK PA10K2 A10K2.u7799 = [0, 0, 4808798417218, 21691530447218, 32215241615119, 16905264153412, 2696455575632, 111598773623, 0, 0] := by
  rw [show A10K2.u7799 = KTree.node A10K2.u7791 (nat_lit 130282738) (nat_lit 15007491767) (nat_lit 0) A10K2.u7798 from rfl, totK_node, atot7791, atot7798]
  decide +kernel

theorem arows7817 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7817 = true := by
  rw [show A10K2.u7817 = KTree.node A10K2.u7809 (nat_lit 130419460) (nat_lit 13170546932) (nat_lit 0) A10K2.u7816 from rfl, allE_node, arows7809, irow7817, arows7816]
  all_goals rfl

theorem atot7817 : totK PA10K2 A10K2.u7817 = [0, 0, 2111179415660, 13262701418654, 28908206049848, 24806124729207, 7355646982830, 715844502502, 13364899180, 0] := by
  rw [show A10K2.u7817 = KTree.node A10K2.u7809 (nat_lit 130419460) (nat_lit 13170546932) (nat_lit 0) A10K2.u7816 from rfl, totK_node, atot7809, atot7816]
  decide +kernel

theorem arows7832 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7832 = true := by
  rw [show A10K2.u7832 = KTree.node A10K2.u7824 (nat_lit 130625179) (nat_lit 9934298573) (nat_lit 0) A10K2.u7831 from rfl, allE_node, arows7824, irow7832, arows7831]
  all_goals rfl

theorem atot7832 : totK PA10K2 A10K2.u7832 = [0, 2238164317933, 12516858869187, 26055761397878, 25027110250554, 11087567637347, 1896807889690, 87977137236, 0, 0] := by
  rw [show A10K2.u7832 = KTree.node A10K2.u7824 (nat_lit 130625179) (nat_lit 9934298573) (nat_lit 0) A10K2.u7831 from rfl, totK_node, atot7824, atot7831]
  decide +kernel

theorem arows7848 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7848 = true := by
  rw [show A10K2.u7848 = KTree.node A10K2.u7840 (nat_lit 130693795) (nat_lit 10475069369) (nat_lit 0) A10K2.u7847 from rfl, allE_node, arows7840, irow7848, arows7847]
  all_goals rfl

theorem atot7848 : totK PA10K2 A10K2.u7848 = [0, 2522866575780, 13877319658524, 28098867171828, 24366808338863, 8261652115300, 1011466468461, 37204059898, 0, 0] := by
  rw [show A10K2.u7848 = KTree.node A10K2.u7840 (nat_lit 130693795) (nat_lit 10475069369) (nat_lit 0) A10K2.u7847 from rfl, totK_node, atot7840, atot7847]
  decide +kernel

theorem arows7863 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7863 = true := by
  rw [show A10K2.u7863 = KTree.node A10K2.u7855 (nat_lit 130787262) (nat_lit 16049402067) (nat_lit 0) A10K2.u7862 from rfl, allE_node, arows7855, irow7863, arows7862]
  all_goals rfl

theorem atot7863 : totK PA10K2 A10K2.u7863 = [0, 1054693577800, 8826358501851, 24658767900779, 28830327711643, 13745644864928, 2227812081306, 100796613114, 0, 0] := by
  rw [show A10K2.u7863 = KTree.node A10K2.u7855 (nat_lit 130787262) (nat_lit 16049402067) (nat_lit 0) A10K2.u7862 from rfl, totK_node, atot7855, atot7862]
  decide +kernel

theorem arows7880 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7880 = true := by
  rw [show A10K2.u7880 = KTree.node A10K2.u7872 (nat_lit 130922644) (nat_lit 12586770762) (nat_lit 0) A10K2.u7879 from rfl, allE_node, arows7872, irow7880, arows7879]
  all_goals rfl

theorem atot7880 : totK PA10K2 A10K2.u7880 = [0, 0, 2710286701750, 15106164048215, 29434198923998, 23111371922419, 6847305561437, 691715103406, 13576218110, 0] := by
  rw [show A10K2.u7880 = KTree.node A10K2.u7872 (nat_lit 130922644) (nat_lit 12586770762) (nat_lit 0) A10K2.u7879 from rfl, totK_node, atot7872, atot7879]
  decide +kernel

theorem arows7895 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7895 = true := by
  rw [show A10K2.u7895 = KTree.node A10K2.u7887 (nat_lit 131031536) (nat_lit 14075027958) (nat_lit 0) A10K2.u7894 from rfl, allE_node, arows7887, irow7895, arows7894]
  all_goals rfl

theorem atot7895 : totK PA10K2 A10K2.u7895 = [0, 1540001081091, 8856425041085, 21264222286357, 26928786309005, 16461249475086, 3272154588745, 145944880625, 0, 0] := by
  rw [show A10K2.u7895 = KTree.node A10K2.u7887 (nat_lit 131031536) (nat_lit 14075027958) (nat_lit 0) A10K2.u7894 from rfl, totK_node, atot7887, atot7894]
  decide +kernel

theorem arows7911 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7911 = true := by
  rw [show A10K2.u7911 = KTree.node A10K2.u7903 (nat_lit 131655062) (nat_lit 15784983380) (nat_lit 0) A10K2.u7910 from rfl, allE_node, arows7903, irow7911, arows7910]
  all_goals rfl

theorem atot7911 : totK PA10K2 A10K2.u7911 = [0, 2629320995746, 14573498580653, 28943232185907, 24077093153932, 7690313632352, 832176968215, 18459763130, 0, 0] := by
  rw [show A10K2.u7911 = KTree.node A10K2.u7903 (nat_lit 131655062) (nat_lit 15784983380) (nat_lit 0) A10K2.u7910 from rfl, totK_node, atot7903, atot7910]
  decide +kernel

theorem arows7926 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7926 = true := by
  rw [show A10K2.u7926 = KTree.node A10K2.u7918 (nat_lit 131796423) (nat_lit 14470067458) (nat_lit 0) A10K2.u7925 from rfl, allE_node, arows7918, irow7926, arows7925]
  all_goals rfl

theorem atot7926 : totK PA10K2 A10K2.u7926 = [0, 2424236405812, 13755052441128, 28329741312493, 24887924563160, 8454704896362, 910383698872, 18713227901, 0, 0] := by
  rw [show A10K2.u7926 = KTree.node A10K2.u7918 (nat_lit 131796423) (nat_lit 14470067458) (nat_lit 0) A10K2.u7925 from rfl, totK_node, atot7918, atot7925]
  decide +kernel

theorem arows7945 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7945 = true := by
  rw [show A10K2.u7945 = KTree.node A10K2.u7937 (nat_lit 131857444) (nat_lit 5954288988) (nat_lit 0) A10K2.u7944 from rfl, allE_node, arows7937, irow7945, arows7944]
  all_goals rfl

theorem atot7945 : totK PA10K2 A10K2.u7945 = [0, 0, 4472133875706, 20937900852602, 32314616741004, 17932817683449, 2932397253872, 106761385489, 0, 0] := by
  rw [show A10K2.u7945 = KTree.node A10K2.u7937 (nat_lit 131857444) (nat_lit 5954288988) (nat_lit 0) A10K2.u7944 from rfl, totK_node, atot7937, atot7944]
  decide +kernel

theorem arows7960 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7960 = true := by
  rw [show A10K2.u7960 = KTree.node A10K2.u7952 (nat_lit 131939006) (nat_lit 11300335331) (nat_lit 0) A10K2.u7959 from rfl, allE_node, arows7952, irow7960, arows7959]
  all_goals rfl

theorem atot7960 : totK PA10K2 A10K2.u7960 = [0, 0, 2086353853694, 12846406559822, 28416482125973, 25949081755409, 8357336211750, 777319434175, 14159155365, 0] := by
  rw [show A10K2.u7960 = KTree.node A10K2.u7952 (nat_lit 131939006) (nat_lit 11300335331) (nat_lit 0) A10K2.u7959 from rfl, totK_node, atot7952, atot7959]
  decide +kernel

theorem arows7976 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7976 = true := by
  rw [show A10K2.u7976 = KTree.node A10K2.u7968 (nat_lit 132080566) (nat_lit 16784593185) (nat_lit 0) A10K2.u7975 from rfl, allE_node, arows7968, irow7976, arows7975]
  all_goals rfl

theorem atot7976 : totK PA10K2 A10K2.u7976 = [0, 0, 2421251661110, 13974991350808, 28975966111501, 25098629995783, 7949741281209, 730013584181, 12758098799, 0] := by
  rw [show A10K2.u7976 = KTree.node A10K2.u7968 (nat_lit 132080566) (nat_lit 16784593185) (nat_lit 0) A10K2.u7975 from rfl, totK_node, atot7968, atot7975]
  decide +kernel

theorem arows7991 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u7991 = true := by
  rw [show A10K2.u7991 = KTree.node A10K2.u7983 (nat_lit 132143204) (nat_lit 13547978332) (nat_lit 0) A10K2.u7990 from rfl, allE_node, arows7983, irow7991, arows7990]
  all_goals rfl

theorem atot7991 : totK PA10K2 A10K2.u7991 = [0, 0, 2231809808435, 12496095123730, 26271605746088, 24739405745768, 10176737818768, 1620136956746, 74383286109, 0] := by
  rw [show A10K2.u7991 = KTree.node A10K2.u7983 (nat_lit 132143204) (nat_lit 13547978332) (nat_lit 0) A10K2.u7990 from rfl, totK_node, atot7983, atot7990]
  decide +kernel

theorem arows8008 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8008 = true := by
  rw [show A10K2.u8008 = KTree.node A10K2.u8000 (nat_lit 132303658) (nat_lit 11754173865) (nat_lit 0) A10K2.u8007 from rfl, allE_node, arows8000, irow8008, arows8007]
  all_goals rfl

theorem atot8008 : totK PA10K2 A10K2.u8008 = [0, 0, 3568549953759, 18108069847063, 31593807431672, 21012221013657, 4390306854256, 208042081030, 0, 0] := by
  rw [show A10K2.u8008 = KTree.node A10K2.u8000 (nat_lit 132303658) (nat_lit 11754173865) (nat_lit 0) A10K2.u8007 from rfl, totK_node, atot8000, atot8007]
  decide +kernel

theorem arows8023 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8023 = true := by
  rw [show A10K2.u8023 = KTree.node A10K2.u8015 (nat_lit 132381907) (nat_lit 10248088735) (nat_lit 0) A10K2.u8022 from rfl, allE_node, arows8015, irow8023, arows8022]
  all_goals rfl

theorem atot8023 : totK PA10K2 A10K2.u8023 = [0, 0, 0, 4528126505690, 21305960042262, 32621192727731, 17518883037833, 2675467635611, 94999656960, 0] := by
  rw [show A10K2.u8023 = KTree.node A10K2.u8015 (nat_lit 132381907) (nat_lit 10248088735) (nat_lit 0) A10K2.u8022 from rfl, totK_node, atot8015, atot8022]
  decide +kernel

theorem arows8039 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8039 = true := by
  rw [show A10K2.u8039 = KTree.node A10K2.u8031 (nat_lit 132579398) (nat_lit 14842210566) (nat_lit 0) A10K2.u8038 from rfl, allE_node, arows8031, irow8039, arows8038]
  all_goals rfl

theorem atot8039 : totK PA10K2 A10K2.u8039 = [0, 0, 0, 3567397638872, 18190086743844, 31012759940444, 20565127704406, 4866692942616, 374700617644, 7237400819] := by
  rw [show A10K2.u8039 = KTree.node A10K2.u8031 (nat_lit 132579398) (nat_lit 14842210566) (nat_lit 0) A10K2.u8038 from rfl, totK_node, atot8031, atot8038]
  decide +kernel

theorem arows8054 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8054 = true := by
  rw [show A10K2.u8054 = KTree.node A10K2.u8046 (nat_lit 132742753) (nat_lit 2633353323) (nat_lit 0) A10K2.u8053 from rfl, allE_node, arows8046, irow8054, arows8053]
  all_goals rfl

theorem atot8054 : totK PA10K2 A10K2.u8054 = [0, 0, 3000864694247, 15395784683732, 28692606964473, 23029891537809, 7427327541126, 855466992801, 45264740730, 0] := by
  rw [show A10K2.u8054 = KTree.node A10K2.u8046 (nat_lit 132742753) (nat_lit 2633353323) (nat_lit 0) A10K2.u8053 from rfl, totK_node, atot8046, atot8053]
  decide +kernel

theorem arows8072 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8072 = true := by
  rw [show A10K2.u8072 = KTree.node A10K2.u8064 (nat_lit 132853318) (nat_lit 15125727397) (nat_lit 0) A10K2.u8071 from rfl, allE_node, arows8064, irow8072, arows8071]
  all_goals rfl

theorem atot8072 : totK PA10K2 A10K2.u8072 = [0, 0, 2811976945744, 15768040674140, 30553295722838, 23341547367419, 6320769167129, 478850284402, 6632180018, 0] := by
  rw [show A10K2.u8072 = KTree.node A10K2.u8064 (nat_lit 132853318) (nat_lit 15125727397) (nat_lit 0) A10K2.u8071 from rfl, totK_node, atot8064, atot8071]
  decide +kernel

theorem arows8087 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8087 = true := by
  rw [show A10K2.u8087 = KTree.node A10K2.u8079 (nat_lit 132988370) (nat_lit 15196470988) (nat_lit 0) A10K2.u8086 from rfl, allE_node, arows8079, irow8087, arows8086]
  all_goals rfl

theorem atot8087 : totK PA10K2 A10K2.u8087 = [0, 0, 0, 3326214093884, 17502925804028, 31226440408204, 21291602835852, 4981830234724, 377461610259, 7380853412] := by
  rw [show A10K2.u8087 = KTree.node A10K2.u8079 (nat_lit 132988370) (nat_lit 15196470988) (nat_lit 0) A10K2.u8086 from rfl, totK_node, atot8079, atot8086]
  decide +kernel

theorem arows8103 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8103 = true := by
  rw [show A10K2.u8103 = KTree.node A10K2.u8095 (nat_lit 133119052) (nat_lit 3050612540) (nat_lit 0) A10K2.u8102 from rfl, allE_node, arows8095, irow8103, arows8102]
  all_goals rfl

theorem atot8103 : totK PA10K2 A10K2.u8103 = [0, 0, 1361469227636, 9565178190193, 24177430076522, 27110326131357, 13974491395626, 2525444694053, 125753341383, 0] := by
  rw [show A10K2.u8103 = KTree.node A10K2.u8095 (nat_lit 133119052) (nat_lit 3050612540) (nat_lit 0) A10K2.u8102 from rfl, totK_node, atot8095, atot8102]
  decide +kernel

theorem arows8118 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8118 = true := by
  rw [show A10K2.u8118 = KTree.node A10K2.u8110 (nat_lit 133752532) (nat_lit 9233804072) (nat_lit 0) A10K2.u8117 from rfl, allE_node, arows8110, irow8118, arows8117]
  all_goals rfl

theorem atot8118 : totK PA10K2 A10K2.u8118 = [0, 0, 2807834751928, 15304239247647, 29761449380285, 23894042610721, 6960915683830, 579226182202, 12477124820, 0] := by
  rw [show A10K2.u8118 = KTree.node A10K2.u8110 (nat_lit 133752532) (nat_lit 9233804072) (nat_lit 0) A10K2.u8117 from rfl, totK_node, atot8110, atot8117]
  decide +kernel

theorem arows8135 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8135 = true := by
  rw [show A10K2.u8135 = KTree.node A10K2.u8127 (nat_lit 133894997) (nat_lit 2337632431) (nat_lit 0) A10K2.u8134 from rfl, allE_node, arows8127, irow8135, arows8134]
  all_goals rfl

theorem atot8135 : totK PA10K2 A10K2.u8135 = [0, 0, 2424236405812, 13945965455496, 28865471649211, 24833155353185, 7762286292951, 666803954968, 12696458652, 0] := by
  rw [show A10K2.u8135 = KTree.node A10K2.u8127 (nat_lit 133894997) (nat_lit 2337632431) (nat_lit 0) A10K2.u8134 from rfl, totK_node, atot8127, atot8134]
  decide +kernel

theorem arows8150 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8150 = true := by
  rw [show A10K2.u8150 = KTree.node A10K2.u8142 (nat_lit 133956102) (nat_lit 14872606531) (nat_lit 0) A10K2.u8149 from rfl, allE_node, arows8142, irow8150, arows8149]
  all_goals rfl

theorem atot8150 : totK PA10K2 A10K2.u8150 = [0, 0, 0, 3934464342005, 19530947899428, 32224415960122, 19408313094783, 3460423763396, 162387666597, 0] := by
  rw [show A10K2.u8150 = KTree.node A10K2.u8142 (nat_lit 133956102) (nat_lit 14872606531) (nat_lit 0) A10K2.u8149 from rfl, totK_node, atot8142, atot8149]
  decide +kernel

theorem arows8166 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8166 = true := by
  rw [show A10K2.u8166 = KTree.node A10K2.u8158 (nat_lit 134047405) (nat_lit 5470134846) (nat_lit 0) A10K2.u8165 from rfl, allE_node, arows8158, irow8166, arows8165]
  all_goals rfl

theorem atot8166 : totK PA10K2 A10K2.u8166 = [0, 0, 0, 2792728059991, 14891935230305, 28865978199335, 24249703715015, 7364108752195, 697851709826, 13585869933] := by
  rw [show A10K2.u8166 = KTree.node A10K2.u8158 (nat_lit 134047405) (nat_lit 5470134846) (nat_lit 0) A10K2.u8165 from rfl, totK_node, atot8158, atot8165]
  decide +kernel

theorem arows8181 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u8181 = true := by
  rw [show A10K2.u8181 = KTree.node A10K2.u8173 (nat_lit 134185349) (nat_lit 5307843420) (nat_lit 0) A10K2.u8180 from rfl, allE_node, arows8173, irow8181, arows8180]
  all_goals rfl

theorem atot8181 : totK PA10K2 A10K2.u8181 = [0, 0, 0, 1696468033473, 11304587076993, 26420149852473, 26348219006900, 10698446317467, 1639786801748, 73776485728] := by
  rw [show A10K2.u8181 = KTree.node A10K2.u8173 (nat_lit 134185349) (nat_lit 5307843420) (nat_lit 0) A10K2.u8180 from rfl, totK_node, atot8173, atot8180]
  decide +kernel

theorem arows30 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u30 = true := by
  rw [show A10K2.u30 = KTree.node A10K2.u14 (nat_lit 131169) (nat_lit 10022573639) (nat_lit 0) A10K2.u29 from rfl, allE_node, arows14, irow30, arows29]
  all_goals rfl

theorem atot30 : totK PA10K2 A10K2.u30 = [5672690316105, 29908850159032, 56941488378537, 45446472392981, 13788279106278, 1473482126377, 42551283831, 0, 0, 0] := by
  rw [show A10K2.u30 = KTree.node A10K2.u14 (nat_lit 131169) (nat_lit 10022573639) (nat_lit 0) A10K2.u29 from rfl, totK_node, atot14, atot29]
  decide +kernel

theorem arows61 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u61 = true := by
  rw [show A10K2.u61 = KTree.node A10K2.u45 (nat_lit 279891) (nat_lit 9107365771) (nat_lit 0) A10K2.u60 from rfl, allE_node, arows45, irow61, arows60]
  all_goals rfl

theorem atot61 : totK PA10K2 A10K2.u61 = [836280282984, 10646889716551, 38218422669938, 57442037959299, 37389087278576, 9718563736241, 1030797893588, 36134558889, 0, 0] := by
  rw [show A10K2.u61 = KTree.node A10K2.u45 (nat_lit 279891) (nat_lit 9107365771) (nat_lit 0) A10K2.u60 from rfl, totK_node, atot45, atot60]
  decide +kernel

theorem arows93 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u93 = true := by
  rw [show A10K2.u93 = KTree.node A10K2.u77 (nat_lit 1051299) (nat_lit 9424555606) (nat_lit 0) A10K2.u92 from rfl, allE_node, arows77, irow93, arows92]
  all_goals rfl

theorem atot93 : totK PA10K2 A10K2.u93 = [2855966361573, 17829804000657, 44700555779547, 53502273974108, 28843585795039, 5974322557482, 405103107173, 5676195732, 0, 0] := by
  rw [show A10K2.u93 = KTree.node A10K2.u77 (nat_lit 1051299) (nat_lit 9424555606) (nat_lit 0) A10K2.u92 from rfl, totK_node, atot77, atot92]
  decide +kernel

theorem arows124 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u124 = true := by
  rw [show A10K2.u124 = KTree.node A10K2.u108 (nat_lit 1214819) (nat_lit 9011522790) (nat_lit 0) A10K2.u123 from rfl, allE_node, arows108, irow124, arows123]
  all_goals rfl

theorem atot124 : totK PA10K2 A10K2.u124 = [2810590781981, 20281566956274, 50650707298608, 53026886753167, 21855419748004, 3119421447889, 119037313879, 0, 0, 0] := by
  rw [show A10K2.u124 = KTree.node A10K2.u108 (nat_lit 1214819) (nat_lit 9011522790) (nat_lit 0) A10K2.u123 from rfl, totK_node, atot108, atot123]
  decide +kernel

theorem arows157 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u157 = true := by
  rw [show A10K2.u157 = KTree.node A10K2.u141 (nat_lit 1577395) (nat_lit 6680228345) (nat_lit 0) A10K2.u156 from rfl, allE_node, arows141, irow157, arows156]
  all_goals rfl

theorem atot157 : totK PA10K2 A10K2.u157 = [3480984518520, 19665334246686, 45078201093383, 51511814151299, 27450673744590, 5858730789106, 488592175926, 6354482628, 0, 0] := by
  rw [show A10K2.u157 = KTree.node A10K2.u141 (nat_lit 1577395) (nat_lit 6680228345) (nat_lit 0) A10K2.u156 from rfl, totK_node, atot141, atot156]
  decide +kernel

theorem arows188 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u188 = true := by
  rw [show A10K2.u188 = KTree.node A10K2.u172 (nat_lit 1806407) (nat_lit 10991789459) (nat_lit 0) A10K2.u187 from rfl, allE_node, arows172, irow188, arows187]
  all_goals rfl

theorem atot188 : totK PA10K2 A10K2.u188 = [2404892320697, 18064590619222, 48485400229305, 56799892447362, 27855059490524, 4821892147127, 230577559511, 0, 0, 0] := by
  rw [show A10K2.u188 = KTree.node A10K2.u172 (nat_lit 1806407) (nat_lit 10991789459) (nat_lit 0) A10K2.u187 from rfl, totK_node, atot172, atot187]
  decide +kernel

theorem arows220 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u220 = true := by
  rw [show A10K2.u220 = KTree.node A10K2.u204 (nat_lit 2041299) (nat_lit 10649282280) (nat_lit 0) A10K2.u219 from rfl, allE_node, arows204, irow220, arows219]
  all_goals rfl

theorem atot220 : totK PA10K2 A10K2.u220 = [0, 4542064106646, 25952961181127, 55124034286659, 51507210873218, 19488154852812, 2522974591959, 87935641093, 0, 0] := by
  rw [show A10K2.u220 = KTree.node A10K2.u204 (nat_lit 2041299) (nat_lit 10649282280) (nat_lit 0) A10K2.u219 from rfl, totK_node, atot204, atot219]
  decide +kernel

theorem arows251 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u251 = true := by
  rw [show A10K2.u251 = KTree.node A10K2.u235 (nat_lit 2235221) (nat_lit 6420257657) (nat_lit 0) A10K2.u250 from rfl, allE_node, arows235, irow251, arows250]
  all_goals rfl

theorem atot251 : totK PA10K2 A10K2.u251 = [0, 5629276289032, 30432212564836, 58263621084796, 45186009940017, 12682392890460, 1288633488522, 42173223013, 0, 0] := by
  rw [show A10K2.u251 = KTree.node A10K2.u235 (nat_lit 2235221) (nat_lit 6420257657) (nat_lit 0) A10K2.u250 from rfl, totK_node, atot235, atot250]
  decide +kernel

theorem arows285 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u285 = true := by
  rw [show A10K2.u285 = KTree.node A10K2.u269 (nat_lit 2391487) (nat_lit 14319036847) (nat_lit 0) A10K2.u284 from rfl, allE_node, arows269, irow285, arows284]
  all_goals rfl

theorem atot285 : totK PA10K2 A10K2.u285 = [0, 0, 7021815410454, 35235209864523, 60154277452555, 39224341903796, 9856284951658, 1033437889875, 36134558889, 0] := by
  rw [show A10K2.u285 = KTree.node A10K2.u269 (nat_lit 2391487) (nat_lit 14319036847) (nat_lit 0) A10K2.u284 from rfl, totK_node, atot269, atot284]
  decide +kernel

theorem arows316 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u316 = true := by
  rw [show A10K2.u316 = KTree.node A10K2.u300 (nat_lit 3174513) (nat_lit 8334353339) (nat_lit 0) A10K2.u315 from rfl, allE_node, arows300, irow316, arows315]
  all_goals rfl

theorem atot316 : totK PA10K2 A10K2.u316 = [0, 3666287800522, 22189177314736, 50133593970765, 50737329834156, 22461215527606, 4204167235218, 326168807313, 5676195732, 0] := by
  rw [show A10K2.u316 = KTree.node A10K2.u300 (nat_lit 3174513) (nat_lit 8334353339) (nat_lit 0) A10K2.u315 from rfl, totK_node, atot300, atot315]
  decide +kernel

theorem arows348 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u348 = true := by
  rw [show A10K2.u348 = KTree.node A10K2.u332 (nat_lit 3415072) (nat_lit 14158318195) (nat_lit 0) A10K2.u347 from rfl, allE_node, arows332, irow348, arows347]
  all_goals rfl

theorem atot348 : totK PA10K2 A10K2.u348 = [0, 1996035672226, 17461939815247, 49536296358793, 56141626629206, 22747917535539, 2978784482394, 99198744494, 0, 0] := by
  rw [show A10K2.u348 = KTree.node A10K2.u332 (nat_lit 3415072) (nat_lit 14158318195) (nat_lit 0) A10K2.u347 from rfl, totK_node, atot332, atot347]
  decide +kernel

theorem arows379 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u379 = true := by
  rw [show A10K2.u379 = KTree.node A10K2.u363 (nat_lit 3719780) (nat_lit 12711645601) (nat_lit 0) A10K2.u378 from rfl, allE_node, arows363, irow379, arows378]
  all_goals rfl

theorem atot379 : totK PA10K2 A10K2.u379 = [0, 5006686729215, 26826826934403, 53186854518139, 47862570980555, 20048982780804, 3840889068272, 299394327555, 5976421810, 0] := by
  rw [show A10K2.u379 = KTree.node A10K2.u363 (nat_lit 3719780) (nat_lit 12711645601) (nat_lit 0) A10K2.u378 from rfl, totK_node, atot363, atot378]
  decide +kernel

theorem arows412 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u412 = true := by
  rw [show A10K2.u412 = KTree.node A10K2.u396 (nat_lit 8407045) (nat_lit 6820374666) (nat_lit 0) A10K2.u411 from rfl, allE_node, arows396, irow412, arows411]
  all_goals rfl

theorem atot412 : totK PA10K2 A10K2.u412 = [3597961741760, 19875568401108, 42537939257560, 46513867997876, 30359759639187, 11558426742742, 1744976498592, 74781409772, 0, 0] := by
  rw [show A10K2.u412 = KTree.node A10K2.u396 (nat_lit 8407045) (nat_lit 6820374666) (nat_lit 0) A10K2.u411 from rfl, totK_node, atot396, atot411]
  decide +kernel

theorem arows443 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u443 = true := by
  rw [show A10K2.u443 = KTree.node A10K2.u427 (nat_lit 8622356) (nat_lit 11245132143) (nat_lit 0) A10K2.u442 from rfl, allE_node, arows427, irow443, arows442]
  all_goals rfl

theorem atot443 : totK PA10K2 A10K2.u443 = [2415627655432, 17241496168540, 45568851282961, 54202529855246, 28726617451826, 6815686321088, 747306877754, 30605747850, 0, 0] := by
  rw [show A10K2.u443 = KTree.node A10K2.u427 (nat_lit 8622356) (nat_lit 11245132143) (nat_lit 0) A10K2.u442 from rfl, totK_node, atot427, atot442]
  decide +kernel

theorem arows475 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u475 = true := by
  rw [show A10K2.u475 = KTree.node A10K2.u459 (nat_lit 8849954) (nat_lit 6509729944) (nat_lit 0) A10K2.u474 from rfl, allE_node, arows459, irow475, arows474]
  all_goals rfl

theorem atot475 : totK PA10K2 A10K2.u475 = [2185661584285, 14730860440801, 40082116054378, 54000376395462, 34384652438919, 8349548839079, 675636484639, 11205006771, 0, 0] := by
  rw [show A10K2.u475 = KTree.node A10K2.u459 (nat_lit 8849954) (nat_lit 6509729944) (nat_lit 0) A10K2.u474 from rfl, totK_node, atot459, atot474]
  decide +kernel

theorem arows506 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u506 = true := by
  rw [show A10K2.u506 = KTree.node A10K2.u490 (nat_lit 9097222) (nat_lit 12376667425) (nat_lit 0) A10K2.u505 from rfl, allE_node, arows490, irow506, arows505]
  all_goals rfl

theorem atot506 : totK PA10K2 A10K2.u506 = [2148948818715, 15907101315096, 42821743227691, 52729877744195, 30639318224632, 8312541585763, 962570446077, 36704093874, 0, 0] := by
  rw [show A10K2.u506 = KTree.node A10K2.u490 (nat_lit 9097222) (nat_lit 12376667425) (nat_lit 0) A10K2.u505 from rfl, totK_node, atot490, atot505]
  decide +kernel

theorem arows541 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u541 = true := by
  rw [show A10K2.u541 = KTree.node A10K2.u525 (nat_lit 9454874) (nat_lit 14369213512) (nat_lit 0) A10K2.u540 from rfl, allE_node, arows525, irow541, arows540]
  all_goals rfl

theorem atot541 : totK PA10K2 A10K2.u541 = [3749445373936, 21110910485399, 46636814794284, 50201842602863, 25918940233514, 5245179977980, 376121607184, 6239673734, 0, 0] := by
  rw [show A10K2.u541 = KTree.node A10K2.u525 (nat_lit 9454874) (nat_lit 14369213512) (nat_lit 0) A10K2.u540 from rfl, totK_node, atot525, atot540]
  decide +kernel

theorem arows572 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u572 = true := by
  rw [show A10K2.u572 = KTree.node A10K2.u556 (nat_lit 9603171) (nat_lit 5086525400) (nat_lit 0) A10K2.u571 from rfl, allE_node, arows556, irow572, arows571]
  all_goals rfl

theorem atot572 : totK PA10K2 A10K2.u572 = [2453432600795, 19072096214798, 50216507199801, 54615342063211, 22912238623942, 3259063469252, 119037313879, 0, 0, 0] := by
  rw [show A10K2.u572 = KTree.node A10K2.u556 (nat_lit 9603171) (nat_lit 5086525400) (nat_lit 0) A10K2.u571 from rfl, totK_node, atot556, atot571]
  decide +kernel

theorem arows604 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u604 = true := by
  rw [show A10K2.u604 = KTree.node A10K2.u588 (nat_lit 9885728) (nat_lit 13629912264) (nat_lit 0) A10K2.u603 from rfl, allE_node, arows588, irow604, arows603]
  all_goals rfl

theorem atot604 : totK PA10K2 A10K2.u604 = [0, 5453631124300, 29944789467007, 57860431302820, 44769807446174, 12867094441065, 1398418248241, 42551283831, 0, 0] := by
  rw [show A10K2.u604 = KTree.node A10K2.u588 (nat_lit 9885728) (nat_lit 13629912264) (nat_lit 0) A10K2.u603 from rfl, totK_node, atot588, atot603]
  decide +kernel

theorem arows635 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u635 = true := by
  rw [show A10K2.u635 = KTree.node A10K2.u619 (nat_lit 10707521) (nat_lit 10272296125) (nat_lit 0) A10K2.u634 from rfl, allE_node, arows619, irow635, arows634]
  all_goals rfl

theorem atot635 : totK PA10K2 A10K2.u635 = [0, 5599791173516, 30995856034177, 59783178516754, 45828137331801, 12382075328133, 1047674039140, 13259410892, 0, 0] := by
  rw [show A10K2.u635 = KTree.node A10K2.u619 (nat_lit 10707521) (nat_lit 10272296125) (nat_lit 0) A10K2.u634 from rfl, totK_node, atot619, atot634]
  decide +kernel

theorem arows668 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u668 = true := by
  rw [show A10K2.u668 = KTree.node A10K2.u652 (nat_lit 11185855) (nat_lit 11082648029) (nat_lit 0) A10K2.u667 from rfl, allE_node, arows652, irow668, arows667]
  all_goals rfl

theorem atot668 : totK PA10K2 A10K2.u668 = [0, 4234784814534, 25246283429139, 54548331569196, 49663249675465, 16950028825404, 2091400030342, 79325725869, 0, 0] := by
  rw [show A10K2.u668 = KTree.node A10K2.u652 (nat_lit 11185855) (nat_lit 11082648029) (nat_lit 0) A10K2.u667 from rfl, totK_node, atot652, atot667]
  decide +kernel

theorem arows699 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u699 = true := by
  rw [show A10K2.u699 = KTree.node A10K2.u683 (nat_lit 11675326) (nat_lit 14171407639) (nat_lit 0) A10K2.u698 from rfl, allE_node, arows683, irow699, arows698]
  all_goals rfl

theorem atot699 : totK PA10K2 A10K2.u699 = [0, 4102109319186, 24924136006435, 54622132172098, 49728262063911, 16353258011789, 1912780919900, 73512229340, 0, 0] := by
  rw [show A10K2.u699 = KTree.node A10K2.u683 (nat_lit 11675326) (nat_lit 14171407639) (nat_lit 0) A10K2.u698 from rfl, totK_node, atot683, atot698]
  decide +kernel

theorem arows731 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u731 = true := by
  rw [show A10K2.u731 = KTree.node A10K2.u715 (nat_lit 11962581) (nat_lit 6356134920) (nat_lit 0) A10K2.u730 from rfl, allE_node, arows715, irow731, arows730]
  all_goals rfl

theorem atot731 : totK PA10K2 A10K2.u731 = [2300403117589, 11557928869029, 25396427336537, 38616980341259, 43410736395118, 24348143228909, 5604716992081, 489767369008, 6354482628, 0] := by
  rw [show A10K2.u731 = KTree.node A10K2.u715 (nat_lit 11962581) (nat_lit 6356134920) (nat_lit 0) A10K2.u730 from rfl, totK_node, atot715, atot730]
  decide +kernel

theorem arows762 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u762 = true := by
  rw [show A10K2.u762 = KTree.node A10K2.u746 (nat_lit 12787093) (nat_lit 1499060418) (nat_lit 0) A10K2.u761 from rfl, allE_node, arows746, irow762, arows761]
  all_goals rfl

theorem atot762 : totK PA10K2 A10K2.u762 = [3756893483078, 23535245034625, 53470621116959, 52279172078772, 20626053848968, 2874549252442, 107033630238, 0, 0, 0] := by
  rw [show A10K2.u762 = KTree.node A10K2.u746 (nat_lit 12787093) (nat_lit 1499060418) (nat_lit 0) A10K2.u761 from rfl, totK_node, atot746, atot761]
  decide +kernel

theorem arows796 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u796 = true := by
  rw [show A10K2.u796 = KTree.node A10K2.u780 (nat_lit 12993811) (nat_lit 10751371044) (nat_lit 0) A10K2.u795 from rfl, allE_node, arows780, irow796, arows795]
  all_goals rfl

theorem atot796 : totK PA10K2 A10K2.u796 = [847358390021, 8621775651444, 32854084474694, 56769111092704, 42678241903493, 12151794047732, 1292297341151, 41810754621, 0, 0] := by
  rw [show A10K2.u796 = KTree.node A10K2.u780 (nat_lit 12993811) (nat_lit 10751371044) (nat_lit 0) A10K2.u795 from rfl, totK_node, atot780, atot795]
  decide +kernel

theorem arows827 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u827 = true := by
  rw [show A10K2.u827 = KTree.node A10K2.u811 (nat_lit 13315485) (nat_lit 4338422861) (nat_lit 0) A10K2.u826 from rfl, allE_node, arows811, irow827, arows826]
  all_goals rfl

theorem atot827 : totK PA10K2 A10K2.u827 = [3610370075287, 22680800630145, 52446590541633, 53431414308545, 22743701826242, 3341446317410, 138000673012, 0, 0, 0] := by
  rw [show A10K2.u827 = KTree.node A10K2.u811 (nat_lit 13315485) (nat_lit 4338422861) (nat_lit 0) A10K2.u826 from rfl, totK_node, atot811, atot826]
  decide +kernel

theorem arows859 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u859 = true := by
  rw [show A10K2.u859 = KTree.node A10K2.u843 (nat_lit 13580586) (nat_lit 12288443943) (nat_lit 0) A10K2.u858 from rfl, allE_node, arows843, irow859, arows858]
  all_goals rfl

theorem atot859 : totK PA10K2 A10K2.u859 = [2127308439256, 14805692127945, 40728125050394, 54240399490900, 34697583123779, 9602534267633, 1044476414315, 36704093874, 0, 0] := by
  rw [show A10K2.u859 = KTree.node A10K2.u843 (nat_lit 13580586) (nat_lit 12288443943) (nat_lit 0) A10K2.u858 from rfl, totK_node, atot843, atot858]
  decide +kernel

theorem arows890 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u890 = true := by
  rw [show A10K2.u890 = KTree.node A10K2.u874 (nat_lit 14356479) (nat_lit 13966711711) (nat_lit 0) A10K2.u889 from rfl, allE_node, arows874, irow890, arows889]
  all_goals rfl

theorem atot890 : totK PA10K2 A10K2.u890 = [4265131281216, 25007671826274, 54214969938109, 51776952943855, 20318763547497, 2648489445317, 74380861019, 0, 0, 0] := by
  rw [show A10K2.u890 = KTree.node A10K2.u874 (nat_lit 14356479) (nat_lit 13966711711) (nat_lit 0) A10K2.u889 from rfl, totK_node, atot874, atot889]
  decide +kernel

theorem arows923 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u923 = true := by
  rw [show A10K2.u923 = KTree.node A10K2.u907 (nat_lit 14499229) (nat_lit 4405278915) (nat_lit 0) A10K2.u922 from rfl, allE_node, arows907, irow923, arows922]
  all_goals rfl

theorem atot923 : totK PA10K2 A10K2.u923 = [0, 6385454730817, 32945630898967, 60143518505296, 45100791165043, 12463847109295, 1067271695541, 14159155365, 0, 0] := by
  rw [show A10K2.u923 = KTree.node A10K2.u907 (nat_lit 14499229) (nat_lit 4405278915) (nat_lit 0) A10K2.u922 from rfl, totK_node, atot907, atot922]
  decide +kernel

theorem arows954 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u954 = true := by
  rw [show A10K2.u954 = KTree.node A10K2.u938 (nat_lit 14706075) (nat_lit 9253344182) (nat_lit 0) A10K2.u953 from rfl, allE_node, arows938, irow954, arows953]
  all_goals rfl

theorem atot954 : totK PA10K2 A10K2.u954 = [0, 3835258981970, 24092454002853, 54135889318438, 51384512428272, 19531585711951, 2675290776345, 109973286931, 0, 0] := by
  rw [show A10K2.u954 = KTree.node A10K2.u938 (nat_lit 14706075) (nat_lit 9253344182) (nat_lit 0) A10K2.u953 from rfl, totK_node, atot938, atot953]
  decide +kernel

theorem arows986 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u986 = true := by
  rw [show A10K2.u986 = KTree.node A10K2.u970 (nat_lit 14934628) (nat_lit 10516678794) (nat_lit 0) A10K2.u985 from rfl, allE_node, arows970, irow986, arows985]
  all_goals rfl

theorem atot986 : totK PA10K2 A10K2.u986 = [0, 2222037618697, 15632124539159, 43456903551871, 56088034596252, 31620122996426, 6718993233265, 517352930264, 7237400819, 0] := by
  rw [show A10K2.u986 = KTree.node A10K2.u970 (nat_lit 14934628) (nat_lit 10516678794) (nat_lit 0) A10K2.u985 from rfl, totK_node, atot970, atot985]
  decide +kernel

theorem arows1017 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1017 = true := by
  rw [show A10K2.u1017 = KTree.node A10K2.u1001 (nat_lit 15284381) (nat_lit 6237309011) (nat_lit 0) A10K2.u1016 from rfl, allE_node, arows1001, irow1017, arows1016]
  all_goals rfl

theorem atot1017 : totK PA10K2 A10K2.u1017 = [0, 3590781414735, 21925828216333, 50776910499367, 53461963574373, 23611604432897, 3640066750193, 159496267024, 0, 0] := by
  rw [show A10K2.u1017 = KTree.node A10K2.u1001 (nat_lit 15284381) (nat_lit 6237309011) (nat_lit 0) A10K2.u1016 from rfl, totK_node, atot1001, atot1016]
  decide +kernel

theorem arows1053 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1053 = true := by
  rw [show A10K2.u1053 = KTree.node A10K2.u1037 (nat_lit 15547897) (nat_lit 5306361419) (nat_lit 0) A10K2.u1052 from rfl, allE_node, arows1037, irow1053, arows1052]
  all_goals rfl

theorem atot1053 : totK PA10K2 A10K2.u1053 = [0, 866947050573, 11348021656531, 41052992568208, 60067704525798, 36366367626882, 7842500409681, 565026693971, 7380853412, 0] := by
  rw [show A10K2.u1053 = KTree.node A10K2.u1037 (nat_lit 15547897) (nat_lit 5306361419) (nat_lit 0) A10K2.u1052 from rfl, totK_node, atot1037, atot1052]
  decide +kernel

theorem arows1084 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1084 = true := by
  rw [show A10K2.u1084 = KTree.node A10K2.u1068 (nat_lit 16327848) (nat_lit 6057157141) (nat_lit 0) A10K2.u1083 from rfl, allE_node, arows1068, irow1084, arows1083]
  all_goals rfl

theorem atot1084 : totK PA10K2 A10K2.u1084 = [0, 5348058925484, 28283044510146, 55435812213025, 48283628220140, 17980576497886, 2423568809108, 87555743113, 0, 0] := by
  rw [show A10K2.u1084 = KTree.node A10K2.u1068 (nat_lit 16327848) (nat_lit 6057157141) (nat_lit 0) A10K2.u1083 from rfl, totK_node, atot1068, atot1083]
  decide +kernel

theorem arows1116 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1116 = true := by
  rw [show A10K2.u1116 = KTree.node A10K2.u1100 (nat_lit 16519948) (nat_lit 11448936075) (nat_lit 0) A10K2.u1115 from rfl, allE_node, arows1100, irow1116, arows1115]
  all_goals rfl

theorem atot1116 : totK PA10K2 A10K2.u1116 = [0, 1029302401414, 12083540192429, 41693706289831, 59614006934605, 35559110105764, 7434360688684, 480836955278, 6725424603, 0] := by
  rw [show A10K2.u1116 = KTree.node A10K2.u1100 (nat_lit 16519948) (nat_lit 11448936075) (nat_lit 0) A10K2.u1115 from rfl, totK_node, atot1100, atot1115]
  decide +kernel

theorem arows1147 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1147 = true := by
  rw [show A10K2.u1147 = KTree.node A10K2.u1131 (nat_lit 16749055) (nat_lit 10271769328) (nat_lit 0) A10K2.u1146 from rfl, allE_node, arows1131, irow1147, arows1146]
  all_goals rfl

theorem atot1147 : totK PA10K2 A10K2.u1147 = [0, 2380035396479, 13873896489961, 34463306165565, 48821022848629, 40223176500716, 14864551213993, 2019189222893, 80636931058, 0] := by
  rw [show A10K2.u1147 = KTree.node A10K2.u1131 (nat_lit 16749055) (nat_lit 10271769328) (nat_lit 0) A10K2.u1146 from rfl, totK_node, atot1131, atot1146]
  decide +kernel

theorem arows1180 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1180 = true := by
  rw [show A10K2.u1180 = KTree.node A10K2.u1164 (nat_lit 16957452) (nat_lit 11556653982) (nat_lit 0) A10K2.u1179 from rfl, allE_node, arows1164, irow1180, arows1179]
  all_goals rfl

theorem atot1180 : totK PA10K2 A10K2.u1180 = [0, 4128935202610, 25094962193474, 55084986227575, 50854147462636, 17457001651139, 1884123862546, 49456212095, 0, 0] := by
  rw [show A10K2.u1180 = KTree.node A10K2.u1164 (nat_lit 16957452) (nat_lit 11556653982) (nat_lit 0) A10K2.u1179 from rfl, totK_node, atot1164, atot1179]
  decide +kernel

theorem arows1211 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1211 = true := by
  rw [show A10K2.u1211 = KTree.node A10K2.u1195 (nat_lit 17095429) (nat_lit 7006709322) (nat_lit 0) A10K2.u1210 from rfl, allE_node, arows1195, irow1211, arows1210]
  all_goals rfl

theorem atot1211 : totK PA10K2 A10K2.u1211 = [0, 0, 5540256483068, 30470752734384, 58385531081464, 44152014902101, 12216588656997, 1302453414247, 41810754621, 0] := by
  rw [show A10K2.u1211 = KTree.node A10K2.u1195 (nat_lit 17095429) (nat_lit 7006709322) (nat_lit 0) A10K2.u1210 from rfl, totK_node, atot1195, atot1210]
  decide +kernel

theorem arows1243 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1243 = true := by
  rw [show A10K2.u1243 = KTree.node A10K2.u1227 (nat_lit 17875265) (nat_lit 10167068818) (nat_lit 0) A10K2.u1242 from rfl, allE_node, arows1227, irow1243, arows1242]
  all_goals rfl

theorem atot1243 : totK PA10K2 A10K2.u1243 = [0, 4844590114467, 26807280971180, 54359206511727, 48020942891228, 17748541291009, 2443164428797, 90588727226, 0, 0] := by
  rw [show A10K2.u1243 = KTree.node A10K2.u1227 (nat_lit 17875265) (nat_lit 10167068818) (nat_lit 0) A10K2.u1242 from rfl, totK_node, atot1227, atot1242]
  decide +kernel

theorem arows1274 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1274 = true := by
  rw [show A10K2.u1274 = KTree.node A10K2.u1258 (nat_lit 18117221) (nat_lit 5833235144) (nat_lit 0) A10K2.u1273 from rfl, allE_node, arows1258, irow1274, arows1273]
  all_goals rfl

theorem atot1274 : totK PA10K2 A10K2.u1274 = [0, 821967029087, 11896265993825, 43542829980441, 60294343475392, 29604635288350, 4468739524113, 173023831209, 0, 0] := by
  rw [show A10K2.u1274 = KTree.node A10K2.u1258 (nat_lit 18117221) (nat_lit 5833235144) (nat_lit 0) A10K2.u1273 from rfl, totK_node, atot1258, atot1273]
  decide +kernel

theorem arows1308 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1308 = true := by
  rw [show A10K2.u1308 = KTree.node A10K2.u1292 (nat_lit 18425173) (nat_lit 6868443389) (nat_lit 0) A10K2.u1307 from rfl, allE_node, arows1292, irow1308, arows1307]
  all_goals rfl

theorem atot1308 : totK PA10K2 A10K2.u1308 = [0, 5885876839217, 30507839135357, 56967909564946, 45914736470574, 16090244592612, 2808522799712, 239626649189, 6354482628, 0] := by
  rw [show A10K2.u1308 = KTree.node A10K2.u1292 (nat_lit 18425173) (nat_lit 6868443389) (nat_lit 0) A10K2.u1307 from rfl, totK_node, atot1292, atot1307]
  decide +kernel

theorem arows1339 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1339 = true := by
  rw [show A10K2.u1339 = KTree.node A10K2.u1323 (nat_lit 18640850) (nat_lit 14555320633) (nat_lit 0) A10K2.u1338 from rfl, allE_node, arows1323, irow1339, arows1338]
  all_goals rfl

theorem atot1339 : totK PA10K2 A10K2.u1339 = [0, 0, 7852394669508, 37669404986329, 62529191725945, 40656187053044, 9208276926387, 636566430453, 7007974415, 0] := by
  rw [show A10K2.u1339 = KTree.node A10K2.u1323 (nat_lit 18640850) (nat_lit 14555320633) (nat_lit 0) A10K2.u1338 from rfl, totK_node, atot1323, atot1338]
  decide +kernel

theorem arows1371 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1371 = true := by
  rw [show A10K2.u1371 = KTree.node A10K2.u1355 (nat_lit 18896910) (nat_lit 11129240354) (nat_lit 0) A10K2.u1370 from rfl, allE_node, arows1355, irow1371, arows1370]
  all_goals rfl

theorem atot1371 : totK PA10K2 A10K2.u1371 = [0, 0, 5038477196659, 27974329949852, 56101245684025, 47653734398369, 16122774717900, 2045473012538, 78077773536, 0] := by
  rw [show A10K2.u1371 = KTree.node A10K2.u1355 (nat_lit 18896910) (nat_lit 11129240354) (nat_lit 0) A10K2.u1370 from rfl, totK_node, atot1355, atot1370]
  decide +kernel

theorem arows1402 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1402 = true := by
  rw [show A10K2.u1402 = KTree.node A10K2.u1386 (nat_lit 19110177) (nat_lit 9648009300) (nat_lit 0) A10K2.u1401 from rfl, allE_node, arows1386, irow1402, arows1401]
  all_goals rfl

theorem atot1402 : totK PA10K2 A10K2.u1402 = [0, 0, 2305947832964, 17630981321629, 47077257973381, 53769563027179, 26607889302937, 6240075598833, 724870176442, 30605747850] := by
  rw [show A10K2.u1402 = KTree.node A10K2.u1386 (nat_lit 19110177) (nat_lit 9648009300) (nat_lit 0) A10K2.u1401 from rfl, totK_node, atot1386, atot1401]
  decide +kernel

theorem arows1435 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1435 = true := by
  rw [show A10K2.u1435 = KTree.node A10K2.u1419 (nat_lit 19337668) (nat_lit 8788976422) (nat_lit 0) A10K2.u1434 from rfl, allE_node, arows1419, irow1435, arows1434]
  all_goals rfl

theorem atot1435 : totK PA10K2 A10K2.u1435 = [0, 0, 2181200105082, 15495581571539, 42249636181588, 53626213891685, 30766707094175, 7175142605260, 622267354356, 11205006771] := by
  rw [show A10K2.u1435 = KTree.node A10K2.u1419 (nat_lit 19337668) (nat_lit 8788976422) (nat_lit 0) A10K2.u1434 from rfl, totK_node, atot1419, atot1434]
  decide +kernel

theorem arows1466 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1466 = true := by
  rw [show A10K2.u1466 = KTree.node A10K2.u1450 (nat_lit 20072121) (nat_lit 508557916) (nat_lit 0) A10K2.u1465 from rfl, allE_node, arows1450, irow1466, arows1465]
  all_goals rfl

theorem atot1466 : totK PA10K2 A10K2.u1466 = [0, 0, 3468004263753, 23368184727837, 54683619027023, 50936351969671, 17022906774970, 1945629317193, 62048158393, 0] := by
  rw [show A10K2.u1466 = KTree.node A10K2.u1450 (nat_lit 20072121) (nat_lit 508557916) (nat_lit 0) A10K2.u1465 from rfl, totK_node, atot1450, atot1465]
  decide +kernel

theorem arows1498 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1498 = true := by
  rw [show A10K2.u1498 = KTree.node A10K2.u1482 (nat_lit 20452181) (nat_lit 5372329579) (nat_lit 0) A10K2.u1497 from rfl, allE_node, arows1482, irow1498, arows1497]
  all_goals rfl

theorem atot1498 : totK PA10K2 A10K2.u1498 = [0, 0, 3898342811760, 22024322539999, 49076446578449, 51320327390311, 23035753799334, 4239707351959, 335420816593, 5976421810] := by
  rw [show A10K2.u1498 = KTree.node A10K2.u1482 (nat_lit 20452181) (nat_lit 5372329579) (nat_lit 0) A10K2.u1497 from rfl, totK_node, atot1482, atot1497]
  decide +kernel

theorem arows1529 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1529 = true := by
  rw [show A10K2.u1529 = KTree.node A10K2.u1513 (nat_lit 25170323) (nat_lit 3488780586) (nat_lit 0) A10K2.u1528 from rfl, allE_node, arows1513, irow1529, arows1528]
  all_goals rfl

theorem atot1529 : totK PA10K2 A10K2.u1529 = [0, 3079826674364, 18483423767884, 43840061621195, 51442459519174, 30751984385268, 8990631934254, 1112366556904, 42512946920, 0] := by
  rw [show A10K2.u1529 = KTree.node A10K2.u1513 (nat_lit 25170323) (nat_lit 3488780586) (nat_lit 0) A10K2.u1528 from rfl, totK_node, atot1513, atot1528]
  decide +kernel

theorem arows1564 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1564 = true := by
  rw [show A10K2.u1564 = KTree.node A10K2.u1548 (nat_lit 25395120) (nat_lit 13943431833) (nat_lit 0) A10K2.u1563 from rfl, allE_node, arows1548, irow1564, arows1563]
  all_goals rfl

theorem atot1564 : totK PA10K2 A10K2.u1564 = [0, 2933762722828, 19738009479721, 48933708446341, 53756310509075, 25171084300051, 4731834663901, 405168515639, 20060612110, 0] := by
  rw [show A10K2.u1564 = KTree.node A10K2.u1548 (nat_lit 25395120) (nat_lit 13943431833) (nat_lit 0) A10K2.u1563 from rfl, totK_node, atot1548, atot1563]
  decide +kernel

theorem arows1595 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1595 = true := by
  rw [show A10K2.u1595 = KTree.node A10K2.u1579 (nat_lit 25613463) (nat_lit 10446066699) (nat_lit 0) A10K2.u1594 from rfl, allE_node, arows1579, irow1595, arows1594]
  all_goals rfl

theorem atot1595 : totK PA10K2 A10K2.u1595 = [0, 2185661584285, 14729477557391, 39745313269923, 53139934193371, 34131035103478, 9151730189387, 930527102924, 21750142511, 0] := by
  rw [show A10K2.u1595 = KTree.node A10K2.u1579 (nat_lit 25613463) (nat_lit 10446066699) (nat_lit 0) A10K2.u1594 from rfl, totK_node, atot1579, atot1594]
  decide +kernel

theorem arows1627 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1627 = true := by
  rw [show A10K2.u1627 = KTree.node A10K2.u1611 (nat_lit 25871138) (nat_lit 11045330773) (nat_lit 0) A10K2.u1626 from rfl, allE_node, arows1611, irow1627, arows1626]
  all_goals rfl

theorem atot1627 : totK PA10K2 A10K2.u1627 = [0, 2148948818715, 17776121164443, 49335730191664, 56423007402410, 24205502693833, 3352449026222, 125758949210, 0, 0] := by
  rw [show A10K2.u1627 = KTree.node A10K2.u1611 (nat_lit 25871138) (nat_lit 11045330773) (nat_lit 0) A10K2.u1626 from rfl, totK_node, atot1611, atot1626]
  decide +kernel

theorem arows1658 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1658 = true := by
  rw [show A10K2.u1658 = KTree.node A10K2.u1642 (nat_lit 26252044) (nat_lit 11448936075) (nat_lit 0) A10K2.u1657 from rfl, allE_node, arows1642, irow1658, arows1657]
  all_goals rfl

theorem atot1658 : totK PA10K2 A10K2.u1658 = [0, 3906546503663, 21768279326184, 47670576418111, 50138441521103, 24260404773329, 4679393434561, 363101918902, 6239673734, 0] := by
  rw [show A10K2.u1658 = KTree.node A10K2.u1642 (nat_lit 26252044) (nat_lit 11448936075) (nat_lit 0) A10K2.u1657 from rfl, totK_node, atot1642, atot1657]
  decide +kernel

theorem arows1691 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1691 = true := by
  rw [show A10K2.u1691 = KTree.node A10K2.u1675 (nat_lit 26479667) (nat_lit 3610309379) (nat_lit 0) A10K2.u1690 from rfl, allE_node, arows1675, irow1691, arows1690]
  all_goals rfl

theorem atot1691 : totK PA10K2 A10K2.u1691 = [0, 2296331471068, 18243015430957, 49263462567001, 55316761002737, 23591167216436, 3276388357524, 124383793444, 0, 0] := by
  rw [show A10K2.u1691 = KTree.node A10K2.u1675 (nat_lit 26479667) (nat_lit 3610309379) (nat_lit 0) A10K2.u1690 from rfl, totK_node, atot1675, atot1690]
  decide +kernel

theorem arows1722 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1722 = true := by
  rw [show A10K2.u1722 = KTree.node A10K2.u1706 (nat_lit 27287994) (nat_lit 12632304876) (nat_lit 0) A10K2.u1721 from rfl, allE_node, arows1706, irow1722, arows1721]
  all_goals rfl

theorem atot1722 : totK PA10K2 A10K2.u1722 = [0, 0, 5535966909526, 30433134184080, 58083773684632, 43958141634884, 12460054067883, 1392395311641, 42551283831, 0] := by
  rw [show A10K2.u1722 = KTree.node A10K2.u1706 (nat_lit 27287994) (nat_lit 12632304876) (nat_lit 0) A10K2.u1721 from rfl, totK_node, atot1706, atot1721]
  decide +kernel

theorem arows1754 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1754 = true := by
  rw [show A10K2.u1754 = KTree.node A10K2.u1738 (nat_lit 27863197) (nat_lit 6247957938) (nat_lit 0) A10K2.u1753 from rfl, allE_node, arows1738, irow1754, arows1753]
  all_goals rfl

theorem atot1754 : totK PA10K2 A10K2.u1754 = [0, 0, 5933056510107, 32276135919446, 60999238463864, 44622365742108, 10861361962418, 850721049636, 13259410892, 0] := by
  rw [show A10K2.u1754 = KTree.node A10K2.u1738 (nat_lit 27863197) (nat_lit 6247957938) (nat_lit 0) A10K2.u1753 from rfl, totK_node, atot1738, atot1753]
  decide +kernel

theorem arows1785 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1785 = true := by
  rw [show A10K2.u1785 = KTree.node A10K2.u1769 (nat_lit 28366125) (nat_lit 6613700219) (nat_lit 0) A10K2.u1784 from rfl, allE_node, arows1769, irow1785, arows1784]
  all_goals rfl

theorem atot1785 : totK PA10K2 A10K2.u1785 = [0, 0, 5339590082976, 29405788191643, 57558957450260, 45937227034990, 13097133352747, 1420205886612, 48242839260, 0] := by
  rw [show A10K2.u1785 = KTree.node A10K2.u1769 (nat_lit 28366125) (nat_lit 6613700219) (nat_lit 0) A10K2.u1784 from rfl, totK_node, atot1769, atot1784]
  decide +kernel

theorem arows1819 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1819 = true := by
  rw [show A10K2.u1819 = KTree.node A10K2.u1803 (nat_lit 28649150) (nat_lit 15268314887) (nat_lit 0) A10K2.u1818 from rfl, allE_node, arows1803, irow1819, arows1818]
  all_goals rfl

theorem atot1819 : totK PA10K2 A10K2.u1819 = [0, 157526836586, 1175037895913, 12949733238797, 44985552723423, 58381819494247, 27272598446729, 5143839527832, 355404831818, 6354482628] := by
  rw [show A10K2.u1819 = KTree.node A10K2.u1803 (nat_lit 28649150) (nat_lit 15268314887) (nat_lit 0) A10K2.u1818 from rfl, totK_node, atot1803, atot1818]
  decide +kernel

theorem arows1850 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1850 = true := by
  rw [show A10K2.u1850 = KTree.node A10K2.u1834 (nat_lit 29493522) (nat_lit 11482470953) (nat_lit 0) A10K2.u1849 from rfl, allE_node, arows1834, irow1850, arows1849]
  all_goals rfl

theorem atot1850 : totK PA10K2 A10K2.u1850 = [0, 5899769764081, 31334768668167, 58788445294863, 45228057720434, 13067955340387, 1349653086346, 42551283831, 0, 0] := by
  rw [show A10K2.u1850 = KTree.node A10K2.u1834 (nat_lit 29493522) (nat_lit 11482470953) (nat_lit 0) A10K2.u1849 from rfl, totK_node, atot1834, atot1849]
  decide +kernel

theorem arows1882 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1882 = true := by
  rw [show A10K2.u1882 = KTree.node A10K2.u1866 (nat_lit 29651340) (nat_lit 8339698573) (nat_lit 0) A10K2.u1881 from rfl, allE_node, arows1866, irow1882, arows1881]
  all_goals rfl

theorem atot1882 : totK PA10K2 A10K2.u1882 = [0, 0, 7436587050825, 36314256784086, 60911213217066, 39905812337898, 10043255698223, 1051187247274, 36134558889, 0] := by
  rw [show A10K2.u1882 = KTree.node A10K2.u1866 (nat_lit 29651340) (nat_lit 8339698573) (nat_lit 0) A10K2.u1881 from rfl, totK_node, atot1866, atot1881]
  decide +kernel

theorem arows1913 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1913 = true := by
  rw [show A10K2.u1913 = KTree.node A10K2.u1897 (nat_lit 29998290) (nat_lit 15577264525) (nat_lit 0) A10K2.u1912 from rfl, allE_node, arows1897, irow1913, arows1912]
  all_goals rfl

theorem atot1913 : totK PA10K2 A10K2.u1913 = [0, 4457728465308, 25548606045692, 54225704595420, 51096634248166, 20334545171296, 2864240876186, 113628732061, 0, 0] := by
  rw [show A10K2.u1913 = KTree.node A10K2.u1897 (nat_lit 29998290) (nat_lit 15577264525) (nat_lit 0) A10K2.u1912 from rfl, totK_node, atot1897, atot1912]
  decide +kernel

theorem arows1946 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1946 = true := by
  rw [show A10K2.u1946 = KTree.node A10K2.u1930 (nat_lit 30270688) (nat_lit 3400141359) (nat_lit 0) A10K2.u1945 from rfl, allE_node, arows1930, irow1946, arows1945]
  all_goals rfl

theorem atot1946 : totK PA10K2 A10K2.u1946 = [0, 2127308439256, 14684334942035, 41000555702669, 56040198051478, 35505070193381, 8288700843087, 613892824614, 8047840951, 0] := by
  rw [show A10K2.u1946 = KTree.node A10K2.u1930 (nat_lit 30270688) (nat_lit 3400141359) (nat_lit 0) A10K2.u1945 from rfl, totK_node, atot1930, atot1945]
  decide +kernel

theorem arows1977 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u1977 = true := by
  rw [show A10K2.u1977 = KTree.node A10K2.u1961 (nat_lit 31044876) (nat_lit 7059818561) (nat_lit 0) A10K2.u1976 from rfl, allE_node, arows1961, irow1977, arows1976]
  all_goals rfl

theorem atot1977 : totK PA10K2 A10K2.u1977 = [0, 4265131281216, 25633605825833, 55978686267142, 51844896932392, 18081977780977, 1999760820773, 51131642604, 0, 0] := by
  rw [show A10K2.u1977 = KTree.node A10K2.u1961 (nat_lit 31044876) (nat_lit 7059818561) (nat_lit 0) A10K2.u1976 from rfl, totK_node, atot1961, atot1976]
  decide +kernel

theorem arows2009 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2009 = true := by
  rw [show A10K2.u2009 = KTree.node A10K2.u1993 (nat_lit 31244845) (nat_lit 5560482018) (nat_lit 0) A10K2.u2008 from rfl, allE_node, arows1993, irow2009, arows2008]
  all_goals rfl

theorem atot2009 : totK PA10K2 A10K2.u2009 = [0, 0, 5993559354746, 32292306636706, 60861089930607, 46106589151867, 12340136350343, 988185091633, 14159155365, 0] := by
  rw [show A10K2.u2009 = KTree.node A10K2.u1993 (nat_lit 31244845) (nat_lit 5560482018) (nat_lit 0) A10K2.u2008 from rfl, totK_node, atot1993, atot2008]
  decide +kernel

theorem arows2040 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2040 = true := by
  rw [show A10K2.u2040 = KTree.node A10K2.u2024 (nat_lit 38350518) (nat_lit 16409148109) (nat_lit 0) A10K2.u2039 from rfl, allE_node, arows2024, irow2040, arows2039]
  all_goals rfl

theorem atot2040 : totK PA10K2 A10K2.u2040 = [2808829852973, 15442380140721, 32113161810334, 35873108899963, 32019803834008, 25209453313602, 10562940578990, 1632372015925, 73776485728, 0] := by
  rw [show A10K2.u2040 = KTree.node A10K2.u2024 (nat_lit 38350518) (nat_lit 16409148109) (nat_lit 0) A10K2.u2039 from rfl, totK_node, atot2024, atot2039]
  decide +kernel

theorem arows2077 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2077 = true := by
  rw [show A10K2.u2077 = KTree.node A10K2.u2061 (nat_lit 38495105) (nat_lit 10296676959) (nat_lit 0) A10K2.u2076 from rfl, allE_node, arows2061, irow2077, arows2076]
  all_goals rfl

theorem atot2077 : totK PA10K2 A10K2.u2077 = [3708965615848, 23007364192998, 52772554288842, 52347142579611, 20856681401895, 2939484637127, 113185311303, 0, 0, 0] := by
  rw [show A10K2.u2077 = KTree.node A10K2.u2061 (nat_lit 38495105) (nat_lit 10296676959) (nat_lit 0) A10K2.u2076 from rfl, totK_node, atot2061, atot2076]
  decide +kernel

theorem arows2108 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2108 = true := by
  rw [show A10K2.u2108 = KTree.node A10K2.u2092 (nat_lit 38685025) (nat_lit 8951841821) (nat_lit 0) A10K2.u2107 from rfl, allE_node, arows2092, irow2108, arows2107]
  all_goals rfl

theorem atot2108 : totK PA10K2 A10K2.u2108 = [560981842138, 7346034913425, 30712150674057, 56245469778354, 44693698343905, 13077780170509, 1358926349430, 42943767608, 0, 0] := by
  rw [show A10K2.u2108 = KTree.node A10K2.u2092 (nat_lit 38685025) (nat_lit 8951841821) (nat_lit 0) A10K2.u2107 from rfl, totK_node, atot2092, atot2107]
  decide +kernel

theorem arows2140 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2140 = true := by
  rw [show A10K2.u2140 = KTree.node A10K2.u2124 (nat_lit 38905530) (nat_lit 14950583633) (nat_lit 0) A10K2.u2139 from rfl, allE_node, arows2124, irow2140, arows2139]
  all_goals rfl

theorem atot2140 : totK PA10K2 A10K2.u2140 = [5109750391162, 28240496311125, 55777953796963, 46281059903508, 15372969866121, 1894509207336, 73400861101, 0, 0, 0] := by
  rw [show A10K2.u2140 = KTree.node A10K2.u2124 (nat_lit 38905530) (nat_lit 14950583633) (nat_lit 0) A10K2.u2139 from rfl, totK_node, atot2124, atot2139]
  decide +kernel

theorem arows2171 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2171 = true := by
  rw [show A10K2.u2171 = KTree.node A10K2.u2155 (nat_lit 39155643) (nat_lit 6759321169) (nat_lit 0) A10K2.u2170 from rfl, allE_node, arows2155, irow2171, arows2170]
  all_goals rfl

theorem atot2171 : totK PA10K2 A10K2.u2171 = [953763886815, 10804794664666, 39439914196675, 58705694903879, 34328871299588, 7119440353848, 534338023047, 6354482628, 0, 0] := by
  rw [show A10K2.u2171 = KTree.node A10K2.u2155 (nat_lit 39155643) (nat_lit 6759321169) (nat_lit 0) A10K2.u2170 from rfl, totK_node, atot2155, atot2170]
  decide +kernel

theorem arows2204 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2204 = true := by
  rw [show A10K2.u2204 = KTree.node A10K2.u2188 (nat_lit 39431850) (nat_lit 12668747883) (nat_lit 0) A10K2.u2203 from rfl, allE_node, arows2188, irow2204, arows2203]
  all_goals rfl

theorem atot2204 : totK PA10K2 A10K2.u2204 = [4935928765675, 28047934741098, 57174791852987, 49673867363255, 16967704844363, 2013611414952, 69348762479, 0, 0, 0] := by
  rw [show A10K2.u2204 = KTree.node A10K2.u2188 (nat_lit 39431850) (nat_lit 12668747883) (nat_lit 0) A10K2.u2203 from rfl, totK_node, atot2188, atot2203]
  decide +kernel

theorem arows2235 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2235 = true := by
  rw [show A10K2.u2235 = KTree.node A10K2.u2219 (nat_lit 39660946) (nat_lit 15259374986) (nat_lit 0) A10K2.u2234 from rfl, allE_node, arows2219, irow2235, arows2234]
  all_goals rfl

theorem atot2235 : totK PA10K2 A10K2.u2235 = [0, 6491119698070, 33658126089927, 60863013120579, 44856977833638, 12262642470120, 1053752916821, 14159155365, 0, 0] := by
  rw [show A10K2.u2235 = KTree.node A10K2.u2219 (nat_lit 39660946) (nat_lit 15259374986) (nat_lit 0) A10K2.u2234 from rfl, totK_node, atot2219, atot2234]
  decide +kernel

theorem arows2267 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2267 = true := by
  rw [show A10K2.u2267 = KTree.node A10K2.u2251 (nat_lit 40452435) (nat_lit 10086765349) (nat_lit 0) A10K2.u2266 from rfl, allE_node, arows2251, irow2267, arows2266]
  all_goals rfl

theorem atot2267 : totK PA10K2 A10K2.u2267 = [0, 4480843069614, 25640150897471, 53917211273716, 49767285903241, 19116547899832, 2646796369952, 110980545626, 0, 0] := by
  rw [show A10K2.u2267 = KTree.node A10K2.u2251 (nat_lit 40452435) (nat_lit 10086765349) (nat_lit 0) A10K2.u2266 from rfl, totK_node, atot2251, atot2266]
  decide +kernel

theorem arows2298 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2298 = true := by
  rw [show A10K2.u2298 = KTree.node A10K2.u2282 (nat_lit 40597430) (nat_lit 16762336813) (nat_lit 0) A10K2.u2297 from rfl, allE_node, arows2282, irow2298, arows2297]
  all_goals rfl

theorem atot2298 : totK PA10K2 A10K2.u2298 = [0, 2903302422428, 20548905954108, 51949505767310, 54901843959778, 22227556590745, 2953792069960, 99502968044, 0, 0] := by
  rw [show A10K2.u2298 = KTree.node A10K2.u2282 (nat_lit 40597430) (nat_lit 16762336813) (nat_lit 0) A10K2.u2297 from rfl, totK_node, atot2282, atot2297]
  decide +kernel

theorem arows2332 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2332 = true := by
  rw [show A10K2.u2332 = KTree.node A10K2.u2316 (nat_lit 40807638) (nat_lit 15099320726) (nat_lit 0) A10K2.u2331 from rfl, allE_node, arows2316, irow2332, arows2331]
  all_goals rfl

theorem atot2332 : totK PA10K2 A10K2.u2332 = [0, 1299799213788, 11173726379445, 35698880977947, 53730093503535, 38015961936137, 11055706405599, 1269991605252, 42686146280, 0] := by
  rw [show A10K2.u2332 = KTree.node A10K2.u2316 (nat_lit 40807638) (nat_lit 15099320726) (nat_lit 0) A10K2.u2331 from rfl, totK_node, atot2316, atot2331]
  decide +kernel

theorem arows2363 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2363 = true := by
  rw [show A10K2.u2363 = KTree.node A10K2.u2347 (nat_lit 41020890) (nat_lit 14363022406) (nat_lit 0) A10K2.u2362 from rfl, allE_node, arows2347, irow2363, arows2362]
  all_goals rfl

theorem atot2363 : totK PA10K2 A10K2.u2363 = [0, 4370933019512, 25701255404567, 54781093837331, 49125192603474, 16441905697491, 1877855237191, 54552033373, 0, 0] := by
  rw [show A10K2.u2363 = KTree.node A10K2.u2347 (nat_lit 41020890) (nat_lit 14363022406) (nat_lit 0) A10K2.u2362 from rfl, totK_node, atot2347, atot2362]
  decide +kernel

theorem arows2395 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2395 = true := by
  rw [show A10K2.u2395 = KTree.node A10K2.u2379 (nat_lit 41306660) (nat_lit 13676929761) (nat_lit 0) A10K2.u2394 from rfl, allE_node, arows2379, irow2395, arows2394]
  all_goals rfl

theorem atot2395 : totK PA10K2 A10K2.u2395 = [0, 1934017180087, 14615184658756, 42958594813196, 57465935994362, 30688475086981, 5750461912947, 397014851519, 6354482628, 0] := by
  rw [show A10K2.u2395 = KTree.node A10K2.u2379 (nat_lit 41306660) (nat_lit 13676929761) (nat_lit 0) A10K2.u2394 from rfl, totK_node, atot2379, atot2394]
  decide +kernel

theorem arows2426 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2426 = true := by
  rw [show A10K2.u2426 = KTree.node A10K2.u2410 (nat_lit 41622980) (nat_lit 7761998093) (nat_lit 0) A10K2.u2425 from rfl, allE_node, arows2410, irow2426, arows2425]
  all_goals rfl

theorem atot2426 : totK PA10K2 A10K2.u2426 = [796021182214, 6561072385721, 26035774182912, 52329742710900, 49436491888370, 19603491258000, 2758672592863, 111757921133, 0, 0] := by
  rw [show A10K2.u2426 = KTree.node A10K2.u2410 (nat_lit 41622980) (nat_lit 7761998093) (nat_lit 0) A10K2.u2425 from rfl, totK_node, atot2410, atot2425]
  decide +kernel

theorem arows2459 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2459 = true := by
  rw [show A10K2.u2459 = KTree.node A10K2.u2443 (nat_lit 42081120) (nat_lit 11322649501) (nat_lit 0) A10K2.u2458 from rfl, allE_node, arows2443, irow2459, arows2458]
  all_goals rfl

theorem atot2459 : totK PA10K2 A10K2.u2459 = [3531981968373, 23372356906843, 54111344499994, 51596050764805, 18355499370083, 2204628974764, 73382957717, 0, 0, 0] := by
  rw [show A10K2.u2459 = KTree.node A10K2.u2443 (nat_lit 42081120) (nat_lit 11322649501) (nat_lit 0) A10K2.u2458 from rfl, totK_node, atot2443, atot2458]
  decide +kernel

theorem arows2490 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2490 = true := by
  rw [show A10K2.u2490 = KTree.node A10K2.u2474 (nat_lit 42358902) (nat_lit 9342096147) (nat_lit 0) A10K2.u2489 from rfl, allE_node, arows2474, irow2490, arows2489]
  all_goals rfl

theorem atot2490 : totK PA10K2 A10K2.u2490 = [2298266100845, 14303485481192, 37256536688854, 51498024418797, 36526757617530, 10755644749505, 1224542858583, 41810754621, 0, 0] := by
  rw [show A10K2.u2490 = KTree.node A10K2.u2474 (nat_lit 42358902) (nat_lit 9342096147) (nat_lit 0) A10K2.u2489 from rfl, totK_node, atot2474, atot2489]
  decide +kernel

theorem arows2522 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2522 = true := by
  rw [show A10K2.u2522 = KTree.node A10K2.u2506 (nat_lit 42649384) (nat_lit 9838449782) (nat_lit 0) A10K2.u2521 from rfl, allE_node, arows2506, irow2522, arows2521]
  all_goals rfl

theorem atot2522 : totK PA10K2 A10K2.u2522 = [3725981149975, 23347733640047, 53336150229536, 52333992217797, 20499042254120, 2868839426650, 111884722575, 0, 0, 0] := by
  rw [show A10K2.u2522 = KTree.node A10K2.u2506 (nat_lit 42649384) (nat_lit 9838449782) (nat_lit 0) A10K2.u2521 from rfl, totK_node, atot2506, atot2521]
  decide +kernel

theorem arows2553 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2553 = true := by
  rw [show A10K2.u2553 = KTree.node A10K2.u2537 (nat_lit 42874018) (nat_lit 14523975480) (nat_lit 0) A10K2.u2552 from rfl, allE_node, arows2537, irow2553, arows2552]
  all_goals rfl

theorem atot2553 : totK PA10K2 A10K2.u2553 = [444521281299, 6595429605501, 30164276078650, 57279291229862, 45506894844835, 13103023795967, 1357952590576, 42943767608, 0, 0] := by
  rw [show A10K2.u2553 = KTree.node A10K2.u2537 (nat_lit 42874018) (nat_lit 14523975480) (nat_lit 0) A10K2.u2552 from rfl, totK_node, atot2537, atot2552]
  decide +kernel

theorem arows2588 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2588 = true := by
  rw [show A10K2.u2588 = KTree.node A10K2.u2572 (nat_lit 43075940) (nat_lit 14004928648) (nat_lit 0) A10K2.u2587 from rfl, allE_node, arows2572, irow2588, arows2587]
  all_goals rfl

theorem atot2588 : totK PA10K2 A10K2.u2588 = [5180302825155, 28291920029539, 55678350890100, 46621861693412, 15755437049070, 1951465638598, 73400861101, 0, 0, 0] := by
  rw [show A10K2.u2588 = KTree.node A10K2.u2572 (nat_lit 43075940) (nat_lit 14004928648) (nat_lit 0) A10K2.u2587 from rfl, totK_node, atot2572, atot2587]
  decide +kernel

theorem arows2619 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2619 = true := by
  rw [show A10K2.u2619 = KTree.node A10K2.u2603 (nat_lit 43331282) (nat_lit 15347524877) (nat_lit 0) A10K2.u2618 from rfl, allE_node, arows2603, irow2619, arows2618]
  all_goals rfl

theorem atot2619 : totK PA10K2 A10K2.u2619 = [568096137437, 11439090155720, 43549272832946, 60602432663139, 30667233739541, 4900667689269, 213600879417, 0, 0, 0] := by
  rw [show A10K2.u2619 = KTree.node A10K2.u2603 (nat_lit 43331282) (nat_lit 15347524877) (nat_lit 0) A10K2.u2618 from rfl, totK_node, atot2603, atot2618]
  decide +kernel

theorem arows2651 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2651 = true := by
  rw [show A10K2.u2651 = KTree.node A10K2.u2635 (nat_lit 44092190) (nat_lit 4400618324) (nat_lit 0) A10K2.u2650 from rfl, allE_node, arows2635, irow2651, arows2650]
  all_goals rfl

theorem atot2651 : totK PA10K2 A10K2.u2651 = [0, 4802762487936, 27087313464864, 55837971487140, 47898283942200, 15135061207070, 1722030192785, 48905766459, 0, 0] := by
  rw [show A10K2.u2651 = KTree.node A10K2.u2635 (nat_lit 44092190) (nat_lit 4400618324) (nat_lit 0) A10K2.u2650 from rfl, totK_node, atot2635, atot2650]
  decide +kernel

theorem arows2682 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2682 = true := by
  rw [show A10K2.u2682 = KTree.node A10K2.u2666 (nat_lit 44700278) (nat_lit 10682725284) (nat_lit 0) A10K2.u2681 from rfl, allE_node, arows2666, irow2682, arows2681]
  all_goals rfl

theorem atot2682 : totK PA10K2 A10K2.u2682 = [0, 5542193018277, 30085316250054, 57844538094922, 46099427503969, 13760181241691, 1460852438618, 43558542526, 0, 0] := by
  rw [show A10K2.u2682 = KTree.node A10K2.u2666 (nat_lit 44700278) (nat_lit 10682725284) (nat_lit 0) A10K2.u2681 from rfl, totK_node, atot2666, atot2681]
  decide +kernel

theorem arows2715 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2715 = true := by
  rw [show A10K2.u2715 = KTree.node A10K2.u2699 (nat_lit 45139968) (nat_lit 15064410632) (nat_lit 0) A10K2.u2714 from rfl, allE_node, arows2699, irow2715, arows2714]
  all_goals rfl

theorem atot2715 : totK PA10K2 A10K2.u2715 = [0, 4065656249778, 24871268434358, 55283881865951, 51251658256563, 17462256434585, 2034432936216, 79583206500, 0, 0] := by
  rw [show A10K2.u2715 = KTree.node A10K2.u2699 (nat_lit 45139968) (nat_lit 15064410632) (nat_lit 0) A10K2.u2714 from rfl, totK_node, atot2699, atot2714]
  decide +kernel

theorem arows2746 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2746 = true := by
  rw [show A10K2.u2746 = KTree.node A10K2.u2730 (nat_lit 45357091) (nat_lit 7591756734) (nat_lit 0) A10K2.u2745 from rfl, allE_node, arows2730, irow2746, arows2745]
  all_goals rfl

theorem atot2746 : totK PA10K2 A10K2.u2746 = [0, 2129015206400, 18125324195126, 49931531268364, 55170526152171, 22089258833680, 3153439610021, 141548036780, 0, 0] := by
  rw [show A10K2.u2746 = KTree.node A10K2.u2730 (nat_lit 45357091) (nat_lit 7591756734) (nat_lit 0) A10K2.u2745 from rfl, totK_node, atot2730, atot2745]
  decide +kernel

theorem arows2778 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2778 = true := by
  rw [show A10K2.u2778 = KTree.node A10K2.u2762 (nat_lit 46170614) (nat_lit 16417161895) (nat_lit 0) A10K2.u2777 from rfl, allE_node, arows2762, irow2778, arows2777]
  all_goals rfl

theorem atot2778 : totK PA10K2 A10K2.u2778 = [4451106476601, 23734482893776, 45750276817378, 40931293516749, 23908107002470, 12450176124260, 3562048469878, 384962563863, 6354482628, 0] := by
  rw [show A10K2.u2778 = KTree.node A10K2.u2762 (nat_lit 46170614) (nat_lit 16417161895) (nat_lit 0) A10K2.u2777 from rfl, totK_node, atot2762, atot2777]
  decide +kernel

theorem arows2809 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2809 = true := by
  rw [show A10K2.u2809 = KTree.node A10K2.u2793 (nat_lit 46435570) (nat_lit 11573021475) (nat_lit 0) A10K2.u2808 from rfl, allE_node, arows2793, irow2809, arows2808]
  all_goals rfl

theorem atot2809 : totK PA10K2 A10K2.u2809 = [861896674927, 9661205109045, 36210849849806, 58576232630009, 40231976790682, 10522203314694, 1077723683488, 36134558889, 0, 0] := by
  rw [show A10K2.u2809 = KTree.node A10K2.u2793 (nat_lit 46435570) (nat_lit 11573021475) (nat_lit 0) A10K2.u2808 from rfl, totK_node, atot2793, atot2808]
  decide +kernel

theorem arows2843 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2843 = true := by
  rw [show A10K2.u2843 = KTree.node A10K2.u2827 (nat_lit 46810326) (nat_lit 13364590125) (nat_lit 0) A10K2.u2842 from rfl, allE_node, arows2827, irow2843, arows2842]
  all_goals rfl

theorem atot2843 : totK PA10K2 A10K2.u2843 = [5205627883234, 28915924490984, 57541664509956, 48046897198667, 15457659029743, 1670378010119, 43558542526, 0, 0, 0] := by
  rw [show A10K2.u2843 = KTree.node A10K2.u2827 (nat_lit 46810326) (nat_lit 13364590125) (nat_lit 0) A10K2.u2842 from rfl, totK_node, atot2827, atot2842]
  decide +kernel

theorem arows2874 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2874 = true := by
  rw [show A10K2.u2874 = KTree.node A10K2.u2858 (nat_lit 47033089) (nat_lit 6298733263) (nat_lit 0) A10K2.u2873 from rfl, allE_node, arows2858, irow2874, arows2873]
  all_goals rfl

theorem atot2874 : totK PA10K2 A10K2.u2874 = [0, 6064247713801, 31784956578082, 58904746646881, 44817201619396, 12832219540463, 1348112396278, 42943767608, 0, 0] := by
  rw [show A10K2.u2874 = KTree.node A10K2.u2858 (nat_lit 47033089) (nat_lit 6298733263) (nat_lit 0) A10K2.u2873 from rfl, totK_node, atot2858, atot2873]
  decide +kernel

theorem arows2906 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2906 = true := by
  rw [show A10K2.u2906 = KTree.node A10K2.u2890 (nat_lit 47747512) (nat_lit 14561152950) (nat_lit 0) A10K2.u2905 from rfl, allE_node, arows2890, irow2906, arows2905]
  all_goals rfl

theorem atot2906 : totK PA10K2 A10K2.u2906 = [4004453979790, 23595411452136, 52067129956889, 52082812550235, 22568801799019, 3679043147288, 168530058270, 0, 0, 0] := by
  rw [show A10K2.u2906 = KTree.node A10K2.u2890 (nat_lit 47747512) (nat_lit 14561152950) (nat_lit 0) A10K2.u2905 from rfl, totK_node, atot2890, atot2905]
  decide +kernel

theorem arows2937 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2937 = true := by
  rw [show A10K2.u2937 = KTree.node A10K2.u2921 (nat_lit 47964456) (nat_lit 11799795512) (nat_lit 0) A10K2.u2936 from rfl, allE_node, arows2921, irow2937, arows2936]
  all_goals rfl

theorem atot2937 : totK PA10K2 A10K2.u2937 = [2389005205952, 16663305137454, 44417894959024, 55034969396867, 31510275186461, 7310832357487, 570694686311, 7007974415, 0, 0] := by
  rw [show A10K2.u2937 = KTree.node A10K2.u2921 (nat_lit 47964456) (nat_lit 11799795512) (nat_lit 0) A10K2.u2936 from rfl, totK_node, atot2921, atot2936]
  decide +kernel

theorem arows2970 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u2970 = true := by
  rw [show A10K2.u2970 = KTree.node A10K2.u2954 (nat_lit 48181140) (nat_lit 7967630883) (nat_lit 0) A10K2.u2969 from rfl, allE_node, arows2954, irow2970, arows2969]
  all_goals rfl

theorem atot2970 : totK PA10K2 A10K2.u2970 = [0, 4837236130847, 27405136901625, 56183408257794, 49408452124844, 17508067799438, 2185964882745, 80927666678, 0, 0] := by
  rw [show A10K2.u2970 = KTree.node A10K2.u2954 (nat_lit 48181140) (nat_lit 7967630883) (nat_lit 0) A10K2.u2969 from rfl, totK_node, atot2954, atot2969]
  decide +kernel

theorem arows3001 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3001 = true := by
  rw [show A10K2.u3001 = KTree.node A10K2.u2985 (nat_lit 48444641) (nat_lit 1020100138) (nat_lit 0) A10K2.u3000 from rfl, allE_node, arows2985, irow3001, arows3000]
  all_goals rfl

theorem atot3001 : totK PA10K2 A10K2.u3001 = [0, 3606386636262, 22575817203603, 52227919267068, 53137191516973, 22490555582693, 3336095736722, 141809884861, 0, 0] := by
  rw [show A10K2.u3001 = KTree.node A10K2.u2985 (nat_lit 48444641) (nat_lit 1020100138) (nat_lit 0) A10K2.u3000 from rfl, totK_node, atot2985, atot3000]
  decide +kernel

theorem arows3033 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3033 = true := by
  rw [show A10K2.u3033 = KTree.node A10K2.u3017 (nat_lit 48722032) (nat_lit 14893237230) (nat_lit 0) A10K2.u3032 from rfl, allE_node, arows3017, irow3033, arows3032]
  all_goals rfl

theorem atot3033 : totK PA10K2 A10K2.u3033 = [0, 2305653685916, 16047413688831, 43327537957006, 55193361431288, 32080305127439, 7150747002204, 553444716299, 7237400819, 0] := by
  rw [show A10K2.u3033 = KTree.node A10K2.u3017 (nat_lit 48722032) (nat_lit 14893237230) (nat_lit 0) A10K2.u3032 from rfl, totK_node, atot3017, atot3032]
  decide +kernel

theorem arows3064 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3064 = true := by
  rw [show A10K2.u3064 = KTree.node A10K2.u3048 (nat_lit 48981424) (nat_lit 13024836495) (nat_lit 0) A10K2.u3063 from rfl, allE_node, arows3048, irow3064, arows3063]
  all_goals rfl

theorem atot3064 : totK PA10K2 A10K2.u3064 = [0, 3761870872245, 23115659098858, 52616023035920, 52554589314059, 21532275588609, 3018373120629, 118669656475, 0, 0] := by
  rw [show A10K2.u3064 = KTree.node A10K2.u3048 (nat_lit 48981424) (nat_lit 13024836495) (nat_lit 0) A10K2.u3063 from rfl, totK_node, atot3048, atot3063]
  decide +kernel

theorem arows3100 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3100 = true := by
  rw [show A10K2.u3100 = KTree.node A10K2.u3084 (nat_lit 49231233) (nat_lit 5814867744) (nat_lit 0) A10K2.u3099 from rfl, allE_node, arows3084, irow3100, arows3099]
  all_goals rfl

theorem atot3100 : totK PA10K2 A10K2.u3100 = [0, 1870719184046, 14904441339764, 43379827911668, 56965892433057, 32780211238730, 7194870541364, 533925287213, 7380853412, 0] := by
  rw [show A10K2.u3100 = KTree.node A10K2.u3084 (nat_lit 49231233) (nat_lit 5814867744) (nat_lit 0) A10K2.u3099 from rfl, totK_node, atot3084, atot3099]
  decide +kernel

theorem arows3131 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3131 = true := by
  rw [show A10K2.u3131 = KTree.node A10K2.u3115 (nat_lit 50008099) (nat_lit 3867891954) (nat_lit 0) A10K2.u3130 from rfl, allE_node, arows3115, irow3131, arows3130]
  all_goals rfl

theorem atot3131 : totK PA10K2 A10K2.u3131 = [0, 4522740001696, 25836443951980, 54643778289015, 50846190744117, 19400321416900, 2296143038792, 50448128089, 0, 0] := by
  rw [show A10K2.u3131 = KTree.node A10K2.u3115 (nat_lit 50008099) (nat_lit 3867891954) (nat_lit 0) A10K2.u3130 from rfl, totK_node, atot3115, atot3130]
  decide +kernel

theorem arows3163 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3163 = true := by
  rw [show A10K2.u3163 = KTree.node A10K2.u3147 (nat_lit 50160542) (nat_lit 15179368968) (nat_lit 0) A10K2.u3162 from rfl, allE_node, arows3147, irow3163, arows3162]
  all_goals rfl

theorem atot3163 : totK PA10K2 A10K2.u3163 = [0, 0, 6374782736091, 33410573523998, 61080130552664, 45019273403315, 11364009483252, 859753831804, 13585869933, 0] := by
  rw [show A10K2.u3163 = KTree.node A10K2.u3147 (nat_lit 50160542) (nat_lit 15179368968) (nat_lit 0) A10K2.u3162 from rfl, totK_node, atot3147, atot3162]
  decide +kernel

theorem arows3194 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3194 = true := by
  rw [show A10K2.u3194 = KTree.node A10K2.u3178 (nat_lit 55144897) (nat_lit 8458718383) (nat_lit 0) A10K2.u3193 from rfl, allE_node, arows3178, irow3194, arows3193]
  all_goals rfl

theorem atot3194 : totK PA10K2 A10K2.u3194 = [0, 4387167801734, 22887645865985, 44517012893921, 43411415832345, 26964460857873, 10370196171851, 1639724736828, 73776485728, 0] := by
  rw [show A10K2.u3194 = KTree.node A10K2.u3178 (nat_lit 55144897) (nat_lit 8458718383) (nat_lit 0) A10K2.u3193 from rfl, totK_node, atot3178, atot3193]
  decide +kernel

theorem arows3227 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3227 = true := by
  rw [show A10K2.u3227 = KTree.node A10K2.u3211 (nat_lit 55291847) (nat_lit 14283702521) (nat_lit 0) A10K2.u3226 from rfl, allE_node, arows3211, irow3227, arows3226]
  all_goals rfl

theorem atot3227 : totK PA10K2 A10K2.u3227 = [0, 2130627667087, 16334410695188, 45565573899405, 55855596297980, 29408087957938, 6567225610883, 704606327408, 31018567651, 0] := by
  rw [show A10K2.u3227 = KTree.node A10K2.u3211 (nat_lit 55291847) (nat_lit 14283702521) (nat_lit 0) A10K2.u3226 from rfl, totK_node, atot3211, atot3226]
  decide +kernel

theorem arows3258 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3258 = true := by
  rw [show A10K2.u3258 = KTree.node A10K2.u3242 (nat_lit 55509467) (nat_lit 5462873108) (nat_lit 0) A10K2.u3257 from rfl, allE_node, arows3242, irow3258, arows3257]
  all_goals rfl

theorem atot3258 : totK PA10K2 A10K2.u3258 = [0, 1616645945202, 12459902337313, 37898813855527, 54881838490577, 36418157910377, 8944344950958, 731630013637, 11925199957, 0] := by
  rw [show A10K2.u3258 = KTree.node A10K2.u3242 (nat_lit 55509467) (nat_lit 5462873108) (nat_lit 0) A10K2.u3257 from rfl, totK_node, atot3242, atot3257]
  decide +kernel

theorem arows3290 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3290 = true := by
  rw [show A10K2.u3290 = KTree.node A10K2.u3274 (nat_lit 55710477) (nat_lit 5796375195) (nat_lit 0) A10K2.u3289 from rfl, allE_node, arows3274, irow3290, arows3289]
  all_goals rfl

theorem atot3290 : totK PA10K2 A10K2.u3290 = [0, 4054086288098, 24920043565845, 54710728220398, 50041226097476, 17018038590142, 1879635093061, 49005728400, 0, 0] := by
  rw [show A10K2.u3290 = KTree.node A10K2.u3274 (nat_lit 55710477) (nat_lit 5796375195) (nat_lit 0) A10K2.u3289 from rfl, totK_node, atot3274, atot3289]
  decide +kernel

theorem arows3321 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3321 = true := by
  rw [show A10K2.u3321 = KTree.node A10K2.u3305 (nat_lit 56002636) (nat_lit 10942262896) (nat_lit 0) A10K2.u3320 from rfl, allE_node, arows3305, irow3321, arows3320]
  all_goals rfl

theorem atot3321 : totK PA10K2 A10K2.u3321 = [0, 2233135491413, 16067989944572, 44354352107870, 56259526139064, 29952251452753, 5734644086953, 394882282575, 6354482628, 0] := by
  rw [show A10K2.u3321 = KTree.node A10K2.u3305 (nat_lit 56002636) (nat_lit 10942262896) (nat_lit 0) A10K2.u3320 from rfl, totK_node, atot3305, atot3320]
  decide +kernel

theorem arows3355 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3355 = true := by
  rw [show A10K2.u3355 = KTree.node A10K2.u3339 (nat_lit 56309206) (nat_lit 15509087285) (nat_lit 0) A10K2.u3354 from rfl, allE_node, arows3339, irow3355, arows3354]
  all_goals rfl

theorem atot3355 : totK PA10K2 A10K2.u3355 = [0, 3656557161077, 23071535733653, 53320603902022, 53627348468146, 21973189969313, 3099769204797, 120169311940, 0, 0] := by
  rw [show A10K2.u3355 = KTree.node A10K2.u3339 (nat_lit 56309206) (nat_lit 15509087285) (nat_lit 0) A10K2.u3354 from rfl, totK_node, atot3339, atot3354]
  decide +kernel

theorem arows3386 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3386 = true := by
  rw [show A10K2.u3386 = KTree.node A10K2.u3370 (nat_lit 56484283) (nat_lit 6453676462) (nat_lit 0) A10K2.u3385 from rfl, allE_node, arows3370, irow3386, arows3385]
  all_goals rfl

theorem atot3386 : totK PA10K2 A10K2.u3386 = [0, 0, 4501964353754, 27833631614974, 59692873509946, 51105013616793, 15262051916538, 1228266921778, 13590611789, 0] := by
  rw [show A10K2.u3386 = KTree.node A10K2.u3370 (nat_lit 56484283) (nat_lit 6453676462) (nat_lit 0) A10K2.u3385 from rfl, totK_node, atot3370, atot3385]
  decide +kernel

theorem arows3418 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3418 = true := by
  rw [show A10K2.u3418 = KTree.node A10K2.u3402 (nat_lit 57271739) (nat_lit 7035925206) (nat_lit 0) A10K2.u3417 from rfl, allE_node, arows3402, irow3418, arows3417]
  all_goals rfl

theorem atot3418 : totK PA10K2 A10K2.u3418 = [0, 0, 5661678052724, 29754878346644, 56159362346371, 44893584342768, 14720346865283, 2032238333919, 85433762096, 0] := by
  rw [show A10K2.u3418 = KTree.node A10K2.u3402 (nat_lit 57271739) (nat_lit 7035925206) (nat_lit 0) A10K2.u3417 from rfl, totK_node, atot3402, atot3417]
  decide +kernel

theorem arows3449 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3449 = true := by
  rw [show A10K2.u3449 = KTree.node A10K2.u3433 (nat_lit 57498280) (nat_lit 7454536796) (nat_lit 0) A10K2.u3448 from rfl, allE_node, arows3433, irow3449, arows3448]
  all_goals rfl

theorem atot3449 : totK PA10K2 A10K2.u3449 = [0, 0, 834905328705, 10950172640123, 39761297859719, 57668933849524, 35047493854135, 9024157873822, 1008140456562, 36704093874] := by
  rw [show A10K2.u3449 = KTree.node A10K2.u3433 (nat_lit 57498280) (nat_lit 7454536796) (nat_lit 0) A10K2.u3448 from rfl, totK_node, atot3433, atot3448]
  decide +kernel

theorem arows3482 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3482 = true := by
  rw [show A10K2.u3482 = KTree.node A10K2.u3466 (nat_lit 57706553) (nat_lit 7301559857) (nat_lit 0) A10K2.u3481 from rfl, allE_node, arows3466, irow3482, arows3481]
  all_goals rfl

theorem atot3482 : totK PA10K2 A10K2.u3482 = [0, 0, 3486035242789, 21157626355320, 48518006992139, 50896455806346, 24333256336582, 4785416854700, 370596093263, 5982052406] := by
  rw [show A10K2.u3482 = KTree.node A10K2.u3466 (nat_lit 57706553) (nat_lit 7301559857) (nat_lit 0) A10K2.u3481 from rfl, totK_node, atot3466, atot3481]
  decide +kernel

theorem arows3513 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3513 = true := by
  rw [show A10K2.u3513 = KTree.node A10K2.u3497 (nat_lit 57951404) (nat_lit 12833588919) (nat_lit 0) A10K2.u3512 from rfl, allE_node, arows3497, irow3513, arows3512]
  all_goals rfl

theorem atot3513 : totK PA10K2 A10K2.u3513 = [0, 0, 2171906535597, 18457383658632, 51095073561738, 55766035447574, 21356241811384, 2688311169663, 100063874953, 0] := by
  rw [show A10K2.u3513 = KTree.node A10K2.u3497 (nat_lit 57951404) (nat_lit 12833588919) (nat_lit 0) A10K2.u3512 from rfl, totK_node, atot3497, atot3512]
  decide +kernel

theorem arows3545 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3545 = true := by
  rw [show A10K2.u3545 = KTree.node A10K2.u3529 (nat_lit 58289906) (nat_lit 14783059945) (nat_lit 0) A10K2.u3544 from rfl, allE_node, arows3529, irow3545, arows3544]
  all_goals rfl

theorem atot3545 : totK PA10K2 A10K2.u3545 = [0, 0, 5884209907460, 29423454719011, 53913812268594, 45409542369133, 18954772097653, 3687978218316, 303043821087, 6354482628] := by
  rw [show A10K2.u3545 = KTree.node A10K2.u3529 (nat_lit 58289906) (nat_lit 14783059945) (nat_lit 0) A10K2.u3544 from rfl, totK_node, atot3529, atot3544]
  decide +kernel

theorem arows3576 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3576 = true := by
  rw [show A10K2.u3576 = KTree.node A10K2.u3560 (nat_lit 58757511) (nat_lit 14213163043) (nat_lit 0) A10K2.u3575 from rfl, allE_node, arows3560, irow3576, arows3575]
  all_goals rfl

theorem atot3576 : totK PA10K2 A10K2.u3576 = [0, 4328003150587, 24098009618743, 48943508296945, 45703529848565, 23185886189188, 7735109191759, 1146979205339, 48968269916, 0] := by
  rw [show A10K2.u3576 = KTree.node A10K2.u3560 (nat_lit 58757511) (nat_lit 14213163043) (nat_lit 0) A10K2.u3575 from rfl, totK_node, atot3560, atot3575]
  decide +kernel

theorem arows3611 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3611 = true := by
  rw [show A10K2.u3611 = KTree.node A10K2.u3595 (nat_lit 59135149) (nat_lit 6464684803) (nat_lit 0) A10K2.u3610 from rfl, allE_node, arows3595, irow3611, arows3610]
  all_goals rfl

theorem atot3611 : totK PA10K2 A10K2.u3611 = [0, 2298266100845, 16188705386918, 44437283566804, 55858999376403, 28960409518129, 5433988646641, 374219459224, 5676195732, 0] := by
  rw [show A10K2.u3611 = KTree.node A10K2.u3595 (nat_lit 59135149) (nat_lit 6464684803) (nat_lit 0) A10K2.u3610 from rfl, totK_node, atot3595, atot3610]
  decide +kernel

theorem arows3642 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3642 = true := by
  rw [show A10K2.u3642 = KTree.node A10K2.u3626 (nat_lit 59426523) (nat_lit 8782552603) (nat_lit 0) A10K2.u3641 from rfl, allE_node, arows3626, irow3642, arows3641]
  all_goals rfl

theorem atot3642 : totK PA10K2 A10K2.u3642 = [0, 3725981149975, 23347733640047, 53394694537829, 52472036180623, 20486988354332, 2801018640894, 97930205976, 0, 0] := by
  rw [show A10K2.u3642 = KTree.node A10K2.u3626 (nat_lit 59426523) (nat_lit 8782552603) (nat_lit 0) A10K2.u3641 from rfl, totK_node, atot3626, atot3641]
  decide +kernel

theorem arows3674 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3674 = true := by
  rw [show A10K2.u3674 = KTree.node A10K2.u3658 (nat_lit 59651507) (nat_lit 9905990438) (nat_lit 0) A10K2.u3673 from rfl, allE_node, arows3658, irow3674, arows3673]
  all_goals rfl

theorem atot3674 : totK PA10K2 A10K2.u3674 = [0, 573258531646, 7244304629258, 30853075267880, 57180851704230, 44579598993711, 12666885446163, 1332710594513, 42943767608, 0] := by
  rw [show A10K2.u3674 = KTree.node A10K2.u3658 (nat_lit 59651507) (nat_lit 9905990438) (nat_lit 0) A10K2.u3673 from rfl, totK_node, atot3658, atot3673]
  decide +kernel

theorem arows3705 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3705 = true := by
  rw [show A10K2.u3705 = KTree.node A10K2.u3689 (nat_lit 59856100) (nat_lit 13288066281) (nat_lit 0) A10K2.u3704 from rfl, allE_node, arows3689, irow3705, arows3704]
  all_goals rfl

theorem atot3705 : totK PA10K2 A10K2.u3705 = [0, 5319866894745, 28639004206421, 55983753628371, 46528782231690, 15233122606582, 1829924681247, 73400861101, 0, 0] := by
  rw [show A10K2.u3705 = KTree.node A10K2.u3689 (nat_lit 59856100) (nat_lit 13288066281) (nat_lit 0) A10K2.u3704 from rfl, totK_node, atot3689, atot3704]
  decide +kernel

theorem arows3738 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3738 = true := by
  rw [show A10K2.u3738 = KTree.node A10K2.u3722 (nat_lit 60110998) (nat_lit 13235960734) (nat_lit 0) A10K2.u3737 from rfl, allE_node, arows3722, irow3738, arows3737]
  all_goals rfl

theorem atot3738 : totK PA10K2 A10K2.u3738 = [0, 295989007569, 10454124608065, 43001884556173, 61681817066297, 31063934870578, 4926443166602, 218614076901, 0, 0] := by
  rw [show A10K2.u3738 = KTree.node A10K2.u3722 (nat_lit 60110998) (nat_lit 13235960734) (nat_lit 0) A10K2.u3737 from rfl, totK_node, atot3722, atot3737]
  decide +kernel

theorem arows3769 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3769 = true := by
  rw [show A10K2.u3769 = KTree.node A10K2.u3753 (nat_lit 60950805) (nat_lit 7022094326) (nat_lit 0) A10K2.u3768 from rfl, allE_node, arows3753, irow3769, arows3768]
  all_goals rfl

theorem atot3769 : totK PA10K2 A10K2.u3769 = [0, 0, 5638142503332, 30707108379986, 59260108650875, 45008980598555, 11222231034198, 1005526645447, 18255270229, 0] := by
  rw [show A10K2.u3769 = KTree.node A10K2.u3753 (nat_lit 60950805) (nat_lit 7022094326) (nat_lit 0) A10K2.u3768 from rfl, totK_node, atot3753, atot3768]
  decide +kernel

theorem arows3801 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3801 = true := by
  rw [show A10K2.u3801 = KTree.node A10K2.u3785 (nat_lit 61489228) (nat_lit 10832124752) (nat_lit 0) A10K2.u3800 from rfl, allE_node, arows3785, irow3801, arows3800]
  all_goals rfl

theorem atot3801 : totK PA10K2 A10K2.u3801 = [0, 0, 4706813002881, 27596678376234, 57616822096297, 49054407137530, 15072480583860, 1650156026226, 50605567978, 0] := by
  rw [show A10K2.u3801 = KTree.node A10K2.u3785 (nat_lit 61489228) (nat_lit 10832124752) (nat_lit 0) A10K2.u3800 from rfl, totK_node, atot3785, atot3800]
  decide +kernel

theorem arows3832 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.u3832 = true := by
  rw [show A10K2.u3832 = KTree.node A10K2.u3816 (nat_lit 61949434) (nat_lit 13326003171) (nat_lit 0) A10K2.u3831 from rfl, allE_node, arows3816, irow3832, arows3831]
  all_goals rfl

theorem atot3832 : totK PA10K2 A10K2.u3832 = [0, 0, 5612147977312, 30426405079741, 58617668028764, 45387824374604, 12380687127332, 1252420504035, 42315302678, 0] := by
  rw [show A10K2.u3832 = KTree.node A10K2.u3816 (nat_lit 61949434) (nat_lit 13326003171) (nat_lit 0) A10K2.u3831 from rfl, totK_node, atot3816, atot3831]
  decide +kernel

end QECKChecks.A10K2
