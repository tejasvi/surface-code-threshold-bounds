import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows2632 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2632 = true := by
  decide +kernel

theorem tot2632 : totK PA10K2 A10K2.t2632 = [0, 0, 908655032647, 2360090968128, 1266363618255, 113083894467, 0, 0, 0, 0] := by
  decide +kernel

theorem rows2633 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2633 = true := by
  decide +kernel

theorem tot2633 : totK PA10K2 A10K2.t2633 = [0, 514294859655, 1634371751284, 1725051688305, 866851388147, 187427344329, 6354482628, 0, 0, 0] := by
  decide +kernel

theorem rows2634 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2634 = true := by
  decide +kernel

theorem tot2634 : totK PA10K2 A10K2.t2634 = [0, 65520693115, 905603889179, 2169092409504, 1623867923650, 289364466793, 6853348008, 0, 0, 0] := by
  decide +kernel

theorem rows2635 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t2635 = true := by
  decide +kernel

theorem tot2635 : totK PA10K2 A10K2.t2635 = [0, 0, 546916786196, 1948879094146, 1955401110079, 549245883414, 34004712665, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
