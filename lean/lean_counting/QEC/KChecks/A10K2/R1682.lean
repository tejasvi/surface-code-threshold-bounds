import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6728 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6728 = true := by
  decide +kernel

theorem tot6728 : totK PA10K2 A10K2.t6728 = [386689141914, 1282502927551, 1555083906339, 1157809775004, 504932630311, 50499610055, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6729 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6729 = true := by
  decide +kernel

theorem tot6729 : totK PA10K2 A10K2.t6729 = [361884947501, 1661607395570, 2106221107181, 798874743923, 71345411225, 0, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6730 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6730 = true := by
  decide +kernel

theorem tot6730 : totK PA10K2 A10K2.t6730 = [0, 502047432904, 1848557455474, 1889136252718, 508549123585, 31768748853, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6731 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t6731 = true := by
  decide +kernel

theorem tot6731 : totK PA10K2 A10K2.t6731 = [561217355197, 1765342837735, 1827735248653, 726326827124, 75429086622, 0, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
