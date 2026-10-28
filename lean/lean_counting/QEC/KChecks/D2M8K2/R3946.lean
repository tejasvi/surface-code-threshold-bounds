import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15784 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15784 = true := by
  decide +kernel

theorem tot15784 : totK PD2M8K2 D2M8K2.t15784 = [0, 0, 333566504060, 507831897354, 65418538336, 0, 0, 0] := by
  decide +kernel

theorem rows15785 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15785 = true := by
  decide +kernel

theorem tot15785 : totK PD2M8K2 D2M8K2.t15785 = [0, 205522976420, 478584583844, 207131925390, 12835841801, 0, 0, 0] := by
  decide +kernel

theorem rows15786 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15786 = true := by
  decide +kernel

theorem tot15786 : totK PD2M8K2 D2M8K2.t15786 = [0, 119573466220, 437454877072, 311832904354, 26311617920, 0, 0, 0] := by
  decide +kernel

theorem rows15787 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15787 = true := by
  decide +kernel

theorem tot15787 : totK PD2M8K2 D2M8K2.t15787 = [0, 0, 216955725415, 501049167658, 160023864530, 5398830306, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
