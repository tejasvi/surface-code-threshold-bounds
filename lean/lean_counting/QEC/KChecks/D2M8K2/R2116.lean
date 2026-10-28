import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8464 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8464 = true := by
  decide +kernel

theorem tot8464 : totK PD2M8K2 D2M8K2.t8464 = [0, 156696092151, 461909920754, 266505871649, 20294322346, 0, 0, 0] := by
  decide +kernel

theorem rows8465 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8465 = true := by
  decide +kernel

theorem tot8465 : totK PD2M8K2 D2M8K2.t8465 = [0, 0, 242218491993, 512759991856, 130993794185, 2348440009, 0, 0] := by
  decide +kernel

theorem rows8466 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8466 = true := by
  decide +kernel

theorem tot8466 : totK PD2M8K2 D2M8K2.t8466 = [0, 86654048599, 277787659370, 369905270482, 134259991056, 10835877391, 0, 0] := by
  decide +kernel

theorem rows8467 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8467 = true := by
  decide +kernel

theorem tot8467 : totK PD2M8K2 D2M8K2.t8467 = [0, 168512129870, 458997534287, 253554415218, 20321318001, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
