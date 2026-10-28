import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3272 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3272 = true := by
  decide +kernel

theorem tot3272 : totK PD2M8K2 D2M8K2.t3272 = [0, 191795818850, 444250666797, 200644425320, 48364542212, 9604228008, 0, 0] := by
  decide +kernel

theorem rows3273 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3273 = true := by
  decide +kernel

theorem tot3273 : totK PD2M8K2 D2M8K2.t3273 = [0, 192215691749, 463413202391, 221984194005, 12534051746, 0, 0, 0] := by
  decide +kernel

theorem rows3274 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3274 = true := by
  decide +kernel

theorem tot3274 : totK PD2M8K2 D2M8K2.t3274 = [0, 37537489105, 317355363529, 433666790989, 97331119184, 1369150432, 0, 0] := by
  decide +kernel

theorem rows3275 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3275 = true := by
  decide +kernel

theorem tot3275 : totK PD2M8K2 D2M8K2.t3275 = [0, 68710591346, 355493773288, 427987063103, 54286747035, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
