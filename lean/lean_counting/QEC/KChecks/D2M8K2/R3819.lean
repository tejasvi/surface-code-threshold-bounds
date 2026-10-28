import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15276 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15276 = true := by
  decide +kernel

theorem tot15276 : totK PD2M8K2 D2M8K2.t15276 = [0, 0, 0, 274658599765, 505721244397, 121493370154, 3699256714, 0] := by
  decide +kernel

theorem rows15277 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15277 = true := by
  decide +kernel

theorem tot15277 : totK PD2M8K2 D2M8K2.t15277 = [0, 0, 160530476227, 377052434458, 248025915763, 95690163123, 8752647282, 0] := by
  decide +kernel

theorem rows15278 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15278 = true := by
  decide +kernel

theorem tot15278 : totK PD2M8K2 D2M8K2.t15278 = [0, 0, 171393450466, 454612550938, 237938053430, 13753366721, 0, 0] := by
  decide +kernel

theorem rows15279 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15279 = true := by
  decide +kernel

theorem tot15279 : totK PD2M8K2 D2M8K2.t15279 = [0, 0, 86223291902, 345150137668, 371911142294, 81809657499, 1369150432, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
