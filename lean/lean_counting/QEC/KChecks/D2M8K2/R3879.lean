import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15516 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15516 = true := by
  decide +kernel

theorem tot15516 : totK PD2M8K2 D2M8K2.t15516 = [0, 84618337556, 356915689038, 369615437656, 69399552696, 1096505104, 0, 0] := by
  decide +kernel

theorem rows15517 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15517 = true := by
  decide +kernel

theorem tot15517 : totK PD2M8K2 D2M8K2.t15517 = [0, 32798473230, 274074553869, 463651119353, 112038067230, 3884009855, 0, 0] := by
  decide +kernel

theorem rows15518 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15518 = true := by
  decide +kernel

theorem tot15518 : totK PD2M8K2 D2M8K2.t15518 = [0, 193224896075, 472633956944, 232198005252, 20479154101, 0, 0, 0] := by
  decide +kernel

theorem rows15519 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15519 = true := by
  decide +kernel

theorem tot15519 : totK PD2M8K2 D2M8K2.t15519 = [0, 190252047346, 464860631883, 234128795761, 15192131316, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
