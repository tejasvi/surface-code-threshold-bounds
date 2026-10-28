import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3284 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3284 = true := by
  decide +kernel

theorem tot3284 : totK PD2M8K2 D2M8K2.t3284 = [0, 169483356863, 459527208606, 259986116620, 22456801898, 0, 0, 0] := by
  decide +kernel

theorem rows3285 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3285 = true := by
  decide +kernel

theorem tot3285 : totK PD2M8K2 D2M8K2.t3285 = [0, 147955916819, 448335963274, 288508945009, 23550797660, 0, 0, 0] := by
  decide +kernel

theorem rows3286 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3286 = true := by
  decide +kernel

theorem tot3286 : totK PD2M8K2 D2M8K2.t3286 = [0, 0, 266225992302, 505991690864, 120578834481, 1268739303, 0, 0] := by
  decide +kernel

theorem rows3287 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3287 = true := by
  decide +kernel

theorem tot3287 : totK PD2M8K2 D2M8K2.t3287 = [0, 0, 197180846048, 476621157124, 197381405295, 12482056447, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
