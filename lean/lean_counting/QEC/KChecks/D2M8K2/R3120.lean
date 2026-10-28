import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12480 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12480 = true := by
  decide +kernel

theorem tot12480 : totK PD2M8K2 D2M8K2.t12480 = [0, 177227747895, 453175855146, 244005162222, 18185084111, 0, 0, 0] := by
  decide +kernel

theorem rows12481 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12481 = true := by
  decide +kernel

theorem tot12481 : totK PD2M8K2 D2M8K2.t12481 = [0, 0, 311499197296, 491746379495, 90468037398, 1096505104, 0, 0] := by
  decide +kernel

theorem rows12482 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12482 = true := by
  decide +kernel

theorem tot12482 : totK PD2M8K2 D2M8K2.t12482 = [0, 88185535531, 307226179490, 387648533937, 110305409809, 3884009855, 0, 0] := by
  decide +kernel

theorem rows12483 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12483 = true := by
  decide +kernel

theorem tot12483 : totK PD2M8K2 D2M8K2.t12483 = [0, 151035210360, 446860613688, 269600274693, 17279214308, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
