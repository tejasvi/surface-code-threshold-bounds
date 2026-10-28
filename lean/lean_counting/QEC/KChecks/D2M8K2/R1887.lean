import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7548 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7548 = true := by
  decide +kernel

theorem tot7548 : totK PD2M8K2 D2M8K2.t7548 = [0, 93301704879, 387477594153, 386950298935, 50886639738, 0, 0, 0] := by
  decide +kernel

theorem rows7549 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7549 = true := by
  decide +kernel

theorem tot7549 : totK PD2M8K2 D2M8K2.t7549 = [0, 158776235429, 445802806355, 287732885701, 23875090196, 0, 0, 0] := by
  decide +kernel

theorem rows7550 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7550 = true := by
  decide +kernel

theorem tot7550 : totK PD2M8K2 D2M8K2.t7550 = [0, 174333546275, 464836420321, 249948920572, 14393959698, 0, 0, 0] := by
  decide +kernel

theorem rows7551 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7551 = true := by
  decide +kernel

theorem tot7551 : totK PD2M8K2 D2M8K2.t7551 = [0, 0, 182466984318, 451078050395, 255143339371, 24987864049, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
