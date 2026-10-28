import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12420 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12420 = true := by
  decide +kernel

theorem tot12420 : totK PD2M8K2 D2M8K2.t12420 = [0, 0, 193905950981, 486967178740, 221315099749, 13656771860, 0, 0] := by
  decide +kernel

theorem rows12421 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12421 = true := by
  decide +kernel

theorem tot12421 : totK PD2M8K2 D2M8K2.t12421 = [0, 85737809554, 322603016411, 380788335675, 107566513225, 1409560813, 0, 0] := by
  decide +kernel

theorem rows12422 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12422 = true := by
  decide +kernel

theorem tot12422 : totK PD2M8K2 D2M8K2.t12422 = [0, 182360342507, 468783972053, 258297685112, 22543228716, 0, 0, 0] := by
  decide +kernel

theorem rows12423 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12423 = true := by
  decide +kernel

theorem tot12423 : totK PD2M8K2 D2M8K2.t12423 = [0, 171119923925, 459890866564, 251725886561, 16264961213, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
