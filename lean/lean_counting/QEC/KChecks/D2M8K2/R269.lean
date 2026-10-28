import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1076 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1076 = true := by
  decide +kernel

theorem tot1076 : totK PD2M8K2 D2M8K2.t1076 = [0, 0, 303081746575, 495155381560, 89510258080, 1096505104, 0, 0] := by
  decide +kernel

theorem rows1077 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1077 = true := by
  decide +kernel

theorem tot1077 : totK PD2M8K2 D2M8K2.t1077 = [0, 83671481343, 302343736595, 388747854924, 111888592590, 3884009855, 0, 0] := by
  decide +kernel

theorem rows1078 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1078 = true := by
  decide +kernel

theorem tot1078 : totK PD2M8K2 D2M8K2.t1078 = [0, 165609696886, 496746277896, 230779369700, 6599752875, 0, 0, 0] := by
  decide +kernel

theorem rows1079 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1079 = true := by
  decide +kernel

theorem tot1079 : totK PD2M8K2 D2M8K2.t1079 = [0, 88808070666, 350633389060, 378828738165, 75711161411, 1268739303, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
