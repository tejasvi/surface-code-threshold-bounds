import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6624 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6624 = true := by
  decide +kernel

theorem tot6624 : totK PD2M8K2 D2M8K2.t6624 = [0, 0, 294338569540, 514001418449, 85812243815, 0, 0, 0] := by
  decide +kernel

theorem rows6625 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6625 = true := by
  decide +kernel

theorem tot6625 : totK PD2M8K2 D2M8K2.t6625 = [0, 170310974658, 390638723504, 252811791648, 77841906337, 3884009855, 0, 0] := by
  decide +kernel

theorem rows6626 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6626 = true := by
  decide +kernel

theorem tot6626 : totK PD2M8K2 D2M8K2.t6626 = [0, 155260542918, 458562817780, 265956238686, 14616838744, 0, 0, 0] := by
  decide +kernel

theorem rows6627 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6627 = true := by
  decide +kernel

theorem tot6627 : totK PD2M8K2 D2M8K2.t6627 = [0, 0, 276071861392, 508816218897, 104536551779, 1268739303, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
