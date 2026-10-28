import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9080 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9080 = true := by
  decide +kernel

theorem tot9080 : totK PD2M8K2 D2M8K2.t9080 = [0, 0, 314351702055, 522124262477, 75966821375, 0, 0, 0] := by
  decide +kernel

theorem rows9081 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9081 = true := by
  decide +kernel

theorem tot9081 : totK PD2M8K2 D2M8K2.t9081 = [0, 173066691409, 387681055498, 251316454391, 77907061280, 3884009855, 0, 0] := by
  decide +kernel

theorem rows9082 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9082 = true := by
  decide +kernel

theorem tot9082 : totK PD2M8K2 D2M8K2.t9082 = [0, 157331397848, 450155046032, 280859221271, 20945668021, 0, 0, 0] := by
  decide +kernel

theorem rows9083 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9083 = true := by
  decide +kernel

theorem tot9083 : totK PD2M8K2 D2M8K2.t9083 = [0, 92620862180, 344328139096, 374309406495, 75107290026, 1268739303, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
