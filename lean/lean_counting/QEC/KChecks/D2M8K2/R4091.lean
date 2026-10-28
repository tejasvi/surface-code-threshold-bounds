import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows16364 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16364 = true := by
  decide +kernel

theorem tot16364 : totK PD2M8K2 D2M8K2.t16364 = [0, 0, 93924006320, 354303277007, 381281377053, 82337772830, 1268739303, 0] := by
  decide +kernel

theorem rows16365 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16365 = true := by
  decide +kernel

theorem tot16365 : totK PD2M8K2 D2M8K2.t16365 = [0, 0, 0, 245458713001, 501856794783, 146328026127, 3699256714, 0] := by
  decide +kernel

theorem rows16366 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16366 = true := by
  decide +kernel

theorem tot16366 : totK PD2M8K2 D2M8K2.t16366 = [0, 0, 0, 183418471542, 459667739050, 228755498781, 18450603579, 0] := by
  decide +kernel

theorem rows16367 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t16367 = true := by
  decide +kernel

theorem tot16367 : totK PD2M8K2 D2M8K2.t16367 = [0, 0, 0, 168279822539, 472828367230, 208132691724, 7871360470, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
