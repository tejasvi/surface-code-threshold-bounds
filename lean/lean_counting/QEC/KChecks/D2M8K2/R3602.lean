import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14408 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14408 = true := by
  decide +kernel

theorem tot14408 : totK PD2M8K2 D2M8K2.t14408 = [0, 92930711933, 388664983334, 395003552785, 40643641273, 0, 0, 0] := by
  decide +kernel

theorem rows14409 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14409 = true := by
  decide +kernel

theorem tot14409 : totK PD2M8K2 D2M8K2.t14409 = [0, 168289758596, 436700186047, 280388229555, 29382719343, 0, 0, 0] := by
  decide +kernel

theorem rows14410 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14410 = true := by
  decide +kernel

theorem tot14410 : totK PD2M8K2 D2M8K2.t14410 = [0, 157931054148, 476413163407, 271664374132, 13648479505, 0, 0, 0] := by
  decide +kernel

theorem rows14411 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14411 = true := by
  decide +kernel

theorem tot14411 : totK PD2M8K2 D2M8K2.t14411 = [0, 0, 179946020997, 451072256908, 248360491988, 22212564151, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
