import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4452 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4452 = true := by
  decide +kernel

theorem tot4452 : totK PD2M8K2 D2M8K2.t4452 = [0, 0, 173522962943, 447121296173, 238919753255, 18225150272, 0, 0] := by
  decide +kernel

theorem rows4453 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4453 = true := by
  decide +kernel

theorem tot4453 : totK PD2M8K2 D2M8K2.t4453 = [0, 0, 191221386977, 488146406941, 194496962598, 9840992866, 0, 0] := by
  decide +kernel

theorem rows4454 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4454 = true := by
  decide +kernel

theorem tot4454 : totK PD2M8K2 D2M8K2.t4454 = [0, 0, 185146314649, 470025377836, 195462716164, 7293741701, 0, 0] := by
  decide +kernel

theorem rows4455 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4455 = true := by
  decide +kernel

theorem tot4455 : totK PD2M8K2 D2M8K2.t4455 = [0, 0, 0, 286466624005, 470428093581, 85241021647, 1206465782, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
