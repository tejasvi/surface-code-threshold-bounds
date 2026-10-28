import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows13356 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13356 = true := by
  decide +kernel

theorem tot13356 : totK PD2M8K2 D2M8K2.t13356 = [0, 193678052207, 471413384322, 221633760073, 12534051746, 0, 0, 0] := by
  decide +kernel

theorem rows13357 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13357 = true := by
  decide +kernel

theorem tot13357 : totK PD2M8K2 D2M8K2.t13357 = [0, 20657074147, 290856111908, 455205503917, 101006207396, 1369150432, 0, 0] := by
  decide +kernel

theorem rows13358 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13358 = true := by
  decide +kernel

theorem tot13358 : totK PD2M8K2 D2M8K2.t13358 = [0, 93258520378, 384325767639, 396652952802, 43347949421, 0, 0, 0] := by
  decide +kernel

theorem rows13359 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13359 = true := by
  decide +kernel

theorem tot13359 : totK PD2M8K2 D2M8K2.t13359 = [0, 174154336335, 432993422214, 272512775885, 30462929994, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
