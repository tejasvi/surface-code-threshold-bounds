import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8484 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8484 = true := by
  decide +kernel

theorem tot8484 : totK PD2M8K2 D2M8K2.t8484 = [0, 0, 217495688701, 507943230505, 165230927290, 5193381917, 0, 0] := by
  decide +kernel

theorem rows8485 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8485 = true := by
  decide +kernel

theorem tot8485 : totK PD2M8K2 D2M8K2.t8485 = [0, 152999581501, 436234097887, 296227732250, 33334509802, 0, 0, 0] := by
  decide +kernel

theorem rows8486 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8486 = true := by
  decide +kernel

theorem tot8486 : totK PD2M8K2 D2M8K2.t8486 = [0, 173511456822, 443306931491, 266292088106, 25619109940, 0, 0, 0] := by
  decide +kernel

theorem rows8487 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8487 = true := by
  decide +kernel

theorem tot8487 : totK PD2M8K2 D2M8K2.t8487 = [0, 112781078216, 434665551600, 339401457189, 28441864929, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
