import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14340 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14340 = true := by
  decide +kernel

theorem tot14340 : totK PD2M8K2 D2M8K2.t14340 = [0, 172800148695, 464368721318, 262732062077, 20212863757, 0, 0, 0] := by
  decide +kernel

theorem rows14341 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14341 = true := by
  decide +kernel

theorem tot14341 : totK PD2M8K2 D2M8K2.t14341 = [0, 0, 237245265274, 496895817079, 153955392803, 4925188030, 0, 0] := by
  decide +kernel

theorem rows14342 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14342 = true := by
  decide +kernel

theorem tot14342 : totK PD2M8K2 D2M8K2.t14342 = [0, 18872545859, 183119837219, 458766421189, 213059837135, 12866082196, 0, 0] := by
  decide +kernel

theorem rows14343 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14343 = true := by
  decide +kernel

theorem tot14343 : totK PD2M8K2 D2M8K2.t14343 = [0, 197565998199, 489961564090, 205252523092, 9852138406, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
