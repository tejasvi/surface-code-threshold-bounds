import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6660 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6660 = true := by
  decide +kernel

theorem tot6660 : totK PD2M8K2 D2M8K2.t6660 = [0, 0, 297574429111, 490403962046, 95447275975, 1310166938, 0, 0] := by
  decide +kernel

theorem rows6661 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6661 = true := by
  decide +kernel

theorem tot6661 : totK PD2M8K2 D2M8K2.t6661 = [0, 92864519961, 380085215594, 391307272535, 45803734787, 0, 0, 0] := by
  decide +kernel

theorem rows6662 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6662 = true := by
  decide +kernel

theorem tot6662 : totK PD2M8K2 D2M8K2.t6662 = [0, 157403206224, 449324003044, 285692103791, 22258561889, 0, 0, 0] := by
  decide +kernel

theorem rows6663 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6663 = true := by
  decide +kernel

theorem tot6663 : totK PD2M8K2 D2M8K2.t6663 = [0, 167763158497, 458474962887, 261997967339, 26144371347, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
