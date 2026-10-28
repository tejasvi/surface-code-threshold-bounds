import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8396 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8396 = true := by
  decide +kernel

theorem tot8396 : totK PD2M8K2 D2M8K2.t8396 = [0, 0, 225743897816, 480286395591, 150363254697, 9362943456, 0, 0] := by
  decide +kernel

theorem rows8397 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8397 = true := by
  decide +kernel

theorem tot8397 : totK PD2M8K2 D2M8K2.t8397 = [0, 153157419074, 424669300466, 266839010710, 48845504327, 2531362957, 0, 0] := by
  decide +kernel

theorem rows8398 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8398 = true := by
  decide +kernel

theorem tot8398 : totK PD2M8K2 D2M8K2.t8398 = [0, 167975977046, 426726048194, 256910183098, 18036423983, 0, 0, 0] := by
  decide +kernel

theorem rows8399 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8399 = true := by
  decide +kernel

theorem tot8399 : totK PD2M8K2 D2M8K2.t8399 = [0, 90881889911, 367129124442, 357342621118, 65684697845, 1096505104, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
