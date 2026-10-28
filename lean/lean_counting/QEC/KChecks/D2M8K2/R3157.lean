import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12628 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12628 = true := by
  decide +kernel

theorem tot12628 : totK PD2M8K2 D2M8K2.t12628 = [0, 0, 191594449828, 452650587334, 232633668414, 17115888737, 0, 0] := by
  decide +kernel

theorem rows12629 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12629 = true := by
  decide +kernel

theorem tot12629 : totK PD2M8K2 D2M8K2.t12629 = [0, 0, 86006868874, 410695679399, 351530350318, 38276567963, 0, 0] := by
  decide +kernel

theorem rows12630 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12630 = true := by
  decide +kernel

theorem tot12630 : totK PD2M8K2 D2M8K2.t12630 = [0, 0, 0, 282939993229, 502755593407, 103147174486, 1369150432, 0] := by
  decide +kernel

theorem rows12631 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12631 = true := by
  decide +kernel

theorem tot12631 : totK PD2M8K2 D2M8K2.t12631 = [0, 0, 180029667328, 445636680476, 255627347144, 18433203757, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
