import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15524 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15524 = true := by
  decide +kernel

theorem tot15524 : totK PD2M8K2 D2M8K2.t15524 = [0, 0, 87476419814, 356291795170, 350878014103, 74836659476, 1369150432, 0] := by
  decide +kernel

theorem rows15525 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15525 = true := by
  decide +kernel

theorem tot15525 : totK PD2M8K2 D2M8K2.t15525 = [0, 0, 7564999111, 334793532729, 447781772714, 60359098588, 0, 0] := by
  decide +kernel

theorem rows15526 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15526 = true := by
  decide +kernel

theorem tot15526 : totK PD2M8K2 D2M8K2.t15526 = [0, 0, 215315895432, 494461165019, 191538663355, 5463989431, 0, 0] := by
  decide +kernel

theorem rows15527 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15527 = true := by
  decide +kernel

theorem tot15527 : totK PD2M8K2 D2M8K2.t15527 = [0, 0, 188050142853, 461264072087, 207544132279, 12243442891, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
