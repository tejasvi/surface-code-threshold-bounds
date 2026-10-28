import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6456 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6456 = true := by
  decide +kernel

theorem tot6456 : totK PD2M8K2 D2M8K2.t6456 = [76459986009, 338642067726, 399288750316, 87217385657, 1268739303, 0, 0, 0] := by
  decide +kernel

theorem rows6457 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6457 = true := by
  decide +kernel

theorem tot6457 : totK PD2M8K2 D2M8K2.t6457 = [0, 205761173989, 480521464963, 182506215035, 7442000727, 0, 0, 0] := by
  decide +kernel

theorem rows6458 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6458 = true := by
  decide +kernel

theorem tot6458 : totK PD2M8K2 D2M8K2.t6458 = [0, 178379215039, 463036311610, 231548705248, 15860424110, 0, 0, 0] := by
  decide +kernel

theorem rows6459 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6459 = true := by
  decide +kernel

theorem tot6459 : totK PD2M8K2 D2M8K2.t6459 = [0, 170984783077, 452704465268, 219947303140, 16561712910, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
