import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3488 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3488 = true := by
  decide +kernel

theorem tot3488 : totK PD2M8K2 D2M8K2.t3488 = [103540504535, 411701304215, 352348911234, 39324780197, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3489 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3489 = true := by
  decide +kernel

theorem tot3489 : totK PD2M8K2 D2M8K2.t3489 = [0, 230381759675, 490096119340, 168892096564, 4967996017, 0, 0, 0] := by
  decide +kernel

theorem rows3490 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3490 = true := by
  decide +kernel

theorem tot3490 : totK PD2M8K2 D2M8K2.t3490 = [0, 195701174423, 468272378614, 211624977552, 14596453775, 0, 0, 0] := by
  decide +kernel

theorem rows3491 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3491 = true := by
  decide +kernel

theorem tot3491 : totK PD2M8K2 D2M8K2.t3491 = [0, 153156054757, 450790657163, 235608233510, 13450165506, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
