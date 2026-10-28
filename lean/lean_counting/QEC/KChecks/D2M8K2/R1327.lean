import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5308 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5308 = true := by
  decide +kernel

theorem tot5308 : totK PD2M8K2 D2M8K2.t5308 = [0, 18872627066, 189117995994, 437697007129, 244620268357, 17476474534, 0, 0] := by
  decide +kernel

theorem rows5309 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5309 = true := by
  decide +kernel

theorem tot5309 : totK PD2M8K2 D2M8K2.t5309 = [0, 209242660012, 485179779284, 189844097446, 5615140248, 0, 0, 0] := by
  decide +kernel

theorem rows5310 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5310 = true := by
  decide +kernel

theorem tot5310 : totK PD2M8K2 D2M8K2.t5310 = [0, 150799174962, 451869915418, 274007007972, 17913639477, 0, 0, 0] := by
  decide +kernel

theorem rows5311 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5311 = true := by
  decide +kernel

theorem tot5311 : totK PD2M8K2 D2M8K2.t5311 = [0, 0, 275558916343, 506901777518, 105871922807, 1369150432, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
