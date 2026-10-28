import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4432 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4432 = true := by
  decide +kernel

theorem tot4432 : totK PD2M8K2 D2M8K2.t4432 = [0, 178061206061, 417439111415, 165322585801, 58298037549, 71937841186, 6818291842, 0] := by
  decide +kernel

theorem rows4433 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4433 = true := by
  decide +kernel

theorem tot4433 : totK PD2M8K2 D2M8K2.t4433 = [0, 188630229194, 459305382951, 211583768912, 10098179496, 0, 0, 0] := by
  decide +kernel

theorem rows4434 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4434 = true := by
  decide +kernel

theorem tot4434 : totK PD2M8K2 D2M8K2.t4434 = [0, 27694058175, 309752194570, 452640366095, 91859545962, 1369150432, 0, 0] := by
  decide +kernel

theorem rows4435 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4435 = true := by
  decide +kernel

theorem tot4435 : totK PD2M8K2 D2M8K2.t4435 = [0, 93301704879, 378548483680, 394817044791, 42100006600, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
