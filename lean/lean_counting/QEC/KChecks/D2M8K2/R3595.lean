import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14380 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14380 = true := by
  decide +kernel

theorem tot14380 : totK PD2M8K2 D2M8K2.t14380 = [0, 116824446283, 423637624763, 307344943766, 29376173512, 0, 0, 0] := by
  decide +kernel

theorem rows14381 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14381 = true := by
  decide +kernel

theorem tot14381 : totK PD2M8K2 D2M8K2.t14381 = [0, 0, 279808249495, 503695111964, 97047250823, 1310166938, 0, 0] := by
  decide +kernel

theorem rows14382 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14382 = true := by
  decide +kernel

theorem tot14382 : totK PD2M8K2 D2M8K2.t14382 = [0, 179905146354, 439051199205, 275941890987, 29527035419, 0, 0, 0] := by
  decide +kernel

theorem rows14383 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14383 = true := by
  decide +kernel

theorem tot14383 : totK PD2M8K2 D2M8K2.t14383 = [0, 175914738093, 462210719100, 249875940519, 18373209281, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
