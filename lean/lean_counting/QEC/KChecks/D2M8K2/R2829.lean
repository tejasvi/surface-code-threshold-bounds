import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11316 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11316 = true := by
  decide +kernel

theorem tot11316 : totK PD2M8K2 D2M8K2.t11316 = [0, 173124426782, 458100513334, 238729662525, 15884393502, 0, 0, 0] := by
  decide +kernel

theorem rows11317 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11317 = true := by
  decide +kernel

theorem tot11317 : totK PD2M8K2 D2M8K2.t11317 = [0, 0, 275812584387, 491927821916, 111466948443, 1171084559, 0, 0] := by
  decide +kernel

theorem rows11318 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11318 = true := by
  decide +kernel

theorem tot11318 : totK PD2M8K2 D2M8K2.t11318 = [0, 49032113723, 232760648045, 389327523830, 168476896078, 11934365838, 0, 0] := by
  decide +kernel

theorem rows11319 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11319 = true := by
  decide +kernel

theorem tot11319 : totK PD2M8K2 D2M8K2.t11319 = [0, 184580542580, 478638782551, 231108867037, 12080346885, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
