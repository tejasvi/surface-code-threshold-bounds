import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1124 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1124 = true := by
  decide +kernel

theorem tot1124 : totK PD2M8K2 D2M8K2.t1124 = [0, 121773157001, 438002031923, 322124540764, 27490507705, 0, 0, 0] := by
  decide +kernel

theorem rows1125 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1125 = true := by
  decide +kernel

theorem tot1125 : totK PD2M8K2 D2M8K2.t1125 = [0, 0, 213807573044, 501384885539, 159815396338, 4880895167, 0, 0] := by
  decide +kernel

theorem rows1126 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1126 = true := by
  decide +kernel

theorem tot1126 : totK PD2M8K2 D2M8K2.t1126 = [0, 163116244108, 446875427266, 255196803399, 23154402235, 0, 0, 0] := by
  decide +kernel

theorem rows1127 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1127 = true := by
  decide +kernel

theorem tot1127 : totK PD2M8K2 D2M8K2.t1127 = [0, 195550760787, 476926093622, 218497251952, 12534051746, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
