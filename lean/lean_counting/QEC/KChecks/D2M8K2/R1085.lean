import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4340 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4340 = true := by
  decide +kernel

theorem tot4340 : totK PD2M8K2 D2M8K2.t4340 = [0, 0, 164703726374, 384815823189, 250702035345, 107772686397, 6804944647, 0] := by
  decide +kernel

theorem rows4341 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4341 = true := by
  decide +kernel

theorem tot4341 : totK PD2M8K2 D2M8K2.t4341 = [0, 0, 170296612972, 449164328959, 256793950966, 19363682577, 0, 0] := by
  decide +kernel

theorem rows4342 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4342 = true := by
  decide +kernel

theorem tot4342 : totK PD2M8K2 D2M8K2.t4342 = [0, 0, 78537910171, 361720131416, 408715569019, 67198761084, 0, 0] := by
  decide +kernel

theorem rows4343 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4343 = true := by
  decide +kernel

theorem tot4343 : totK PD2M8K2 D2M8K2.t4343 = [0, 0, 0, 215483721519, 485945179701, 169708584440, 6581970177, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
