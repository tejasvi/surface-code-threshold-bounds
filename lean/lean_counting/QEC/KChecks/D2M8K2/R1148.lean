import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4592 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4592 = true := by
  decide +kernel

theorem tot4592 : totK PD2M8K2 D2M8K2.t4592 = [0, 0, 0, 213222601948, 485748682589, 164874586140, 3368360898, 0] := by
  decide +kernel

theorem rows4593 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4593 = true := by
  decide +kernel

theorem tot4593 : totK PD2M8K2 D2M8K2.t4593 = [0, 0, 0, 193661800274, 456755422096, 238383623867, 20001318118, 0] := by
  decide +kernel

theorem rows4594 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4594 = true := by
  decide +kernel

theorem tot4594 : totK PD2M8K2 D2M8K2.t4594 = [0, 0, 0, 211615905374, 493808890561, 179039488490, 8823588495, 0] := by
  decide +kernel

theorem rows4595 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t4595 = true := by
  decide +kernel

theorem tot4595 : totK PD2M8K2 D2M8K2.t4595 = [0, 0, 0, 195360054028, 469959741381, 221519883700, 16063424123, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
