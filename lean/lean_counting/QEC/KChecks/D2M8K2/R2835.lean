import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11340 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11340 = true := by
  decide +kernel

theorem tot11340 : totK PD2M8K2 D2M8K2.t11340 = [82494396464, 331628390833, 369044127606, 100200603933, 3581949829, 0, 0, 0] := by
  decide +kernel

theorem rows11341 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11341 = true := by
  decide +kernel

theorem tot11341 : totK PD2M8K2 D2M8K2.t11341 = [176990743926, 452518801863, 268106930899, 27881952543, 0, 0, 0, 0] := by
  decide +kernel

theorem rows11342 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11342 = true := by
  decide +kernel

theorem tot11342 : totK PD2M8K2 D2M8K2.t11342 = [180183318095, 472976665645, 241439042032, 13262355368, 0, 0, 0, 0] := by
  decide +kernel

theorem rows11343 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11343 = true := by
  decide +kernel

theorem tot11343 : totK PD2M8K2 D2M8K2.t11343 = [0, 292024701281, 514507502367, 98429347501, 1096505104, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
