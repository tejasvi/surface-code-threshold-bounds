import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows1108 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1108 = true := by
  decide +kernel

theorem tot1108 : totK PD2M8K2 D2M8K2.t1108 = [0, 151995866805, 452035648072, 252036206798, 18126906772, 0, 0, 0] := by
  decide +kernel

theorem rows1109 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1109 = true := by
  decide +kernel

theorem tot1109 : totK PD2M8K2 D2M8K2.t1109 = [0, 78825086634, 336060834570, 384394088376, 80069374578, 1310166938, 0, 0] := by
  decide +kernel

theorem rows1110 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1110 = true := by
  decide +kernel

theorem tot1110 : totK PD2M8K2 D2M8K2.t1110 = [0, 38603867747, 348730875963, 469727881791, 52838857690, 0, 0, 0] := by
  decide +kernel

theorem rows1111 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t1111 = true := by
  decide +kernel

theorem tot1111 : totK PD2M8K2 D2M8K2.t1111 = [0, 159653054575, 437215413969, 281331641846, 30376266838, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
