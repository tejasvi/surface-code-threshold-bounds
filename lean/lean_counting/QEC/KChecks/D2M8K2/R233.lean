import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows932 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t932 = true := by
  decide +kernel

theorem tot932 : totK PD2M8K2 D2M8K2.t932 = [0, 212715553182, 484444063876, 182741473832, 9580924078, 0, 0, 0] := by
  decide +kernel

theorem rows933 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t933 = true := by
  decide +kernel

theorem tot933 : totK PD2M8K2 D2M8K2.t933 = [86966015402, 334101278352, 368643755610, 95660009868, 3455941720, 0, 0, 0] := by
  decide +kernel

theorem rows934 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t934 = true := by
  decide +kernel

theorem tot934 : totK PD2M8K2 D2M8K2.t934 = [170018224674, 437743693293, 276791624332, 30530391473, 0, 0, 0, 0] := by
  decide +kernel

theorem rows935 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t935 = true := by
  decide +kernel

theorem tot935 : totK PD2M8K2 D2M8K2.t935 = [141546329533, 447160959384, 287444695456, 23752615660, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
