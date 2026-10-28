import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows11452 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11452 = true := by
  decide +kernel

theorem tot11452 : totK PD2M8K2 D2M8K2.t11452 = [0, 0, 165074381875, 453494331647, 271386792141, 28488717195, 0, 0] := by
  decide +kernel

theorem rows11453 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11453 = true := by
  decide +kernel

theorem tot11453 : totK PD2M8K2 D2M8K2.t11453 = [0, 0, 187397715903, 483805324137, 213873722487, 6491593854, 0, 0] := by
  decide +kernel

theorem rows11454 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11454 = true := by
  decide +kernel

theorem tot11454 : totK PD2M8K2 D2M8K2.t11454 = [0, 0, 170158766577, 456698825994, 246149050760, 21383138092, 0, 0] := by
  decide +kernel

theorem rows11455 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t11455 = true := by
  decide +kernel

theorem tot11455 : totK PD2M8K2 D2M8K2.t11455 = [0, 0, 179033216875, 466697029557, 235846040405, 13761953177, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
