import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3420 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3420 = true := by
  decide +kernel

theorem tot3420 : totK PD2M8K2 D2M8K2.t3420 = [0, 176345943235, 486670755734, 214598510217, 7600300831, 0, 0, 0] := by
  decide +kernel

theorem rows3421 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3421 = true := by
  decide +kernel

theorem tot3421 : totK PD2M8K2 D2M8K2.t3421 = [0, 172025135532, 456564970729, 217105600401, 15367806931, 0, 0, 0] := by
  decide +kernel

theorem rows3422 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3422 = true := by
  decide +kernel

theorem tot3422 : totK PD2M8K2 D2M8K2.t3422 = [0, 71745490359, 316081993421, 384735752235, 92055440925, 1369150432, 0, 0] := by
  decide +kernel

theorem rows3423 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3423 = true := by
  decide +kernel

theorem tot3423 : totK PD2M8K2 D2M8K2.t3423 = [0, 50826171624, 356452763341, 397536066399, 53345994976, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
