import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5656 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5656 = true := by
  decide +kernel

theorem tot5656 : totK PD2M8K2 D2M8K2.t5656 = [0, 200316062866, 491928521679, 194736438624, 5336070015, 0, 0, 0] := by
  decide +kernel

theorem rows5657 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5657 = true := by
  decide +kernel

theorem tot5657 : totK PD2M8K2 D2M8K2.t5657 = [0, 176842782278, 484680873171, 214408889150, 6360151198, 0, 0, 0] := by
  decide +kernel

theorem rows5658 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5658 = true := by
  decide +kernel

theorem tot5658 : totK PD2M8K2 D2M8K2.t5658 = [0, 0, 277589250588, 498361872167, 91659472856, 1310285577, 0, 0] := by
  decide +kernel

theorem rows5659 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5659 = true := by
  decide +kernel

theorem tot5659 : totK PD2M8K2 D2M8K2.t5659 = [0, 89415162224, 385155891200, 393959745573, 44146748382, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
