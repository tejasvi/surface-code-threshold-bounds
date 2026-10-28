import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15364 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15364 = true := by
  decide +kernel

theorem tot15364 : totK PD2M8K2 D2M8K2.t15364 = [0, 0, 123001750377, 442325016186, 308792054558, 20303287946, 0, 0] := by
  decide +kernel

theorem rows15365 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15365 = true := by
  decide +kernel

theorem tot15365 : totK PD2M8K2 D2M8K2.t15365 = [0, 0, 0, 310289784783, 526116983072, 69853989143, 0, 0] := by
  decide +kernel

theorem rows15366 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15366 = true := by
  decide +kernel

theorem tot15366 : totK PD2M8K2 D2M8K2.t15366 = [0, 0, 161704990643, 408320625162, 286484594666, 64259696492, 1415142070, 0] := by
  decide +kernel

theorem rows15367 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15367 = true := by
  decide +kernel

theorem tot15367 : totK PD2M8K2 D2M8K2.t15367 = [0, 0, 186539269510, 468169082031, 231519036086, 13286264144, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
