import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15240 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15240 = true := by
  decide +kernel

theorem tot15240 : totK PD2M8K2 D2M8K2.t15240 = [0, 0, 178194951440, 449850863643, 250432192078, 15823826065, 0, 0] := by
  decide +kernel

theorem rows15241 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15241 = true := by
  decide +kernel

theorem tot15241 : totK PD2M8K2 D2M8K2.t15241 = [0, 0, 180009070954, 447643449278, 228202900783, 17104814242, 0, 0] := by
  decide +kernel

theorem rows15242 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15242 = true := by
  decide +kernel

theorem tot15242 : totK PD2M8K2 D2M8K2.t15242 = [0, 0, 37477818724, 339335075188, 439088571404, 63149986662, 1096505104, 0] := by
  decide +kernel

theorem rows15243 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15243 = true := by
  decide +kernel

theorem tot15243 : totK PD2M8K2 D2M8K2.t15243 = [0, 0, 88185535531, 396884662044, 379718874313, 33936826688, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
