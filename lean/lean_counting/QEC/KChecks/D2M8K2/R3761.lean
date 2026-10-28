import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15044 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15044 = true := by
  decide +kernel

theorem tot15044 : totK PD2M8K2 D2M8K2.t15044 = [0, 86902333671, 350925324942, 377056398186, 78921032181, 976161439, 0, 0] := by
  decide +kernel

theorem rows15045 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15045 = true := by
  decide +kernel

theorem tot15045 : totK PD2M8K2 D2M8K2.t15045 = [0, 178588180851, 455497325704, 266750687865, 27178123400, 0, 0, 0] := by
  decide +kernel

theorem rows15046 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15046 = true := by
  decide +kernel

theorem tot15046 : totK PD2M8K2 D2M8K2.t15046 = [0, 182497872290, 474473854559, 249243666567, 13698413237, 0, 0, 0] := by
  decide +kernel

theorem rows15047 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15047 = true := by
  decide +kernel

theorem tot15047 : totK PD2M8K2 D2M8K2.t15047 = [0, 0, 271822971089, 504706936098, 123446655385, 1268739303, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
