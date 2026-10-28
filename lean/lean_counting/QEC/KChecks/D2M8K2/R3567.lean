import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14268 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14268 = true := by
  decide +kernel

theorem tot14268 : totK PD2M8K2 D2M8K2.t14268 = [81358316749, 331291141026, 376140875818, 94639752981, 3460111309, 0, 0, 0] := by
  decide +kernel

theorem rows14269 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14269 = true := by
  decide +kernel

theorem tot14269 : totK PD2M8K2 D2M8K2.t14269 = [174522329621, 457255267327, 271811525911, 27696829117, 0, 0, 0, 0] := by
  decide +kernel

theorem rows14270 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14270 = true := by
  decide +kernel

theorem tot14270 : totK PD2M8K2 D2M8K2.t14270 = [89659383061, 350414537199, 381393384395, 82303778923, 1198073392, 0, 0, 0] := by
  decide +kernel

theorem rows14271 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14271 = true := by
  decide +kernel

theorem tot14271 : totK PD2M8K2 D2M8K2.t14271 = [18567060971, 257722896397, 474444748761, 154359489762, 8351094376, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
