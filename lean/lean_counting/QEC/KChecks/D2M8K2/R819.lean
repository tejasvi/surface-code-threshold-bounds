import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3276 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3276 = true := by
  decide +kernel

theorem tot3276 : totK PD2M8K2 D2M8K2.t3276 = [0, 183566745301, 473811739276, 240558498172, 19333710703, 0, 0, 0] := by
  decide +kernel

theorem rows3277 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3277 = true := by
  decide +kernel

theorem tot3277 : totK PD2M8K2 D2M8K2.t3277 = [0, 171520152440, 461219759093, 242435935675, 13782265251, 0, 0, 0] := by
  decide +kernel

theorem rows3278 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3278 = true := by
  decide +kernel

theorem tot3278 : totK PD2M8K2 D2M8K2.t3278 = [0, 0, 278864283431, 500541689028, 112094751636, 1198073392, 0, 0] := by
  decide +kernel

theorem rows3279 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3279 = true := by
  decide +kernel

theorem tot3279 : totK PD2M8K2 D2M8K2.t3279 = [0, 3756869540, 190163746683, 466666373578, 192083336677, 11991925116, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
