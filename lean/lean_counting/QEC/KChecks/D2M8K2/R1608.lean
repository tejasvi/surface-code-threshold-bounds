import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6432 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6432 = true := by
  decide +kernel

theorem tot6432 : totK PD2M8K2 D2M8K2.t6432 = [0, 169719410940, 454595055541, 271247480125, 26973432871, 0, 0, 0] := by
  decide +kernel

theorem rows6433 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6433 = true := by
  decide +kernel

theorem tot6433 : totK PD2M8K2 D2M8K2.t6433 = [0, 0, 287114828551, 495376466165, 101968449500, 1198073392, 0, 0] := by
  decide +kernel

theorem rows6434 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6434 = true := by
  decide +kernel

theorem tot6434 : totK PD2M8K2 D2M8K2.t6434 = [0, 105988959550, 357805125046, 339846956668, 94017039693, 4030866388, 0, 0] := by
  decide +kernel

theorem rows6435 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6435 = true := by
  decide +kernel

theorem tot6435 : totK PD2M8K2 D2M8K2.t6435 = [0, 175332632883, 442901022014, 272073412683, 28232646136, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
