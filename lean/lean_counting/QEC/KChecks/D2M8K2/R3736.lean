import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows14944 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14944 = true := by
  decide +kernel

theorem tot14944 : totK PD2M8K2 D2M8K2.t14944 = [0, 205740645460, 485236285625, 213189189766, 10264426692, 0, 0, 0] := by
  decide +kernel

theorem rows14945 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14945 = true := by
  decide +kernel

theorem tot14945 : totK PD2M8K2 D2M8K2.t14945 = [0, 55986240665, 289683429272, 375116141556, 177822232444, 21400436502, 0, 0] := by
  decide +kernel

theorem rows14946 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14946 = true := by
  decide +kernel

theorem tot14946 : totK PD2M8K2 D2M8K2.t14946 = [0, 0, 202356081718, 486035705308, 204883389027, 7908366594, 0, 0] := by
  decide +kernel

theorem rows14947 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14947 = true := by
  decide +kernel

theorem tot14947 : totK PD2M8K2 D2M8K2.t14947 = [0, 67008747100, 236765170014, 400616084834, 181887833218, 8191853852, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
