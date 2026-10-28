import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows12 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t12 = true := by
  decide +kernel

theorem tot12 : totK PD2M8K2 D2M8K2.t12 = [155064788974, 441121086887, 284129494385, 31081692956, 0, 0, 0, 0] := by
  decide +kernel

theorem rows13 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t13 = true := by
  decide +kernel

theorem tot13 : totK PD2M8K2 D2M8K2.t13 = [186032461199, 453741243117, 233857743413, 17104814242, 0, 0, 0, 0] := by
  decide +kernel

theorem rows14 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t14 = true := by
  decide +kernel

theorem tot14 : totK PD2M8K2 D2M8K2.t14 = [73451219382, 355216574202, 385946954184, 74905405855, 1096505104, 0, 0, 0] := by
  decide +kernel

theorem rows15 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15 = true := by
  decide +kernel

theorem tot15 : totK PD2M8K2 D2M8K2.t15 = [0, 275026203151, 514562235199, 109651021218, 1069412848, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
