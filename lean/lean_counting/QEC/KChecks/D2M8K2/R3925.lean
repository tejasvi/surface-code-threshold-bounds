import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows15700 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15700 = true := by
  decide +kernel

theorem tot15700 : totK PD2M8K2 D2M8K2.t15700 = [0, 0, 0, 225339744952, 507522197832, 149941370523, 2448800629, 0] := by
  decide +kernel

theorem rows15701 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15701 = true := by
  decide +kernel

theorem tot15701 : totK PD2M8K2 D2M8K2.t15701 = [0, 0, 0, 221996077751, 483834667125, 178884884800, 6170241507, 0] := by
  decide +kernel

theorem rows15702 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15702 = true := by
  decide +kernel

theorem tot15702 : totK PD2M8K2 D2M8K2.t15702 = [0, 0, 183175457280, 419971406020, 265931917786, 59297008884, 6594335571, 0] := by
  decide +kernel

theorem rows15703 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t15703 = true := by
  decide +kernel

theorem tot15703 : totK PD2M8K2 D2M8K2.t15703 = [0, 0, 168068806673, 472631058491, 250380732856, 13471501968, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
