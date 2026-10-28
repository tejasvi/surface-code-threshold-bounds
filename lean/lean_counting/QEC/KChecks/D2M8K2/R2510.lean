import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows10040 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10040 = true := by
  decide +kernel

theorem tot10040 : totK PD2M8K2 D2M8K2.t10040 = [0, 0, 182232044675, 434956785062, 279690342008, 33177290790, 0, 0] := by
  decide +kernel

theorem rows10041 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10041 = true := by
  decide +kernel

theorem tot10041 : totK PD2M8K2 D2M8K2.t10041 = [0, 0, 176467387261, 475998250000, 245847022710, 12940973730, 0, 0] := by
  decide +kernel

theorem rows10042 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10042 = true := by
  decide +kernel

theorem tot10042 : totK PD2M8K2 D2M8K2.t10042 = [0, 0, 89209449686, 359461223665, 362469756554, 98852797527, 13132862920, 0] := by
  decide +kernel

theorem rows10043 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t10043 = true := by
  decide +kernel

theorem tot10043 : totK PD2M8K2 D2M8K2.t10043 = [0, 0, 0, 174042576828, 464020588164, 238180676655, 14819874722, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
