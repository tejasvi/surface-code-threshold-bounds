import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3176 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3176 = true := by
  decide +kernel

theorem tot3176 : totK PD2M8K2 D2M8K2.t3176 = [0, 235771827624, 503354532528, 162354102931, 5768874209, 0, 0, 0] := by
  decide +kernel

theorem rows3177 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3177 = true := by
  decide +kernel

theorem tot3177 : totK PD2M8K2 D2M8K2.t3177 = [69131323710, 268307983207, 399682313982, 136341375953, 7481811052, 0, 0, 0] := by
  decide +kernel

theorem rows3178 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3178 = true := by
  decide +kernel

theorem tot3178 : totK PD2M8K2 D2M8K2.t3178 = [166411097073, 453059066669, 254477798237, 23142137017, 0, 0, 0, 0] := by
  decide +kernel

theorem rows3179 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t3179 = true := by
  decide +kernel

theorem tot3179 : totK PD2M8K2 D2M8K2.t3179 = [180567783026, 457987658098, 245017148338, 17995366712, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
