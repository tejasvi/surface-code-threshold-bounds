import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6144 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6144 = true := by
  decide +kernel

theorem tot6144 : totK PD2M8K2 D2M8K2.t6144 = [0, 155505132346, 453623631173, 252127462864, 18471174381, 0, 0, 0] := by
  decide +kernel

theorem rows6145 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6145 = true := by
  decide +kernel

theorem tot6145 : totK PD2M8K2 D2M8K2.t6145 = [0, 0, 284385816437, 458063333013, 106685806223, 1369150432, 0, 0] := by
  decide +kernel

theorem rows6146 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6146 = true := by
  decide +kernel

theorem tot6146 : totK PD2M8K2 D2M8K2.t6146 = [0, 160250810744, 452699384220, 262915829028, 22695287968, 0, 0, 0] := by
  decide +kernel

theorem rows6147 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6147 = true := by
  decide +kernel

theorem tot6147 : totK PD2M8K2 D2M8K2.t6147 = [0, 177727555137, 460218969022, 233356847326, 13629821414, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
