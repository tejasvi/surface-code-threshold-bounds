import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows6236 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6236 = true := by
  decide +kernel

theorem tot6236 : totK PD2M8K2 D2M8K2.t6236 = [188701150295, 466258978864, 233373438636, 16766849653, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6237 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6237 = true := by
  decide +kernel

theorem tot6237 : totK PD2M8K2 D2M8K2.t6237 = [124949412320, 436132914985, 320081904367, 36203977427, 0, 0, 0, 0] := by
  decide +kernel

theorem rows6238 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6238 = true := by
  decide +kernel

theorem tot6238 : totK PD2M8K2 D2M8K2.t6238 = [0, 174118666661, 442723642125, 259720925252, 25359060837, 0, 0, 0] := by
  decide +kernel

theorem rows6239 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t6239 = true := by
  decide +kernel

theorem tot6239 : totK PD2M8K2 D2M8K2.t6239 = [0, 165391654670, 486037250326, 239212451049, 7644965563, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
