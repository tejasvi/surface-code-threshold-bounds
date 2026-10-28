import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows5388 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5388 = true := by
  decide +kernel

theorem tot5388 : totK PD2M8K2 D2M8K2.t5388 = [0, 0, 201915404993, 475517780755, 223599231053, 13867098996, 0, 0] := by
  decide +kernel

theorem rows5389 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5389 = true := by
  decide +kernel

theorem tot5389 : totK PD2M8K2 D2M8K2.t5389 = [0, 0, 194411529938, 474221846905, 220574113943, 12512770788, 0, 0] := by
  decide +kernel

theorem rows5390 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5390 = true := by
  decide +kernel

theorem tot5390 : totK PD2M8K2 D2M8K2.t5390 = [0, 0, 196130926559, 462778292245, 237269365244, 19046756399, 0, 0] := by
  decide +kernel

theorem rows5391 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t5391 = true := by
  decide +kernel

theorem tot5391 : totK PD2M8K2 D2M8K2.t5391 = [0, 0, 202737817249, 483381207061, 206383658697, 8531669623, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
