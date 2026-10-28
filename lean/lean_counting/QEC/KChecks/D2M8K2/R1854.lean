import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7416 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7416 = true := by
  decide +kernel

theorem tot7416 : totK PD2M8K2 D2M8K2.t7416 = [0, 179637077310, 452721355577, 259380435747, 19928617554, 0, 0, 0] := by
  decide +kernel

theorem rows7417 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7417 = true := by
  decide +kernel

theorem tot7417 : totK PD2M8K2 D2M8K2.t7417 = [0, 69380177453, 345229286440, 389190424721, 82536920663, 1164319620, 0, 0] := by
  decide +kernel

theorem rows7418 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7418 = true := by
  decide +kernel

theorem tot7418 : totK PD2M8K2 D2M8K2.t7418 = [0, 0, 246092613470, 488101899624, 151344832024, 9404247146, 0, 0] := by
  decide +kernel

theorem rows7419 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t7419 = true := by
  decide +kernel

theorem tot7419 : totK PD2M8K2 D2M8K2.t7419 = [0, 151752104418, 389500729512, 284559544594, 73148905003, 2481160468, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
