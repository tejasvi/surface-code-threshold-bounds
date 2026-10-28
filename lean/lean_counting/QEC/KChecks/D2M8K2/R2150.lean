import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows8600 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8600 = true := by
  decide +kernel

theorem tot8600 : totK PD2M8K2 D2M8K2.t8600 = [176205413550, 462954569179, 250243496758, 17829946705, 0, 0, 0, 0] := by
  decide +kernel

theorem rows8601 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8601 = true := by
  decide +kernel

theorem tot8601 : totK PD2M8K2 D2M8K2.t8601 = [73215069665, 349545343093, 369775738581, 110944442201, 13135967731, 0, 0, 0] := by
  decide +kernel

theorem rows8602 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8602 = true := by
  decide +kernel

theorem tot8602 : totK PD2M8K2 D2M8K2.t8602 = [0, 172571399822, 455070985583, 245595575594, 15110570837, 0, 0, 0] := by
  decide +kernel

theorem rows8603 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t8603 = true := by
  decide +kernel

theorem tot8603 : totK PD2M8K2 D2M8K2.t8603 = [35250516920, 212614316847, 433903155073, 208931908664, 9355169654, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
