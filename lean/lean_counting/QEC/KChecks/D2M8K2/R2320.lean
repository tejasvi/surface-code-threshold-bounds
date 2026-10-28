import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows9280 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9280 = true := by
  decide +kernel

theorem tot9280 : totK PD2M8K2 D2M8K2.t9280 = [0, 171545254961, 462646442480, 249437260015, 16014116729, 0, 0, 0] := by
  decide +kernel

theorem rows9281 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9281 = true := by
  decide +kernel

theorem tot9281 : totK PD2M8K2 D2M8K2.t9281 = [0, 0, 276208258333, 492710766850, 109911351658, 1171084559, 0, 0] := by
  decide +kernel

theorem rows9282 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9282 = true := by
  decide +kernel

theorem tot9282 : totK PD2M8K2 D2M8K2.t9282 = [0, 52161388308, 227856744526, 393067304818, 170303307723, 11934365838, 0, 0] := by
  decide +kernel

theorem rows9283 : KTree.allE (rowCheckK PD2M8K2 tD2M8K2) D2M8K2.t9283 = true := by
  decide +kernel

theorem tot9283 : totK PD2M8K2 D2M8K2.t9283 = [0, 189703917344, 488450437184, 215213254503, 11071105621, 0, 0, 0] := by
  decide +kernel

end QECKChecks.D2M8K2
