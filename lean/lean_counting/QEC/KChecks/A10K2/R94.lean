import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows376 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t376 = true := by
  decide +kernel

theorem tot376 : totK PA10K2 A10K2.t376 = [0, 0, 294097016330, 1517275665201, 2239299995600, 912232533364, 67009817206, 0, 0, 0] := by
  decide +kernel

theorem rows377 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t377 = true := by
  decide +kernel

theorem tot377 : totK PA10K2 A10K2.t377 = [0, 0, 326124593181, 1300453816224, 1980877251882, 1253071816166, 233707742471, 7380853412, 0, 0] := by
  decide +kernel

theorem rows378 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t378 = true := by
  decide +kernel

theorem tot378 : totK PA10K2 A10K2.t378 = [0, 0, 466574603614, 1805630123617, 2090795672255, 633984537497, 25558364319, 0, 0, 0] := by
  decide +kernel

theorem rows379 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t379 = true := by
  decide +kernel

theorem tot379 : totK PA10K2 A10K2.t379 = [0, 473630045979, 1691411610546, 1731800101354, 685984589534, 247970793918, 37674658091, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
