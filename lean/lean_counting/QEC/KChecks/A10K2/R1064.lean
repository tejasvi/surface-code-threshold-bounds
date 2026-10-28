import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows4256 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4256 = true := by
  decide +kernel

theorem tot4256 : totK PA10K2 A10K2.t4256 = [0, 527487307185, 1896872617762, 1956827334705, 517461125224, 17931077132, 0, 0, 0, 0] := by
  decide +kernel

theorem rows4257 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4257 = true := by
  decide +kernel

theorem tot4257 : totK PA10K2 A10K2.t4257 = [0, 0, 607507045442, 1985893101955, 1671489525959, 401574223861, 25333254304, 0, 0, 0] := by
  decide +kernel

theorem rows4258 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4258 = true := by
  decide +kernel

theorem tot4258 : totK PA10K2 A10K2.t4258 = [0, 291577383370, 1273307373863, 1911757335995, 1160187226292, 207302290062, 5447185874, 0, 0, 0] := by
  decide +kernel

theorem rows4259 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t4259 = true := by
  decide +kernel

theorem tot4259 : totK PA10K2 A10K2.t4259 = [0, 268130014770, 1441223718675, 2163789713480, 835826167461, 58805274416, 0, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
