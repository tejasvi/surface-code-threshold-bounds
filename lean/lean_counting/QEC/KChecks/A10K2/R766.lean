import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3064 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3064 = true := by
  decide +kernel

theorem tot3064 : totK PA10K2 A10K2.t3064 = [0, 0, 466005079570, 1835056383574, 2058017435072, 637659828055, 25177607156, 0, 0, 0] := by
  decide +kernel

theorem rows3065 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3065 = true := by
  decide +kernel

theorem tot3065 : totK PA10K2 A10K2.t3065 = [0, 0, 0, 613582109227, 2019687403197, 1848024293682, 377726822792, 12224107035, 0, 0] := by
  decide +kernel

theorem rows3066 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3066 = true := by
  decide +kernel

theorem tot3066 : totK PA10K2 A10K2.t3066 = [0, 0, 211556496991, 883148075506, 1611480320541, 1602447839957, 576212275274, 48886019071, 0, 0] := by
  decide +kernel

theorem rows3067 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3067 = true := by
  decide +kernel

theorem tot3067 : totK PA10K2 A10K2.t3067 = [0, 0, 490883207570, 1784489087925, 1926654152887, 549286939743, 32731286466, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
