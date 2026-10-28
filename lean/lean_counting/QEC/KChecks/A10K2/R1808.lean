import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7232 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7232 = true := by
  decide +kernel

theorem tot7232 : totK PA10K2 A10K2.t7232 = [0, 0, 598247720592, 2078936443161, 2024519505711, 477240266264, 13814447077, 0, 0, 0] := by
  decide +kernel

theorem rows7233 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7233 = true := by
  decide +kernel

theorem tot7233 : totK PA10K2 A10K2.t7233 = [0, 0, 531177890356, 1873713033548, 1965959487890, 615187702544, 49164041343, 0, 0, 0] := by
  decide +kernel

theorem rows7234 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7234 = true := by
  decide +kernel

theorem tot7234 : totK PA10K2 A10K2.t7234 = [0, 0, 473974092908, 1826515708783, 2109309973763, 616739966607, 33352429405, 0, 0, 0] := by
  decide +kernel

theorem rows7235 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7235 = true := by
  decide +kernel

theorem tot7235 : totK PA10K2 A10K2.t7235 = [0, 0, 0, 589024280945, 2019158976835, 1804860448500, 384927508368, 13576218110, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
