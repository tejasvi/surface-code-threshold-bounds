import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows3212 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3212 = true := by
  decide +kernel

theorem tot3212 : totK PA10K2 A10K2.t3212 = [0, 0, 509620454389, 1828571088665, 1974981822891, 673613199283, 56143165367, 0, 0, 0] := by
  decide +kernel

theorem rows3213 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3213 = true := by
  decide +kernel

theorem tot3213 : totK PA10K2 A10K2.t3213 = [0, 0, 288405974479, 1462284124732, 2248037106426, 1029183257929, 89693153093, 0, 0, 0] := by
  decide +kernel

theorem rows3214 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3214 = true := by
  decide +kernel

theorem tot3214 : totK PA10K2 A10K2.t3214 = [0, 0, 312057137912, 1413103286475, 2065650298534, 1081700672345, 117382561570, 0, 0, 0] := by
  decide +kernel

theorem rows3215 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t3215 = true := by
  decide +kernel

theorem tot3215 : totK PA10K2 A10K2.t3215 = [0, 0, 505017398559, 1867397920496, 2036144986206, 563927919875, 16776689649, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
