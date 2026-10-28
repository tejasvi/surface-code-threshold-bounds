import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7244 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7244 = true := by
  decide +kernel

theorem tot7244 : totK PA10K2 A10K2.t7244 = [0, 330854518425, 1569652369974, 2200598504363, 881770617587, 70597248720, 0, 0, 0, 0] := by
  decide +kernel

theorem rows7245 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7245 = true := by
  decide +kernel

theorem tot7245 : totK PA10K2 A10K2.t7245 = [0, 0, 508830922790, 1972739225665, 2026128868099, 459631711003, 13816090359, 0, 0, 0] := by
  decide +kernel

theorem rows7246 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7246 = true := by
  decide +kernel

theorem tot7246 : totK PA10K2 A10K2.t7246 = [0, 0, 629900304297, 1943500509885, 1807606441404, 565746666871, 49180423016, 0, 0, 0] := by
  decide +kernel

theorem rows7247 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7247 = true := by
  decide +kernel

theorem tot7247 : totK PA10K2 A10K2.t7247 = [0, 0, 476236816663, 1849199245665, 1990434348638, 544964813795, 31010298977, 0, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
