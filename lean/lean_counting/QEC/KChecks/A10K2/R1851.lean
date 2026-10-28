import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7404 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7404 = true := by
  decide +kernel

theorem tot7404 : totK PA10K2 A10K2.t7404 = [0, 0, 480625918787, 1853998892304, 2100644281231, 668569224071, 32311983079, 0, 0, 0] := by
  decide +kernel

theorem rows7405 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7405 = true := by
  decide +kernel

theorem tot7405 : totK PA10K2 A10K2.t7405 = [0, 0, 0, 587698371342, 2089562141911, 2035706890595, 439795008038, 13548089516, 0, 0] := by
  decide +kernel

theorem rows7406 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7406 = true := by
  decide +kernel

theorem tot7406 : totK PA10K2 A10K2.t7406 = [0, 0, 0, 624371376459, 1947882780152, 1858919764514, 593897051022, 49164041343, 0, 0] := by
  decide +kernel

theorem rows7407 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7407 = true := by
  decide +kernel

theorem tot7407 : totK PA10K2 A10K2.t7407 = [0, 0, 0, 473475863094, 1887907810932, 2141148912431, 590781858133, 20478153604, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
