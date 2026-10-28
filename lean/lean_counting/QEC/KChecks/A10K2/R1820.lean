import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem rows7280 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7280 = true := by
  decide +kernel

theorem tot7280 : totK PA10K2 A10K2.t7280 = [0, 0, 0, 575581596014, 1980247795968, 1804650852264, 387648821303, 11991740650, 0, 0] := by
  decide +kernel

theorem rows7281 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7281 = true := by
  decide +kernel

theorem tot7281 : totK PA10K2 A10K2.t7281 = [0, 0, 459159501540, 1703353488521, 2076302368037, 808538432387, 68939973848, 0, 0, 0] := by
  decide +kernel

theorem rows7282 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7282 = true := by
  decide +kernel

theorem tot7282 : totK PA10K2 A10K2.t7282 = [0, 0, 226222707868, 1293640895186, 2207655296707, 1223353660741, 134954749915, 0, 0, 0] := by
  decide +kernel

theorem rows7283 : KTree.allE (rowCheckK PA10K2 tA10K2) A10K2.t7283 = true := by
  decide +kernel

theorem tot7283 : totK PA10K2 A10K2.t7283 = [0, 0, 281717535487, 1235676519086, 1936656834583, 1317981527284, 278280674439, 12219140272, 0, 0] := by
  decide +kernel

end QECKChecks.A10K2
