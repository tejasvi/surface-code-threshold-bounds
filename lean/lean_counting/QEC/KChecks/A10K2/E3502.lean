import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem dfs_6_6_5_6_0 : dfsPreK PA10K2 tA10K2 [6, 6, 5, 6, 0] [] = true := by
  decide +kernel

theorem dfs_6_6_5_6_1 : dfsPreK PA10K2 tA10K2 [6, 6, 5, 6, 1] [] = true := by
  decide +kernel

theorem dfs_6_6_5_6_2 : dfsPreK PA10K2 tA10K2 [6, 6, 5, 6, 2] [] = true := by
  decide +kernel

theorem dfs_6_6_5_6_3 : dfsPreK PA10K2 tA10K2 [6, 6, 5, 6, 3] [] = true := by
  decide +kernel

theorem dfs_6_6_5_6_4 : dfsPreK PA10K2 tA10K2 [6, 6, 5, 6, 4] [] = true := by
  decide +kernel

theorem dfs_6_6_5_6_5 : dfsPreK PA10K2 tA10K2 [6, 6, 5, 6, 5] [] = true := by
  decide +kernel

theorem dfs_6_6_5_6_6 : dfsPreK PA10K2 tA10K2 [6, 6, 5, 6, 6] [] = true := by
  decide +kernel

theorem dfs_6_6_5_6_7 : dfsPreK PA10K2 tA10K2 [6, 6, 5, 6, 7] [] = true := by
  decide +kernel

end QECKChecks.A10K2
