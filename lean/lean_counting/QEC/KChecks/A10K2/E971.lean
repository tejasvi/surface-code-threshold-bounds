import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem dfs_1_7_1_3_0 : dfsPreK PA10K2 tA10K2 [1, 7, 1, 3, 0] [] = true := by
  decide +kernel

theorem dfs_1_7_1_3_1 : dfsPreK PA10K2 tA10K2 [1, 7, 1, 3, 1] [] = true := by
  decide +kernel

theorem dfs_1_7_1_3_2 : dfsPreK PA10K2 tA10K2 [1, 7, 1, 3, 2] [] = true := by
  decide +kernel

theorem dfs_1_7_1_3_3 : dfsPreK PA10K2 tA10K2 [1, 7, 1, 3, 3] [] = true := by
  decide +kernel

theorem dfs_1_7_1_3_4 : dfsPreK PA10K2 tA10K2 [1, 7, 1, 3, 4] [] = true := by
  decide +kernel

theorem dfs_1_7_1_3_5 : dfsPreK PA10K2 tA10K2 [1, 7, 1, 3, 5] [] = true := by
  decide +kernel

theorem dfs_1_7_1_3_6 : dfsPreK PA10K2 tA10K2 [1, 7, 1, 3, 6] [] = true := by
  decide +kernel

theorem dfs_1_7_1_3_7 : dfsPreK PA10K2 tA10K2 [1, 7, 1, 3, 7] [] = true := by
  decide +kernel

end QECKChecks.A10K2
