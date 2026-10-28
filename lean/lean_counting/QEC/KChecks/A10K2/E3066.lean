import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem dfs_5_7_7_2_0 : dfsPreK PA10K2 tA10K2 [5, 7, 7, 2, 0] [] = true := by
  decide +kernel

theorem dfs_5_7_7_2_1 : dfsPreK PA10K2 tA10K2 [5, 7, 7, 2, 1] [] = true := by
  decide +kernel

theorem dfs_5_7_7_2_2 : dfsPreK PA10K2 tA10K2 [5, 7, 7, 2, 2] [] = true := by
  decide +kernel

theorem dfs_5_7_7_2_3 : dfsPreK PA10K2 tA10K2 [5, 7, 7, 2, 3] [] = true := by
  decide +kernel

theorem dfs_5_7_7_2_4 : dfsPreK PA10K2 tA10K2 [5, 7, 7, 2, 4] [] = true := by
  decide +kernel

theorem dfs_5_7_7_2_5 : dfsPreK PA10K2 tA10K2 [5, 7, 7, 2, 5] [] = true := by
  decide +kernel

theorem dfs_5_7_7_2_6 : dfsPreK PA10K2 tA10K2 [5, 7, 7, 2, 6] [] = true := by
  decide +kernel

theorem dfs_5_7_7_2_7 : dfsPreK PA10K2 tA10K2 [5, 7, 7, 2, 7] [] = true := by
  decide +kernel

end QECKChecks.A10K2
