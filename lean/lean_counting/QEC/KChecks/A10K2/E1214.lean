import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem dfs_2_2_7_6_0 : dfsPreK PA10K2 tA10K2 [2, 2, 7, 6, 0] [] = true := by
  decide +kernel

theorem dfs_2_2_7_6_1 : dfsPreK PA10K2 tA10K2 [2, 2, 7, 6, 1] [] = true := by
  decide +kernel

theorem dfs_2_2_7_6_2 : dfsPreK PA10K2 tA10K2 [2, 2, 7, 6, 2] [] = true := by
  decide +kernel

theorem dfs_2_2_7_6_3 : dfsPreK PA10K2 tA10K2 [2, 2, 7, 6, 3] [] = true := by
  decide +kernel

theorem dfs_2_2_7_6_4 : dfsPreK PA10K2 tA10K2 [2, 2, 7, 6, 4] [] = true := by
  decide +kernel

theorem dfs_2_2_7_6_5 : dfsPreK PA10K2 tA10K2 [2, 2, 7, 6, 5] [] = true := by
  decide +kernel

theorem dfs_2_2_7_6_6 : dfsPreK PA10K2 tA10K2 [2, 2, 7, 6, 6] [] = true := by
  decide +kernel

theorem dfs_2_2_7_6_7 : dfsPreK PA10K2 tA10K2 [2, 2, 7, 6, 7] [] = true := by
  decide +kernel

end QECKChecks.A10K2
