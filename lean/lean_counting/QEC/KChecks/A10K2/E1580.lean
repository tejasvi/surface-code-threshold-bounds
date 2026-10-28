import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem dfs_3_0_5_4_0 : dfsPreK PA10K2 tA10K2 [3, 0, 5, 4, 0] [] = true := by
  decide +kernel

theorem dfs_3_0_5_4_1 : dfsPreK PA10K2 tA10K2 [3, 0, 5, 4, 1] [] = true := by
  decide +kernel

theorem dfs_3_0_5_4_2 : dfsPreK PA10K2 tA10K2 [3, 0, 5, 4, 2] [] = true := by
  decide +kernel

theorem dfs_3_0_5_4_3 : dfsPreK PA10K2 tA10K2 [3, 0, 5, 4, 3] [] = true := by
  decide +kernel

theorem dfs_3_0_5_4_4 : dfsPreK PA10K2 tA10K2 [3, 0, 5, 4, 4] [] = true := by
  decide +kernel

theorem dfs_3_0_5_4_5 : dfsPreK PA10K2 tA10K2 [3, 0, 5, 4, 5] [] = true := by
  decide +kernel

theorem dfs_3_0_5_4_6 : dfsPreK PA10K2 tA10K2 [3, 0, 5, 4, 6] [] = true := by
  decide +kernel

theorem dfs_3_0_5_4_7 : dfsPreK PA10K2 tA10K2 [3, 0, 5, 4, 7] [] = true := by
  decide +kernel

end QECKChecks.A10K2
