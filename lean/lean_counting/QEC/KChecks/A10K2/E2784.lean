import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem dfs_5_3_4_0_0 : dfsPreK PA10K2 tA10K2 [5, 3, 4, 0, 0] [] = true := by
  decide +kernel

theorem dfs_5_3_4_0_1 : dfsPreK PA10K2 tA10K2 [5, 3, 4, 0, 1] [] = true := by
  decide +kernel

theorem dfs_5_3_4_0_2 : dfsPreK PA10K2 tA10K2 [5, 3, 4, 0, 2] [] = true := by
  decide +kernel

theorem dfs_5_3_4_0_3 : dfsPreK PA10K2 tA10K2 [5, 3, 4, 0, 3] [] = true := by
  decide +kernel

theorem dfs_5_3_4_0_4 : dfsPreK PA10K2 tA10K2 [5, 3, 4, 0, 4] [] = true := by
  decide +kernel

theorem dfs_5_3_4_0_5 : dfsPreK PA10K2 tA10K2 [5, 3, 4, 0, 5] [] = true := by
  decide +kernel

theorem dfs_5_3_4_0_6 : dfsPreK PA10K2 tA10K2 [5, 3, 4, 0, 6] [] = true := by
  decide +kernel

theorem dfs_5_3_4_0_7 : dfsPreK PA10K2 tA10K2 [5, 3, 4, 0, 7] [] = true := by
  decide +kernel

end QECKChecks.A10K2
