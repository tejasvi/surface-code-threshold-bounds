import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem dfs_0_0_1_5_0 : dfsPreK PA10K2 tA10K2 [0, 0, 1, 5, 0] [] = true := by
  decide +kernel

theorem dfs_0_0_1_5_1 : dfsPreK PA10K2 tA10K2 [0, 0, 1, 5, 1] [] = true := by
  decide +kernel

theorem dfs_0_0_1_5_2 : dfsPreK PA10K2 tA10K2 [0, 0, 1, 5, 2] [] = true := by
  decide +kernel

theorem dfs_0_0_1_5_3 : dfsPreK PA10K2 tA10K2 [0, 0, 1, 5, 3] [] = true := by
  decide +kernel

theorem dfs_0_0_1_5_4 : dfsPreK PA10K2 tA10K2 [0, 0, 1, 5, 4] [] = true := by
  decide +kernel

theorem dfs_0_0_1_5_5 : dfsPreK PA10K2 tA10K2 [0, 0, 1, 5, 5] [] = true := by
  decide +kernel

theorem dfs_0_0_1_5_6 : dfsPreK PA10K2 tA10K2 [0, 0, 1, 5, 6] [] = true := by
  decide +kernel

theorem dfs_0_0_1_5_7 : dfsPreK PA10K2 tA10K2 [0, 0, 1, 5, 7] [] = true := by
  decide +kernel

end QECKChecks.A10K2
