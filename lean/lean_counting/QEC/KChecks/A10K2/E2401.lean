import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem dfs_4_5_4_1_0 : dfsPreK PA10K2 tA10K2 [4, 5, 4, 1, 0] [] = true := by
  decide +kernel

theorem dfs_4_5_4_1_1 : dfsPreK PA10K2 tA10K2 [4, 5, 4, 1, 1] [] = true := by
  decide +kernel

theorem dfs_4_5_4_1_2 : dfsPreK PA10K2 tA10K2 [4, 5, 4, 1, 2] [] = true := by
  decide +kernel

theorem dfs_4_5_4_1_3 : dfsPreK PA10K2 tA10K2 [4, 5, 4, 1, 3] [] = true := by
  decide +kernel

theorem dfs_4_5_4_1_4 : dfsPreK PA10K2 tA10K2 [4, 5, 4, 1, 4] [] = true := by
  decide +kernel

theorem dfs_4_5_4_1_5 : dfsPreK PA10K2 tA10K2 [4, 5, 4, 1, 5] [] = true := by
  decide +kernel

theorem dfs_4_5_4_1_6 : dfsPreK PA10K2 tA10K2 [4, 5, 4, 1, 6] [] = true := by
  decide +kernel

theorem dfs_4_5_4_1_7 : dfsPreK PA10K2 tA10K2 [4, 5, 4, 1, 7] [] = true := by
  decide +kernel

end QECKChecks.A10K2
