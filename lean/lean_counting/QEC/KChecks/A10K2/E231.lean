import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem dfs_0_3_4_7_0 : dfsPreK PA10K2 tA10K2 [0, 3, 4, 7, 0] [] = true := by
  decide +kernel

theorem dfs_0_3_4_7_1 : dfsPreK PA10K2 tA10K2 [0, 3, 4, 7, 1] [] = true := by
  decide +kernel

theorem dfs_0_3_4_7_2 : dfsPreK PA10K2 tA10K2 [0, 3, 4, 7, 2] [] = true := by
  decide +kernel

theorem dfs_0_3_4_7_3 : dfsPreK PA10K2 tA10K2 [0, 3, 4, 7, 3] [] = true := by
  decide +kernel

theorem dfs_0_3_4_7_4 : dfsPreK PA10K2 tA10K2 [0, 3, 4, 7, 4] [] = true := by
  decide +kernel

theorem dfs_0_3_4_7_5 : dfsPreK PA10K2 tA10K2 [0, 3, 4, 7, 5] [] = true := by
  decide +kernel

theorem dfs_0_3_4_7_6 : dfsPreK PA10K2 tA10K2 [0, 3, 4, 7, 6] [] = true := by
  decide +kernel

theorem dfs_0_3_4_7_7 : dfsPreK PA10K2 tA10K2 [0, 3, 4, 7, 7] [] = true := by
  decide +kernel

end QECKChecks.A10K2
