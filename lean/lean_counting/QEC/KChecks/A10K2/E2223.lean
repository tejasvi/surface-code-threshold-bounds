import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem dfs_4_2_5_7_0 : dfsPreK PA10K2 tA10K2 [4, 2, 5, 7, 0] [] = true := by
  decide +kernel

theorem dfs_4_2_5_7_1 : dfsPreK PA10K2 tA10K2 [4, 2, 5, 7, 1] [] = true := by
  decide +kernel

theorem dfs_4_2_5_7_2 : dfsPreK PA10K2 tA10K2 [4, 2, 5, 7, 2] [] = true := by
  decide +kernel

theorem dfs_4_2_5_7_3 : dfsPreK PA10K2 tA10K2 [4, 2, 5, 7, 3] [] = true := by
  decide +kernel

theorem dfs_4_2_5_7_4 : dfsPreK PA10K2 tA10K2 [4, 2, 5, 7, 4] [] = true := by
  decide +kernel

theorem dfs_4_2_5_7_5 : dfsPreK PA10K2 tA10K2 [4, 2, 5, 7, 5] [] = true := by
  decide +kernel

theorem dfs_4_2_5_7_6 : dfsPreK PA10K2 tA10K2 [4, 2, 5, 7, 6] [] = true := by
  decide +kernel

theorem dfs_4_2_5_7_7 : dfsPreK PA10K2 tA10K2 [4, 2, 5, 7, 7] [] = true := by
  decide +kernel

end QECKChecks.A10K2
