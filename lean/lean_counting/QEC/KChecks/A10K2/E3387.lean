import QECCountComp.KData.A10K2

namespace QECKChecks.A10K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem dfs_6_4_7_3_0 : dfsPreK PA10K2 tA10K2 [6, 4, 7, 3, 0] [] = true := by
  decide +kernel

theorem dfs_6_4_7_3_1 : dfsPreK PA10K2 tA10K2 [6, 4, 7, 3, 1] [] = true := by
  decide +kernel

theorem dfs_6_4_7_3_2 : dfsPreK PA10K2 tA10K2 [6, 4, 7, 3, 2] [] = true := by
  decide +kernel

theorem dfs_6_4_7_3_3 : dfsPreK PA10K2 tA10K2 [6, 4, 7, 3, 3] [] = true := by
  decide +kernel

theorem dfs_6_4_7_3_4 : dfsPreK PA10K2 tA10K2 [6, 4, 7, 3, 4] [] = true := by
  decide +kernel

theorem dfs_6_4_7_3_5 : dfsPreK PA10K2 tA10K2 [6, 4, 7, 3, 5] [] = true := by
  decide +kernel

theorem dfs_6_4_7_3_6 : dfsPreK PA10K2 tA10K2 [6, 4, 7, 3, 6] [] = true := by
  decide +kernel

theorem dfs_6_4_7_3_7 : dfsPreK PA10K2 tA10K2 [6, 4, 7, 3, 7] [] = true := by
  decide +kernel

end QECKChecks.A10K2
