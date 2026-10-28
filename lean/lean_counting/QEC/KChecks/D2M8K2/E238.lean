import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem dfs_1_7_10_0 : dfsPreK PD2M8K2 tD2M8K2 [1, 7, 10, 0] [] = true := by
  decide +kernel

theorem dfs_1_7_10_1 : dfsPreK PD2M8K2 tD2M8K2 [1, 7, 10, 1] [] = true := by
  decide +kernel

theorem dfs_1_7_10_2 : dfsPreK PD2M8K2 tD2M8K2 [1, 7, 10, 2] [] = true := by
  decide +kernel

theorem dfs_1_7_10_3 : dfsPreK PD2M8K2 tD2M8K2 [1, 7, 10, 3] [] = true := by
  decide +kernel

theorem dfs_1_7_10_4 : dfsPreK PD2M8K2 tD2M8K2 [1, 7, 10, 4] [] = true := by
  decide +kernel

theorem dfs_1_7_10_5 : dfsPreK PD2M8K2 tD2M8K2 [1, 7, 10, 5] [] = true := by
  decide +kernel

theorem dfs_1_7_10_6 : dfsPreK PD2M8K2 tD2M8K2 [1, 7, 10, 6] [] = true := by
  decide +kernel

theorem dfs_1_7_10_7 : dfsPreK PD2M8K2 tD2M8K2 [1, 7, 10, 7] [] = true := by
  decide +kernel

theorem dfs_1_7_10_8 : dfsPreK PD2M8K2 tD2M8K2 [1, 7, 10, 8] [] = true := by
  decide +kernel

theorem dfs_1_7_10_9 : dfsPreK PD2M8K2 tD2M8K2 [1, 7, 10, 9] [] = true := by
  decide +kernel

theorem dfs_1_7_10_10 : dfsPreK PD2M8K2 tD2M8K2 [1, 7, 10, 10] [] = true := by
  decide +kernel

theorem dfs_1_7_10_11 : dfsPreK PD2M8K2 tD2M8K2 [1, 7, 10, 11] [] = true := by
  decide +kernel

end QECKChecks.D2M8K2
