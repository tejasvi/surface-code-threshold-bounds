import QECCountComp.KData.D2M8K2

namespace QECKChecks.D2M8K2

open QECComp QECComp.KData

set_option maxRecDepth 1000000
set_option maxHeartbeats 0
set_option Elab.async false

theorem dfs_1_9_2_0 : dfsPreK PD2M8K2 tD2M8K2 [1, 9, 2, 0] [] = true := by
  decide +kernel

theorem dfs_1_9_2_1 : dfsPreK PD2M8K2 tD2M8K2 [1, 9, 2, 1] [] = true := by
  decide +kernel

theorem dfs_1_9_2_2 : dfsPreK PD2M8K2 tD2M8K2 [1, 9, 2, 2] [] = true := by
  decide +kernel

theorem dfs_1_9_2_3 : dfsPreK PD2M8K2 tD2M8K2 [1, 9, 2, 3] [] = true := by
  decide +kernel

theorem dfs_1_9_2_4 : dfsPreK PD2M8K2 tD2M8K2 [1, 9, 2, 4] [] = true := by
  decide +kernel

theorem dfs_1_9_2_5 : dfsPreK PD2M8K2 tD2M8K2 [1, 9, 2, 5] [] = true := by
  decide +kernel

theorem dfs_1_9_2_6 : dfsPreK PD2M8K2 tD2M8K2 [1, 9, 2, 6] [] = true := by
  decide +kernel

theorem dfs_1_9_2_7 : dfsPreK PD2M8K2 tD2M8K2 [1, 9, 2, 7] [] = true := by
  decide +kernel

theorem dfs_1_9_2_8 : dfsPreK PD2M8K2 tD2M8K2 [1, 9, 2, 8] [] = true := by
  decide +kernel

theorem dfs_1_9_2_9 : dfsPreK PD2M8K2 tD2M8K2 [1, 9, 2, 9] [] = true := by
  decide +kernel

theorem dfs_1_9_2_10 : dfsPreK PD2M8K2 tD2M8K2 [1, 9, 2, 10] [] = true := by
  decide +kernel

theorem dfs_1_9_2_11 : dfsPreK PD2M8K2 tD2M8K2 [1, 9, 2, 11] [] = true := by
  decide +kernel

end QECKChecks.D2M8K2
